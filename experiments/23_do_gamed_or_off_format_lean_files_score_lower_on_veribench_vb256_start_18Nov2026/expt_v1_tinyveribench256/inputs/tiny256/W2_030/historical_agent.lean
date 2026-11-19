import Mathlib
namespace Agent

/-!
# A queue monitor, with FIFO, LIFO and priority strategies

This is a functional, small-step translation of Python's `queue` module. A step
runs while holding the queue's mutex. `blocked` releases that mutex, registers
on the appropriate condition, and retains a continuation; `resume` reacquires
it. Arbitrary interleavings (including spurious wake-ups) are represented by
calling `resume` with the current shared state. There is deliberately no
fairness assumption and no assertion that a blocking call terminates.

Lists describe *removal order*: a deque for FIFO, the reverse of the Python
list for LIFO, and the sorted abstraction of a heap for priority queues.
The comparator is supplied only to insertion; FIFO and LIFO accept arbitrary
Lean element types. Priority comparisons must, as in Python, define an order.
Exceptions leave the shared state unchanged. Notifications are explicit.

Timeouts and monotonic-clock samples use `Float`, not an exact-arithmetic
replacement. `Clock.start` is the sample for constructing a deadline and
`Clock.now` the subsequent sample for checking it. A resumed operation keeps
its original deadline. Waiting itself is an external condition-variable
primitive (including its platform-specific handling of nonfinite durations).
The model specifies the Python code up to this primitive, not an OS scheduler,
the GIL, or exceptions thrown inside user-supplied comparisons.
-/
namespace QueueThreadsafe

inductive Kind where
  | fifo | lifo | priority
  deriving Repr, DecidableEq

structure Queue (α : Type) where
  kind : Kind := .fifo
  maxsize : Int := 0
  items : List α := []
  unfinished : Nat := 0
  isShutdown : Bool := false
  deriving Repr, DecidableEq

abbrev Comparator (α : Type) := α → α → Bool

def init (kind : Kind := .fifo) (maxsize : Int := 0) : Queue α :=
  ⟨kind, maxsize, [], 0, false⟩

def benchmark_queue (maxsize : Int := 0) : Queue α := init .fifo maxsize
def benchmark_priority_queue (maxsize : Int := 0) : Queue α := init .priority maxsize
def benchmark_lifo_queue (maxsize : Int := 0) : Queue α := init .lifo maxsize

def qsize (q : Queue α) : Nat := q.items.length
def empty (q : Queue α) : Bool := q.items.isEmpty
def full (q : Queue α) : Bool := decide (0 < q.maxsize ∧ q.maxsize ≤ (qsize q : Int))

def priorityInsert (cmp : Comparator α) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if cmp x y then x :: y :: ys else y :: priorityInsert cmp x ys

def hookPut (cmp : Comparator α) (q : Queue α) (x : α) : List α :=
  match q.kind with
  | .fifo => q.items ++ [x]
  | .lifo => x :: q.items
  | .priority => priorityInsert cmp x q.items

inductive Error where
  | empty | full | shutDown | negativeTimeout | tooManyTaskDone
  deriving Repr, DecidableEq

inductive Notice where
  | notEmptyOne | notFullOne | allTasksDoneAll | notEmptyAll | notFullAll
  deriving Repr, DecidableEq

structure Clock where
  start : Float := 0
  now : Float := 0
  deriving Repr

inductive Pending (α : Type) where
  | put (item : α) (deadline : Option Float)
  | get (deadline : Option Float)
  | join
  deriving Repr

inductive Condition where
  | notEmpty | notFull | allTasksDone
  deriving Repr, DecidableEq

def Pending.condition : Pending α → Condition
  | .put .. => .notFull
  | .get .. => .notEmpty
  | .join => .allTasksDone

def Pending.duration (p : Pending α) (now : Float) : Option Float :=
  match p with
  | .put _ d | .get d => d.map (fun endtime => endtime - now)
  | .join => none

inductive Call (α : Type) where
  | put (item : α) (block : Bool := true) (timeout : Option Float := none)
  | get (block : Bool := true) (timeout : Option Float := none)
  | taskDone | join
  | shutdown (immediate : Bool := false)
  | resume (pending : Pending α)
  deriving Repr

inductive Decision (α : Type) where
  | enqueue (item : α) | dequeue | finish | joined
  | close (immediate : Bool)
  | fail (error : Error)
  | suspend (pending : Pending α)
  deriving Repr

def putLoop (q : Queue α) (x : α) (deadline : Option Float) (now : Float) : Decision α :=
  if full q then
    match deadline with
    | none => .suspend (.put x none)
    | some t => if t - now ≤ 0 then .fail .full else .suspend (.put x deadline)
  else .enqueue x

def getLoop (q : Queue α) (deadline : Option Float) (now : Float) : Decision α :=
  if empty q then
    match deadline with
    | none => .suspend (.get none)
    | some t => if t - now ≤ 0 then .fail .empty else .suspend (.get deadline)
  else .dequeue

/-- Control flow inside the monitor, before the state-changing strategy hook. -/
def classify (q : Queue α) (call : Call α) (clock : Clock) : Decision α :=
  match call with
  | .put x block timeout =>
    if q.isShutdown then .fail .shutDown
    else if q.maxsize ≤ 0 then .enqueue x
    else if !block then
      if full q then .fail .full else .enqueue x
    else match timeout with
      | none => putLoop q x none clock.now
      | some t => if t < 0 then .fail .negativeTimeout
                  else putLoop q x (some (clock.start + t)) clock.now
  | .get block timeout =>
    if q.isShutdown && empty q then .fail .shutDown
    else if !block then
      if empty q then .fail .empty else .dequeue
    else match timeout with
      | none => getLoop q none clock.now
      | some t => if t < 0 then .fail .negativeTimeout
                  else getLoop q (some (clock.start + t)) clock.now
  | .taskDone => if q.unfinished = 0 then .fail .tooManyTaskDone else .finish
  | .join => if q.unfinished = 0 then .joined else .suspend .join
  | .shutdown immediate => .close immediate
  | .resume (.put x deadline) =>
    if q.isShutdown then .fail .shutDown else putLoop q x deadline clock.now
  | .resume (.get deadline) =>
    if q.isShutdown && empty q then .fail .shutDown else getLoop q deadline clock.now
  | .resume .join => if q.unfinished = 0 then .joined else .suspend .join

inductive Result (α : Type) where
  | done | value (item : α) | raised (error : Error) | blocked (pending : Pending α)
  deriving Repr

structure Step (α : Type) where
  queue : Queue α
  result : Result α
  notices : List Notice := []
  deriving Repr

/-- Pure state update. `dequeue` on [] is unreachable from `classify`. -/
def commit (cmp : Comparator α) (q : Queue α) : Decision α → Step α
  | .enqueue x => ⟨{q with items := hookPut cmp q x, unfinished := q.unfinished + 1},
                   .done, [.notEmptyOne]⟩
  | .dequeue => match q.items with
    | [] => ⟨q, .raised .empty, []⟩
    | x :: xs => ⟨{q with items := xs}, .value x, [.notFullOne]⟩
  | .finish => ⟨{q with unfinished := q.unfinished - 1}, .done,
                if q.unfinished = 1 then [.allTasksDoneAll] else []⟩
  | .joined => ⟨q, .done, []⟩
  | .close immediate =>
    ⟨{q with isShutdown := true,
             items := if immediate then [] else q.items,
             unfinished := if immediate then q.unfinished - q.items.length else q.unfinished},
      .done, (if immediate then [.allTasksDoneAll] else []) ++ [.notEmptyAll, .notFullAll]⟩
  | .fail e => ⟨q, .raised e, []⟩
  | .suspend p => ⟨q, .blocked p, []⟩

def step (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock := {}) : Step α :=
  commit cmp q (classify q call clock)

def put (cmp : Comparator α) (q : Queue α) (x : α)
    (block : Bool := true) (timeout : Option Float := none) (clock : Clock := {}) : Step α :=
  step cmp q (.put x block timeout) clock

def get (q : Queue α) (block : Bool := true) (timeout : Option Float := none)
    (clock : Clock := {}) : Step α := step (fun _ _ => false) q (.get block timeout) clock

def put_nowait (cmp : Comparator α) (q : Queue α) (x : α) : Step α := put cmp q x false
def get_nowait (q : Queue α) : Step α := get q false
def task_done (q : Queue α) : Step α := step (fun _ _ => false) q .taskDone
def join (q : Queue α) : Step α := step (fun _ _ => false) q .join
def shutdown (q : Queue α) (immediate : Bool := false) : Step α :=
  step (fun _ _ => false) q (.shutdown immediate)

/-- Python's immediate shutdown loop, before replacing it by saturated subtraction. -/
def drainCount : Nat → List α → Nat
  | n, [] => n
  | n, _ :: xs => drainCount (n - 1) xs

-- Unit tests: the supplied test scenarios, plus waits, deadlines and shutdown draining.
def natCmp (a b : Nat) : Bool := decide (a ≤ b)
def load (cmp : Comparator α) (q : Queue α) (xs : List α) : Queue α :=
  xs.foldl (fun s x => (put cmp s x).queue) q

def popMany : Nat → Queue α → List α
  | 0, _ => []
  | n + 1, q => match (get_nowait q).result with
    | .value x => x :: popMany n (get_nowait q).queue
    | _ => []

def hasError (s : Step α) (e : Error) : Bool :=
  match s.result with | .raised e' => decide (e = e') | _ => false

def isBlocked (s : Step α) : Bool :=
  match s.result with | .blocked _ => true | _ => false

def pairCmp (a b : Nat × String) : Bool :=
  if a.1 = b.1 then decide (a.2 ≤ b.2) else decide (a.1 ≤ b.1)

example : empty (benchmark_queue (α := Nat) 5) && !full (benchmark_queue (α := Nat) 5) = true := by native_decide
example : popMany 3 (load natCmp (benchmark_queue 5) [111,333,222]) = [111,333,222] := by native_decide
example : popMany 3 (load natCmp (benchmark_lifo_queue 5) [111,333,222]) = [222,333,111] := by native_decide
example : popMany 3 (load pairCmp (benchmark_priority_queue 5) [(2,"two"),(1,"one"),(3,"three")]) =
    [(1,"one"),(2,"two"),(3,"three")] := by native_decide
example : let q := (put natCmp (benchmark_queue 1) 1).queue
    full q && hasError (put_nowait natCmp q 2) .full &&
      hasError (get_nowait (get_nowait q).queue) .empty = true := by native_decide
example : let q := (get (put (fun _ _ => false) (benchmark_queue 3) "a").queue).queue
    (task_done q).queue.unfinished = 0 ∧ hasError (task_done (task_done q).queue) .tooManyTaskDone = true := by native_decide
example : hasError (put natCmp (shutdown (benchmark_queue 2)).queue 1) .shutDown = true := by native_decide
example : isBlocked (get (benchmark_queue (α := Nat) 2)) = true := by native_decide
example : isBlocked (put natCmp (load natCmp (benchmark_queue 1) [4]) 7) = true := by native_decide
example : hasError (get (benchmark_queue (α := Nat)) true (some (-1))) .negativeTimeout = true := by native_decide
example : hasError (put natCmp (benchmark_queue 2) 9 true (some (-1))) .negativeTimeout = true := by native_decide
example : (put natCmp (benchmark_queue 0) 9 true (some (-1))).queue.items = [9] := by native_decide
example : hasError (get (benchmark_queue (α := Nat)) true (some 2) ⟨10,12⟩) .empty = true := by native_decide
example : isBlocked (get (benchmark_queue (α := Nat)) true (some 2) ⟨10,11⟩) = true := by native_decide
example : let q := load natCmp (benchmark_queue 4) [1,2,3]
    (shutdown q true).queue.items = [] ∧ (shutdown q true).queue.unfinished = 0 ∧
    hasError (get (shutdown q true).queue) .shutDown = true := by native_decide
#eval popMany 3 (load natCmp (benchmark_queue 5) [111,333,222])
#eval popMany 3 (load pairCmp (benchmark_priority_queue 5) [(2,"two"),(1,"one"),(3,"three")])
#eval get (benchmark_queue (α := Nat) 2) true (some 5) ⟨10,11⟩

/-- Executable counterpart of all six scenarios in the supplied Python `check`. -/
def check : Bool :=
  let q0 : Queue Nat := benchmark_queue 5
  let q := load natCmp q0 [111,333,222]
  let qAfter := (get (get (get q).queue).queue).queue
  let lq := load natCmp (benchmark_lifo_queue 5) [111,333,222]
  let pq := load pairCmp (benchmark_priority_queue 5) [(2,"two"),(1,"one"),(3,"three")]
  let small := (put natCmp (benchmark_queue 1) 1).queue
  let tasks := (get (put (fun _ _ => false) (benchmark_queue 3) "a").queue).queue
  let doneTasks := (task_done tasks).queue
  let closed : Queue String := (shutdown (benchmark_queue 2)).queue
  empty q0 && !full q0 && decide (popMany 3 q = [111,333,222]) && empty qAfter &&
  decide (popMany 3 lq = [222,333,111]) &&
  decide (popMany 3 pq = [(1,"one"),(2,"two"),(3,"three")]) &&
  full small && hasError (put_nowait natCmp small 2) .full &&
  hasError (get_nowait (get small).queue) .empty &&
  decide (doneTasks.unfinished = 0) && hasError (task_done doneTasks) .tooManyTaskDone &&
  hasError (put (fun _ _ => false) closed "x") .shutDown

example : check = true := by native_decide
#eval check

/-- Reachable queues respect a positive capacity. No bound is imposed for maxsize ≤ 0.
There is intentionally no assumption `items.length ≤ unfinished`: Python allows
`task_done` to be called before `get`, and detects only a counter underflow. -/
def Pre (q : Queue α) : Prop := 0 < q.maxsize → (q.items.length : Int) ≤ q.maxsize

def observers_prop (q : Queue α) : Prop :=
  qsize q = q.items.length ∧ (empty q = true ↔ q.items = []) ∧
  (full q = true ↔ 0 < q.maxsize ∧ q.maxsize ≤ (q.items.length : Int))

theorem observers_thm (q : Queue α) : observers_prop q := by
  simp [observers_prop, qsize, empty, full]

theorem priorityInsert_perm (cmp : Comparator α) (x : α) (xs : List α) :
    (priorityInsert cmp x xs).Perm (x :: xs) := by
  induction xs with
  | nil => simp [priorityInsert]
  | cons y ys ih =>
    simp only [priorityInsert]
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap _ _ _)

theorem hookPut_length (cmp : Comparator α) (q : Queue α) (x : α) :
    (hookPut cmp q x).length = q.items.length + 1 := by
  cases h : q.kind <;> simp [hookPut, h, (priorityInsert_perm cmp x q.items).length_eq]

def insertion_prop (cmp : Comparator α) (q : Queue α) (x : α) : Prop :=
  (hookPut cmp q x).Perm (x :: q.items) ∧
  (hookPut cmp q x).length = q.items.length + 1 ∧
  (q.kind = .fifo → hookPut cmp q x = q.items ++ [x]) ∧
  (q.kind = .lifo → hookPut cmp q x = x :: q.items)

theorem insertion_thm (cmp : Comparator α) (q : Queue α) (x : α) :
    insertion_prop cmp q x := by
  refine ⟨?_, hookPut_length cmp q x, ?_, ?_⟩
  · cases h : q.kind
    · simp [hookPut, h]
    · simp [hookPut, h]
    · exact (by simpa [hookPut, h] using priorityInsert_perm cmp x q.items)
  · intro h; simp [hookPut, h]
  · intro h; simp [hookPut, h]

/-- The contract required of priority comparisons; no comparison is used by FIFO/LIFO. -/
def ComparatorOrder (cmp : Comparator α) : Prop :=
  (∀ a b c, cmp a b = true → cmp b c = true → cmp a c = true) ∧
  (∀ a b, cmp a b = true ∨ cmp b a = true)

def priority_prop (cmp : Comparator α) (xs : List α) (x : α) : Prop :=
  ComparatorOrder cmp → xs.Pairwise (fun a b => cmp a b = true) →
    (priorityInsert cmp x xs).Pairwise (fun a b => cmp a b = true)

theorem priority_thm (cmp : Comparator α) (xs : List α) (x : α) :
    priority_prop cmp xs x := by
  intro ho hs
  induction xs with
  | nil => simp [priorityInsert]
  | cons y ys ih =>
    obtain ⟨hy, hys⟩ := List.pairwise_cons.mp hs
    simp only [priorityInsert]
    split
    next hxy =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, List.pairwise_cons.mpr ⟨hy, hys⟩⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · exact ho.1 x y z hxy (hy z hz)
    next hxy =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih hys⟩
      intro z hz
      have hz' := (priorityInsert_perm cmp x ys).mem_iff.mp hz
      rcases List.mem_cons.mp hz' with rfl | hz'
      · exact (ho.2 _ y).resolve_left hxy
      · exact hy z hz'

/-- Nonblocking put: shutdown precedes Full; success adds one unfinished task. -/
def put_prop (cmp : Comparator α) (q : Queue α) (x : α) : Prop :=
  put_nowait cmp q x =
    if q.isShutdown then ⟨q, .raised .shutDown, []⟩
    else if full q then ⟨q, .raised .full, []⟩
    else ⟨{q with items := hookPut cmp q x, unfinished := q.unfinished + 1},
           .done, [.notEmptyOne]⟩

theorem put_thm (cmp : Comparator α) (q : Queue α) (x : α) : put_prop cmp q x := by
  unfold put_prop put_nowait put step classify
  by_cases hs : q.isShutdown = true
  · simp [hs, commit]
  · by_cases hm : q.maxsize ≤ 0
    · have hf : full q = false := by simp [full, qsize]; omega
      simp [hs, hm, hf, commit]
    · simp [hs, hm]; split <;> simp [commit, hs]

/-- Dequeue does not decrement the task counter, including during graceful shutdown. -/
def get_prop (q : Queue α) : Prop :=
  get_nowait q = match q.items with
    | [] => ⟨q, .raised (if q.isShutdown then .shutDown else .empty), []⟩
    | x :: xs => ⟨{q with items := xs}, .value x, [.notFullOne]⟩

theorem get_thm (q : Queue α) : get_prop q := by
  unfold get_prop get_nowait get step classify
  cases h : q.items with
  | nil => cases q.isShutdown <;> simp [empty, h, commit]
  | cons x xs => simp [empty, h, commit]

def task_prop (q : Queue α) : Prop :=
  task_done q = (if q.unfinished = 0 then ⟨q, .raised .tooManyTaskDone, []⟩
    else ⟨{q with unfinished := q.unfinished - 1}, .done,
            if q.unfinished = 1 then [.allTasksDoneAll] else []⟩) ∧
  join q = (if q.unfinished = 0 then ⟨q, .done, []⟩ else ⟨q, .blocked .join, []⟩)

theorem task_thm (q : Queue α) : task_prop q := by
  unfold task_prop task_done join step classify
  by_cases h : q.unfinished = 0 <;> simp [h, commit]

def shutdown_prop (q : Queue α) (immediate : Bool) : Prop :=
  shutdown q immediate =
    ⟨{q with isShutdown := true,
             items := if immediate then [] else q.items,
             unfinished := if immediate then drainCount q.unfinished q.items else q.unfinished},
      .done, (if immediate then [.allTasksDoneAll] else []) ++ [.notEmptyAll, .notFullAll]⟩

theorem drainCount_eq (n : Nat) (xs : List α) : drainCount n xs = n - xs.length := by
  induction xs generalizing n with
  | nil => simp [drainCount]
  | cons x xs ih => simp only [drainCount, ih, List.length_cons]; omega

theorem shutdown_thm (q : Queue α) (immediate : Bool) : shutdown_prop q immediate := by
  simp [shutdown_prop, shutdown, step, classify, commit, drainCount_eq]

/-- Authorization facts established by the control flow before committing. -/
def SafeDecision (q : Queue α) : Decision α → Prop
  | .enqueue _ => full q = false
  | .dequeue => empty q = false
  | .finish => 0 < q.unfinished
  | _ => True

theorem putLoop_safe (q : Queue α) (x : α) (d : Option Float) (now : Float) :
    SafeDecision q (putLoop q x d now) := by
  unfold putLoop
  split
  · cases d with
    | none => trivial
    | some t => simp only []; split <;> trivial
  · simpa [SafeDecision] using (Bool.eq_false_iff.mpr ‹¬full q = true›)

theorem getLoop_safe (q : Queue α) (d : Option Float) (now : Float) :
    SafeDecision q (getLoop q d now) := by
  unfold getLoop
  split
  · cases d with
    | none => trivial
    | some t => simp only []; split <;> trivial
  · simpa [SafeDecision] using (Bool.eq_false_iff.mpr ‹¬empty q = true›)

theorem classify_safe (q : Queue α) (call : Call α) (clock : Clock) :
    SafeDecision q (classify q call clock) := by
  cases call with
  | put x block timeout =>
    simp only [classify]
    split
    · trivial
    · split
      next hm => simp [SafeDecision, full, qsize]; omega
      next hm =>
        split
        · split <;> simp_all [SafeDecision]
        · cases timeout with
          | none => exact putLoop_safe _ _ _ _
          | some t => simp only []; split; trivial; exact putLoop_safe _ _ _ _
  | get block timeout =>
    simp only [classify]
    split
    · trivial
    · split
      · split <;> simp_all [SafeDecision]
      · cases timeout with
        | none => exact getLoop_safe _ _ _
        | some t => simp only []; split; trivial; exact getLoop_safe _ _ _
  | taskDone => simp only [classify]; split <;> simp_all [SafeDecision]; omega
  | join => simp only [classify]; split <;> trivial
  | shutdown b => trivial
  | resume p =>
    cases p with
    | put x d => simp only [classify]; split; trivial; exact putLoop_safe _ _ _ _
    | get d => simp only [classify]; split; trivial; exact getLoop_safe _ _ _
    | join => simp only [classify]; split <;> trivial

def capacity_prop (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock) : Prop :=
  Pre q → Pre (step cmp q call clock).queue

theorem commit_preserves (cmp : Comparator α) (q : Queue α) (d : Decision α)
    (hp : Pre q) (hs : SafeDecision q d) : Pre (commit cmp q d).queue := by
  cases d with
  | enqueue x =>
    have hnfull : ¬ (0 < q.maxsize ∧ q.maxsize ≤ (q.items.length : Int)) := by
      simpa [SafeDecision, full, qsize] using hs
    intro hpos
    change ((hookPut cmp q x).length : Int) ≤ q.maxsize
    rw [hookPut_length]
    have hn : (q.items.length : Int) < q.maxsize := by
      change 0 < q.maxsize at hpos
      omega
    push_cast
    omega
  | dequeue =>
    cases hi : q.items with
    | nil => simpa [commit, hi] using hp
    | cons x xs =>
      simp only [commit, hi]
      intro hpos
      change 0 < q.maxsize at hpos
      change (xs.length : Int) ≤ q.maxsize
      have hh := hp hpos
      simp only [hi, List.length_cons, Nat.cast_add, Nat.cast_one] at hh
      omega
  | finish => exact hp
  | joined => exact hp
  | close b =>
    cases b
    · exact hp
    · intro hpos; change (0 : Int) ≤ q.maxsize; change 0 < q.maxsize at hpos; omega
  | fail e => exact hp
  | suspend p => exact hp

theorem capacity_thm (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock) :
    capacity_prop cmp q call clock := by
  intro hp
  exact commit_preserves cmp q _ hp (classify_safe q call clock)

/-- Exceptions and waits cannot partially mutate the monitor state or notify a waiter. -/
def atomic_prop (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock) : Prop :=
  (∀ e, (step cmp q call clock).result = .raised e →
    (step cmp q call clock).queue = q ∧ (step cmp q call clock).notices = []) ∧
  (∀ p, (step cmp q call clock).result = .blocked p →
    (step cmp q call clock).queue = q ∧ (step cmp q call clock).notices = [])

theorem commit_atomic (cmp : Comparator α) (q : Queue α) (d : Decision α) :
    (∀ e, (commit cmp q d).result = .raised e →
      (commit cmp q d).queue = q ∧ (commit cmp q d).notices = []) ∧
    (∀ p, (commit cmp q d).result = .blocked p →
      (commit cmp q d).queue = q ∧ (commit cmp q d).notices = []) := by
  cases d <;> try { simp [commit] }
  cases hi : q.items <;> simp [commit, hi]

theorem atomic_thm (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock) :
    atomic_prop cmp q call clock := commit_atomic cmp q _

/-- Configuration cannot change, and shutdown is irreversible. -/
def frame_prop (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock) : Prop :=
  let s := step cmp q call clock
  s.queue.kind = q.kind ∧ s.queue.maxsize = q.maxsize ∧
  (q.isShutdown = true → s.queue.isShutdown = true)

theorem commit_frame (cmp : Comparator α) (q : Queue α) (d : Decision α) :
    (commit cmp q d).queue.kind = q.kind ∧
    (commit cmp q d).queue.maxsize = q.maxsize ∧
    (q.isShutdown = true → (commit cmp q d).queue.isShutdown = true) := by
  cases d <;> try { simp [commit] }
  cases hi : q.items <;> simp [commit, hi]

theorem frame_thm (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock) :
    frame_prop cmp q call clock := commit_frame cmp q _

/-- A successful priority dequeue returns a minimum, not merely some member. -/
def priority_min_prop (cmp : Comparator α) (q : Queue α) : Prop :=
  ComparatorOrder cmp → q.items.Pairwise (fun a b => cmp a b = true) →
  ∀ x, (get_nowait q).result = .value x → ∀ y ∈ q.items, cmp x y = true

theorem priority_min_thm (cmp : Comparator α) (q : Queue α) : priority_min_prop cmp q := by
  intro ho hs x hx y hy
  have hg := get_thm q
  unfold get_prop at hg
  cases hi : q.items with
  | nil => simp [hi] at hy
  | cons a xs =>
    rw [hi] at hg
    rw [hg] at hx
    have hax : a = x := by simpa using hx
    subst a
    rw [hi] at hs hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (ho.2 _ _).elim id id
    · exact (List.pairwise_cons.mp hs).1 y hy

/-- Indefinite waits, shutdown checks after reacquiring the lock, and join resumption. -/
def blocking_prop (cmp : Comparator α) (q : Queue α) (x : α) (clock : Clock) : Prop :=
  (q.isShutdown = false → full q = true →
    put cmp q x true none clock = ⟨q, .blocked (.put x none), []⟩) ∧
  (q.isShutdown = false → empty q = true →
    get q true none clock = ⟨q, .blocked (.get none), []⟩) ∧
  (∀ d, step cmp q (.resume (.put x d)) clock =
    if q.isShutdown then ⟨q, .raised .shutDown, []⟩
    else commit cmp q (putLoop q x d clock.now)) ∧
  (∀ d, step cmp q (.resume (.get d)) clock =
    if q.isShutdown && empty q then ⟨q, .raised .shutDown, []⟩
    else commit cmp q (getLoop q d clock.now)) ∧
  step cmp q (.resume .join) clock = join q

theorem blocking_thm (cmp : Comparator α) (q : Queue α) (x : α) (clock : Clock) :
    blocking_prop cmp q x clock := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hs hf
    have hm : ¬ q.maxsize ≤ 0 := by
      have := (of_decide_eq_true hf : 0 < q.maxsize ∧ q.maxsize ≤ (qsize q : Int))
      omega
    simp [put, step, classify, hs, hm, putLoop, hf, commit]
  · intro hs he
    simp [get, step, classify, hs, getLoop, he, commit]
  · intro d; simp only [step, classify]; split <;> rfl
  · intro d; simp only [step, classify]; split <;> rfl
  · simp only [step, classify, join]; split <;> rfl

/-- All timeout-sensitive branches, including Python's deliberately ignored arguments.
The inequalities below are Float inequalities. No finite/nonnegative assumption is
silently added to the domain. The same expressions handle NaN and infinities. -/
def timeout_prop (q : Queue α) (x : α) (t : Float) (clock : Clock) : Prop :=
  (q.isShutdown = false → 0 < q.maxsize → t < 0 →
    classify q (.put x true (some t)) clock = .fail .negativeTimeout) ∧
  ((q.isShutdown && empty q) = false → t < 0 →
    classify q (.get true (some t)) clock = .fail .negativeTimeout) ∧
  classify q (.put x false (some t)) clock = classify q (.put x false none) clock ∧
  classify q (.get false (some t)) clock = classify q (.get false none) clock ∧
  (q.isShutdown = false → q.maxsize ≤ 0 →
    classify q (.put x true (some t)) clock = .enqueue x) ∧
  (q.isShutdown = false → 0 < q.maxsize → ¬ t < 0 →
    classify q (.put x true (some t)) clock = putLoop q x (some (clock.start + t)) clock.now) ∧
  ((q.isShutdown && empty q) = false → ¬ t < 0 →
    classify q (.get true (some t)) clock = getLoop q (some (clock.start + t)) clock.now) ∧
  putLoop q x (some t) clock.now =
    (if full q then if t - clock.now ≤ 0 then .fail .full else .suspend (.put x (some t)) else .enqueue x) ∧
  getLoop q (some t) clock.now =
    (if empty q then if t - clock.now ≤ 0 then .fail .empty else .suspend (.get (some t)) else .dequeue)

theorem timeout_thm (q : Queue α) (x : α) (t : Float) (clock : Clock) :
    timeout_prop q x t clock := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro hs hm ht; have hm' : ¬q.maxsize ≤ 0 := by omega
    simp [classify, hs, hm', ht]
  · intro hs ht; simp [classify, hs, ht]
  · simp [classify]
  · simp [classify]
  · intro hs hm; simp [classify, hs, hm]
  · intro hs hm ht; have hm' : ¬q.maxsize ≤ 0 := by omega
    simp [classify, hs, hm', ht]
  · intro hs ht; simp [classify, hs, ht]

/-- Finite schedules are arbitrary serializations of mutex-protected transitions.
Blocked calls can be followed by other threads' calls and later resume events. -/
def run (cmp : Comparator α) : Queue α → List (Call α × Clock) → Queue α
  | q, [] => q
  | q, (c, t) :: rest => run cmp (step cmp q c t).queue rest

def trace_prop (cmp : Comparator α) (q : Queue α) (history : List (Call α × Clock)) : Prop :=
  (Pre q → Pre (run cmp q history)) ∧
  (q.isShutdown = true → (run cmp q history).isShutdown = true)

theorem trace_thm (cmp : Comparator α) (q : Queue α) (history : List (Call α × Clock)) :
    trace_prop cmp q history := by
  induction history generalizing q with
  | nil => exact ⟨id, id⟩
  | cons event rest ih =>
    rcases event with ⟨c, t⟩
    refine ⟨?_, ?_⟩
    · intro hp
      exact (ih _).1 (capacity_thm cmp q c t hp)
    · intro hs
      exact (ih _).2 ((frame_thm cmp q c t).2.2 hs)

theorem init_pre (kind : Kind) (maxsize : Int) : Pre (init (α := α) kind maxsize) := by
  intro h; simp only [init, List.length_nil, Nat.cast_zero]; change 0 < maxsize at h; omega

theorem put_unbounded (cmp : Comparator α) (q : Queue α) (x : α)
    (hm : q.maxsize ≤ 0) (hs : q.isShutdown = false) :
    put cmp q x = ⟨{q with items := hookPut cmp q x, unfinished := q.unfinished + 1},
                    .done, [.notEmptyOne]⟩ := by
  simp [put, step, classify, hm, hs, commit]

theorem load_fifo (cmp : Comparator α) (q : Queue α) (xs : List α)
    (hk : q.kind = .fifo) (hm : q.maxsize ≤ 0) (hs : q.isShutdown = false) :
    (load cmp q xs).items = q.items ++ xs := by
  induction xs generalizing q with
  | nil => simp [load]
  | cons x xs ih =>
    change (load cmp (put cmp q x).queue xs).items = q.items ++ (x :: xs)
    rw [put_unbounded cmp q x hm hs]
    rw [ih {q with items := hookPut cmp q x, unfinished := q.unfinished + 1} hk hm hs]
    simp [hookPut, hk, List.append_assoc]

theorem load_lifo (cmp : Comparator α) (q : Queue α) (xs : List α)
    (hk : q.kind = .lifo) (hm : q.maxsize ≤ 0) (hs : q.isShutdown = false) :
    (load cmp q xs).items = xs.reverse ++ q.items := by
  induction xs generalizing q with
  | nil => simp [load]
  | cons x xs ih =>
    change (load cmp (put cmp q x).queue xs).items = (x :: xs).reverse ++ q.items
    rw [put_unbounded cmp q x hm hs]
    rw [ih {q with items := hookPut cmp q x, unfinished := q.unfinished + 1} hk hm hs]
    simp [hookPut, hk, List.reverse_cons, List.append_assoc]

theorem load_priority (cmp : Comparator α) (q : Queue α) (xs : List α)
    (hk : q.kind = .priority) (hm : q.maxsize ≤ 0) (hs : q.isShutdown = false) :
    (load cmp q xs).items.Perm (q.items ++ xs) ∧
    (ComparatorOrder cmp → q.items.Pairwise (fun a b => cmp a b = true) →
      (load cmp q xs).items.Pairwise (fun a b => cmp a b = true)) := by
  induction xs generalizing q with
  | nil => simp [load]
  | cons x xs ih =>
    change (load cmp (put cmp q x).queue xs).items.Perm (q.items ++ (x :: xs)) ∧ _
    rw [put_unbounded cmp q x hm hs]
    have hi := ih {q with items := hookPut cmp q x, unfinished := q.unfinished + 1} hk hm hs
    constructor
    · have hp : (hookPut cmp q x).Perm (q.items ++ [x]) := by
        simpa [hookPut, hk] using
          (priorityInsert_perm cmp x q.items).trans (List.perm_append_comm (l₁ := [x]) (l₂ := q.items))
      simpa [List.append_assoc] using hi.1.trans (hp.append_right xs)
    · intro ho hsorted
      change (load cmp (put cmp q x).queue xs).items.Pairwise _
      rw [put_unbounded cmp q x hm hs]
      apply hi.2 ho
      simpa [hookPut, hk] using priority_thm cmp q.items x ho hsorted

def batch_prop (cmp : Comparator α) (xs : List α) : Prop :=
  (load cmp (benchmark_queue 0) xs).items = xs ∧
  (load cmp (benchmark_lifo_queue 0) xs).items = xs.reverse ∧
  (load cmp (benchmark_priority_queue 0) xs).items.Perm xs ∧
  (ComparatorOrder cmp →
    (load cmp (benchmark_priority_queue 0) xs).items.Pairwise (fun a b => cmp a b = true))

theorem batch_thm (cmp : Comparator α) (xs : List α) : batch_prop cmp xs := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [benchmark_queue, init] using
      load_fifo cmp (benchmark_queue 0) xs rfl (by change (0 : Int) ≤ 0; omega) rfl
  · simpa [benchmark_lifo_queue, init] using
      load_lifo cmp (benchmark_lifo_queue 0) xs rfl (by change (0 : Int) ≤ 0; omega) rfl
  · simpa [benchmark_priority_queue, init] using
      (load_priority cmp (benchmark_priority_queue 0) xs rfl (by change (0 : Int) ≤ 0; omega) rfl).1
  · intro ho
    exact (load_priority cmp (benchmark_priority_queue 0) xs rfl (by change (0 : Int) ≤ 0; omega) rfl).2 ho (by simp [benchmark_priority_queue, init])

def removal_prop (q : Queue α) : Prop := popMany q.items.length q = q.items

theorem removal_thm (q : Queue α) : removal_prop q := by
  suffices h : ∀ n (q : Queue α), q.items.length = n → popMany n q = q.items from
    h q.items.length q rfl
  intro n
  induction n with
  | zero => intro q h; have he := List.length_eq_zero_iff.mp h; simp [popMany, he]
  | succ n ih =>
    intro q h
    have hg := get_thm q
    unfold get_prop at hg
    cases hi : q.items with
    | nil => simp [hi] at h
    | cons x xs =>
      rw [hi] at hg
      have hn : xs.length = n := by simpa [hi] using h
      simp only [popMany, hg]
      have ht := ih {q with items := xs} hn
      simpa [hi] using congrArg (List.cons x) ht
/-- Priority ordering is preserved not just by batches, but by every monitor transition. -/
def order_preservation_prop (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock) : Prop :=
  ComparatorOrder cmp → q.kind = .priority →
  q.items.Pairwise (fun a b => cmp a b = true) →
  (step cmp q call clock).queue.items.Pairwise (fun a b => cmp a b = true)

theorem commit_order_preservation (cmp : Comparator α) (q : Queue α) (d : Decision α)
    (ho : ComparatorOrder cmp) (hk : q.kind = .priority)
    (hs : q.items.Pairwise (fun a b => cmp a b = true)) :
    (commit cmp q d).queue.items.Pairwise (fun a b => cmp a b = true) := by
  cases d with
  | enqueue x => simpa [commit, hookPut, hk] using priority_thm cmp q.items x ho hs
  | dequeue =>
    cases hi : q.items with
    | nil => simp [commit, hi]
    | cons x xs =>
      simp only [hi, List.pairwise_cons] at hs
      simpa [commit, hi] using hs.2
  | finish => exact hs
  | joined => exact hs
  | close b => cases b <;> simpa [commit] using hs
  | fail e => exact hs
  | suspend p => exact hs

theorem order_preservation_thm (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock) :
    order_preservation_prop cmp q call clock := by
  intro ho hk hs
  exact commit_order_preservation cmp q _ ho hk hs

/-- Shutdown has precedence over capacity, nonblocking errors, and timeout validation. -/
def shutdown_safety_prop (cmp : Comparator α) (q : Queue α) (x : α)
    (block : Bool) (timeout : Option Float) (clock : Clock) : Prop :=
  q.isShutdown = true →
    put cmp q x block timeout clock = ⟨q, .raised .shutDown, []⟩ ∧
    (empty q = true → get q block timeout clock = ⟨q, .raised .shutDown, []⟩)

theorem shutdown_safety_thm (cmp : Comparator α) (q : Queue α) (x : α)
    (block : Bool) (timeout : Option Float) (clock : Clock) :
    shutdown_safety_prop cmp q x block timeout clock := by
  intro hs
  constructor
  · simp [put, step, classify, hs, commit]
  · intro he; simp [get, step, classify, hs, he, commit]

/-- The full monitor contract, including preservation for this step and any finite schedule. -/
def Post_prop (cmp : Comparator α) (q : Queue α) (x : α) (call : Call α)
    (clock : Clock) (t : Float) (immediate : Bool) (history : List (Call α × Clock)) : Prop :=
  observers_prop q ∧ insertion_prop cmp q x ∧ priority_prop cmp q.items x ∧
  put_prop cmp q x ∧ get_prop q ∧ task_prop q ∧ shutdown_prop q immediate ∧
  capacity_prop cmp q call clock ∧ atomic_prop cmp q call clock ∧
  frame_prop cmp q call clock ∧ priority_min_prop cmp q ∧ blocking_prop cmp q x clock ∧
  timeout_prop q x t clock ∧ trace_prop cmp q history ∧ batch_prop cmp q.items ∧
  removal_prop q ∧ order_preservation_prop cmp q call clock ∧
  (∀ d, shutdown_safety_prop cmp q x immediate d clock) ∧ Pre (step cmp q call clock).queue


/-! ## Property-based tests
These are executable counterparts, not theorem proofs. Float continuations are
observed with `toBits` (including signed zeros and NaN payloads). Comparator
laws are universal in the theorems; their tested instance is the Nat order.
Capacity preconditions are imposed only on properties that require them.
-/
structure PendingKey (α : Type) where
  condition : Condition
  item : Option α
  deadlineBits : Option Nat
  deriving Repr, DecidableEq

structure Observation (α : Type) where
  tag : Nat
  item : Option α
  error : Option Error
  pending : Option (PendingKey α)
  deriving Repr, DecidableEq

def pendingKey : Pending α → PendingKey α
  | .put x d => ⟨.notFull, some x, d.map (fun f => f.toBits.toNat)⟩
  | .get d => ⟨.notEmpty, none, d.map (fun f => f.toBits.toNat)⟩
  | .join => ⟨.allTasksDone, none, none⟩

def resultKey : Result α → Observation α
  | .done => ⟨0, none, none, none⟩
  | .value x => ⟨1, some x, none, none⟩
  | .raised e => ⟨2, none, some e, none⟩
  | .blocked p => ⟨3, none, none, some (pendingKey p)⟩

def decisionKey : Decision α → Observation α
  | .enqueue x => ⟨0, some x, none, none⟩
  | .dequeue => ⟨1, none, none, none⟩
  | .finish => ⟨2, none, none, none⟩
  | .joined => ⟨3, none, none, none⟩
  | .close false => ⟨4, none, none, none⟩
  | .close true => ⟨5, none, none, none⟩
  | .fail e => ⟨6, none, some e, none⟩
  | .suspend p => ⟨7, none, none, some (pendingKey p)⟩


def sameStep (a b : Step Nat) : Bool :=
  decide (a.queue = b.queue) && decide (resultKey a.result = resultKey b.result) &&
    decide (a.notices = b.notices)
def sameDecision (a b : Decision Nat) : Bool := decide (decisionKey a = decisionKey b)
def implies (a b : Bool) : Bool := !a || b

def smallLists : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => [] :: (List.range 3).flatMap (fun x => (smallLists n).map (x :: ·))

def sampleQueues : List (Queue Nat) := do
  let k ← [.fifo, .lifo, .priority]
  let m ← [-2, 0, 1, 2, 3, 5]
  let xs ← smallLists 2
  let u ← [0, 1, 2, 5]
  let sd ← [false, true]
  pure ⟨k, m, xs, u, sd⟩

def sampleClocks : List Clock := [⟨0,0⟩, ⟨1,2⟩, ⟨2,7⟩]
def sampleTimes : List Float :=
  [-2, -1, 0, 1, 3, 8, Float.ofBits 0x8000000000000000,
   Float.ofBits 0x7ff0000000000000, Float.ofBits 0xfff0000000000000,
   Float.ofBits 0x7ff8000000000001]
def sampleDeadlines : List (Option Float) := none :: sampleTimes.map some

def sampleCalls (x : Nat) : List (Call Nat) :=
  [.put x, .put x false, .put x true (some (-1)), .put x true (some 0), .put x true (some 3),
   .get, .get false, .get true (some (-1)), .get true (some 0), .get true (some 3),
   .taskDone, .join, .shutdown false, .shutdown true,
   .resume (.put x none), .resume (.put x (some 2)),
   .resume (.get none), .resume (.get (some 2)), .resume .join]

def sampleHistory (x : Nat) : List (Call Nat × Clock) :=
  [(.get, ⟨0,0⟩), (.put x, ⟨0,0⟩), (.resume (.get none), ⟨1,1⟩),
   (.taskDone, ⟨1,1⟩), (.put (x+1), ⟨1,1⟩), (.join, ⟨1,1⟩),
   (.shutdown (decide (x % 2 = 0)), ⟨2,2⟩), (.resume (.put x (some 3)), ⟨3,3⟩),
   (.resume (.get (some 3)), ⟨3,3⟩), (.taskDone, ⟨3,3⟩), (.resume .join, ⟨3,3⟩)]

def preCheck (q : Queue Nat) : Bool := decide (0 < q.maxsize → (q.items.length : Int) ≤ q.maxsize)
def observersCheck (q : Queue Nat) : Bool :=
  @decide (observers_prop q) (by unfold observers_prop; infer_instance)
def insertionCheck (q : Queue Nat) (x : Nat) : Bool :=
  @decide (insertion_prop natCmp q x) (by unfold insertion_prop; infer_instance)
def priorityCheck (xs : List Nat) (x : Nat) : Bool :=
  decide (xs.Pairwise (fun a b => natCmp a b = true) →
    (priorityInsert natCmp x xs).Pairwise (fun a b => natCmp a b = true))

def putCheck (q : Queue Nat) (x : Nat) : Bool :=
  sameStep (put_nowait natCmp q x)
    (if q.isShutdown then ⟨q, .raised .shutDown, []⟩
     else if full q then ⟨q, .raised .full, []⟩
     else ⟨{q with items := hookPut natCmp q x, unfinished := q.unfinished + 1}, .done, [.notEmptyOne]⟩)

def getCheck (q : Queue Nat) : Bool :=
  sameStep (get_nowait q) (match q.items with
    | [] => ⟨q, .raised (if q.isShutdown then .shutDown else .empty), []⟩
    | x :: xs => ⟨{q with items := xs}, .value x, [.notFullOne]⟩)

def taskCheck (q : Queue Nat) : Bool :=
  sameStep (task_done q)
    (if q.unfinished = 0 then ⟨q, .raised .tooManyTaskDone, []⟩
     else ⟨{q with unfinished := q.unfinished - 1}, .done,
       if q.unfinished = 1 then [.allTasksDoneAll] else []⟩) &&
  sameStep (join q) (if q.unfinished = 0 then ⟨q, .done, []⟩ else ⟨q, .blocked .join, []⟩)

def shutdownCheck (q : Queue Nat) (b : Bool) : Bool :=
  sameStep (shutdown q b)
    ⟨{q with isShutdown := true,
             items := if b then [] else q.items,
             unfinished := if b then drainCount q.unfinished q.items else q.unfinished},
      .done, (if b then [.allTasksDoneAll] else []) ++ [.notEmptyAll, .notFullAll]⟩

def capacityCheck (q : Queue Nat) (c : Call Nat) (clock : Clock) : Bool :=
  implies (preCheck q) (preCheck (step natCmp q c clock).queue)

def atomicCheck (q : Queue Nat) (c : Call Nat) (clock : Clock) : Bool :=
  let s := step natCmp q c clock
  match s.result with
  | .raised _ | .blocked _ => decide (s.queue = q ∧ s.notices = [])
  | _ => true

def frameCheck (q : Queue Nat) (c : Call Nat) (clock : Clock) : Bool :=
  let s := step natCmp q c clock
  decide (s.queue.kind = q.kind ∧ s.queue.maxsize = q.maxsize ∧
    (q.isShutdown = true → s.queue.isShutdown = true))

def minimumCheck (q : Queue Nat) : Bool :=
  implies (decide (q.items.Pairwise (fun a b => natCmp a b = true)))
    (match (get_nowait q).result with
    | .value x => q.items.all (natCmp x)
    | _ => true)

def blockingCheck (q : Queue Nat) (x : Nat) (clock : Clock) : Bool :=
  implies (!q.isShutdown && full q)
    (sameStep (put natCmp q x true none clock) ⟨q, .blocked (.put x none), []⟩) &&
  implies (!q.isShutdown && empty q)
    (sameStep (get q true none clock) ⟨q, .blocked (.get none), []⟩) &&
  sampleDeadlines.all (fun d =>
    sameStep (step natCmp q (.resume (.put x d)) clock)
      (if q.isShutdown then ⟨q, .raised .shutDown, []⟩ else commit natCmp q (putLoop q x d clock.now)) &&
    sameStep (step natCmp q (.resume (.get d)) clock)
      (if q.isShutdown && empty q then ⟨q, .raised .shutDown, []⟩ else commit natCmp q (getLoop q d clock.now))) &&
  sameStep (step natCmp q (.resume .join) clock) (join q)

def timeoutCheck (q : Queue Nat) (x : Nat) (t : Float) (clock : Clock) : Bool :=
  implies (!q.isShutdown && decide (0 < q.maxsize) && decide (t < 0))
    (sameDecision (classify q (.put x true (some t)) clock) (.fail .negativeTimeout)) &&
  implies (!(q.isShutdown && empty q) && decide (t < 0))
    (sameDecision (classify q (.get true (some t)) clock) (.fail .negativeTimeout)) &&
  sameDecision (classify q (.put x false (some t)) clock) (classify q (.put x false none) clock) &&
  sameDecision (classify q (.get false (some t)) clock) (classify q (.get false none) clock) &&
  implies (!q.isShutdown && decide (q.maxsize ≤ 0))
    (sameDecision (classify q (.put x true (some t)) clock) (.enqueue x)) &&
  implies (!q.isShutdown && decide (0 < q.maxsize) && !decide (t < 0))
    (sameDecision (classify q (.put x true (some t)) clock) (putLoop q x (some (clock.start + t)) clock.now)) &&
  implies (!(q.isShutdown && empty q) && !decide (t < 0))
    (sameDecision (classify q (.get true (some t)) clock) (getLoop q (some (clock.start + t)) clock.now)) &&
  sameDecision (putLoop q x (some t) clock.now)
    (if full q then if t - clock.now ≤ 0 then .fail .full else .suspend (.put x (some t)) else .enqueue x) &&
  sameDecision (getLoop q (some t) clock.now)
    (if empty q then if t - clock.now ≤ 0 then .fail .empty else .suspend (.get (some t)) else .dequeue)

def traceCheck (q : Queue Nat) (history : List (Call Nat × Clock)) : Bool :=
  implies (preCheck q) (preCheck (run natCmp q history)) &&
  implies q.isShutdown (run natCmp q history).isShutdown

def batchCheck (xs : List Nat) : Bool :=
  decide ((load natCmp (benchmark_queue 0) xs).items = xs ∧
    (load natCmp (benchmark_lifo_queue 0) xs).items = xs.reverse ∧
    (load natCmp (benchmark_priority_queue 0) xs).items.Perm xs ∧
    (load natCmp (benchmark_priority_queue 0) xs).items.Pairwise (fun a b => natCmp a b = true))

def removalCheck (q : Queue Nat) : Bool := decide (popMany q.items.length q = q.items)

def orderPreservationCheck (q : Queue Nat) (c : Call Nat) (clock : Clock) : Bool :=
  implies (decide (q.kind = .priority ∧ q.items.Pairwise (fun a b => natCmp a b = true)))
    (decide ((step natCmp q c clock).queue.items.Pairwise (fun a b => natCmp a b = true)))

def shutdownSafetyCheck (q : Queue Nat) (x : Nat) (b : Bool) (d : Option Float) (clock : Clock) : Bool :=
  implies q.isShutdown
    (sameStep (put natCmp q x b d clock) ⟨q, .raised .shutDown, []⟩ &&
     implies (empty q) (sameStep (get q b d clock) ⟨q, .raised .shutDown, []⟩))

def postCheck (q : Queue Nat) (x : Nat) (c : Call Nat) (clock : Clock)
    (t : Float) (immediate : Bool) (history : List (Call Nat × Clock)) : Bool :=
  observersCheck q && insertionCheck q x && priorityCheck q.items x &&
  putCheck q x && getCheck q && taskCheck q && shutdownCheck q immediate &&
  capacityCheck q c clock && atomicCheck q c clock && frameCheck q c clock &&
  minimumCheck q && blockingCheck q x clock && timeoutCheck q x t clock &&
  traceCheck q history && batchCheck q.items && removalCheck q &&
  orderPreservationCheck q c clock && sampleDeadlines.all (fun d => shutdownSafetyCheck q x immediate d clock) &&
  preCheck (step natCmp q c clock).queue

-- PBT: observers_prop
example : sampleQueues.all observersCheck = true := by native_decide
-- PBT: insertion_prop
example : sampleQueues.all (fun q => (List.range 5).all (insertionCheck q)) = true := by native_decide
-- PBT: priority_prop, with the total transitive Nat comparator
example : (smallLists 4).all (fun xs => (List.range 5).all (priorityCheck xs)) = true := by native_decide
-- PBT: put_prop
example : sampleQueues.all (fun q => (List.range 5).all (putCheck q)) = true := by native_decide
-- PBT: get_prop
example : sampleQueues.all getCheck = true := by native_decide
-- PBT: task_prop
example : sampleQueues.all taskCheck = true := by native_decide
-- PBT: shutdown_prop, including unfinished < items.length
example : sampleQueues.all (fun q => [false,true].all (shutdownCheck q)) = true := by native_decide
-- PBT: capacity_prop
example : sampleQueues.all (fun q => (sampleCalls 3).all (fun c => sampleClocks.all (capacityCheck q c))) = true := by native_decide
-- PBT: atomic_prop
example : sampleQueues.all (fun q => (sampleCalls 3).all (fun c => sampleClocks.all (atomicCheck q c))) = true := by native_decide
-- PBT: frame_prop
example : sampleQueues.all (fun q => (sampleCalls 3).all (fun c => sampleClocks.all (frameCheck q c))) = true := by native_decide
-- PBT: priority_min_prop
example : sampleQueues.all minimumCheck = true := by native_decide
-- PBT: blocking_prop (also finite, infinite and NaN saved deadlines)
example : sampleQueues.all (fun q => sampleClocks.all (blockingCheck q 3)) = true := by native_decide
-- PBT: timeout_prop; negative, zero, positive, nonfinite and signed-zero timeouts
example : sampleQueues.all (fun q => sampleTimes.all (fun t => sampleClocks.all (timeoutCheck q 3 t))) = true := by native_decide
-- PBT: trace_prop
example : sampleQueues.all (fun q => (List.range 6).all (fun x => traceCheck q (sampleHistory x))) = true := by native_decide
-- PBT: batch_prop
example : (smallLists 5).all batchCheck = true := by native_decide
-- PBT: removal_prop
example : sampleQueues.all removalCheck = true := by native_decide
-- PBT: order_preservation_prop
example : sampleQueues.all (fun q => (sampleCalls 3).all (fun c => sampleClocks.all (orderPreservationCheck q c))) = true := by native_decide
-- PBT: shutdown_safety_prop, every argument mode and all sampled timeout bit patterns
example : sampleQueues.all (fun q => [false,true].all (fun b => sampleDeadlines.all (fun d =>
    sampleClocks.all (shutdownSafetyCheck q 3 b d)))) = true := by native_decide
-- PBT: Post_prop under its unchanged Pre
example : sampleQueues.all (fun q => (sampleCalls 3).all (fun c =>
    implies (preCheck q) (postCheck q 3 c ⟨1,2⟩ 3 true (sampleHistory 3)))) = true := by native_decide
#eval (sampleQueues.length, (smallLists 5).length)
#eval sampleQueues.all (fun q => implies (preCheck q)
  (postCheck q 2 (.resume (.get (some 4))) ⟨1,3⟩ 2 false (sampleHistory 2)))

/-- Kernel-checked correctness, not inferred from the executable tests. -/
theorem correctness (cmp : Comparator α) (q : Queue α) (x : α) (call : Call α)
    (clock : Clock) (t : Float) (immediate : Bool) (history : List (Call α × Clock)) :
    Pre q → Post_prop cmp q x call clock t immediate history := by
  intro hp
  exact ⟨observers_thm q, insertion_thm cmp q x, priority_thm cmp q.items x,
    put_thm cmp q x, get_thm q, task_thm q, shutdown_thm q immediate,
    capacity_thm cmp q call clock, atomic_thm cmp q call clock, frame_thm cmp q call clock,
    priority_min_thm cmp q, blocking_thm cmp q x clock, timeout_thm q x t clock,
    trace_thm cmp q history, batch_thm cmp q.items, removal_thm q,
    order_preservation_thm cmp q call clock, fun d => shutdown_safety_thm cmp q x immediate d clock,
    capacity_thm cmp q call clock hp⟩

/-! ## Imperative implementation
The pure classifier is shared: it is the monitor's guard/continuation logic.
The commit phase below independently performs the state updates with mutable
variables. In particular, it does not call `commit` or `step`.
-/
def commitImperative (cmp : Comparator α) (original : Queue α) (decision : Decision α) : Step α := Id.run do
  let mut q := original
  let mut result : Result α := .done
  let mut notices : List Notice := []
  match decision with
  | .enqueue x =>
    match q.kind with
    | .fifo => q := {q with items := q.items ++ [x]}
    | .lifo => q := {q with items := x :: q.items}
    | .priority => q := {q with items := priorityInsert cmp x q.items}
    q := {q with unfinished := q.unfinished + 1}
    notices := [.notEmptyOne]
  | .dequeue =>
    match q.items with
    | [] => result := .raised .empty
    | x :: xs =>
      q := {q with items := xs}
      result := .value x
      notices := [.notFullOne]
  | .finish =>
    if q.unfinished = 1 then notices := [.allTasksDoneAll]
    q := {q with unfinished := q.unfinished - 1}
  | .joined => pure ()
  | .close immediate =>
    q := {q with isShutdown := true}
    if immediate then
      let count := q.items.length
      q := {q with items := []}
      q := {q with unfinished := q.unfinished - count}
      notices := [.allTasksDoneAll]
    notices := notices ++ [.notEmptyAll, .notFullAll]
  | .fail e => result := .raised e
  | .suspend p => result := .blocked p
  return ⟨q, result, notices⟩

def stepImperative (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock := {}) : Step α :=
  commitImperative cmp q (classify q call clock)

def runImperative (cmp : Comparator α) (q : Queue α) (history : List (Call α × Clock)) : Queue α :=
  history.foldl (fun s event => (stepImperative cmp s event.1 event.2).queue) q

-- Imperative tests: all three strategies, errors, timed suspension and shutdown.
example : (runImperative natCmp (benchmark_queue 5)
    [(.put 111, {}), (.put 333, {}), (.put 222, {})]).items = [111,333,222] := by native_decide
example : (runImperative natCmp (benchmark_lifo_queue 5)
    [(.put 111, {}), (.put 333, {}), (.put 222, {})]).items = [222,333,111] := by native_decide
example : (runImperative pairCmp (benchmark_priority_queue 5)
    [(.put (2,"two"), {}), (.put (1,"one"), {}), (.put (3,"three"), {})]).items =
    [(1,"one"),(2,"two"),(3,"three")] := by native_decide
example : hasError (stepImperative natCmp (load natCmp (benchmark_queue 1) [1]) (.put 2 false)) .full = true := by native_decide
example : isBlocked (stepImperative natCmp (benchmark_queue 2) (.get true (some 4)) ⟨1,2⟩) = true := by native_decide
example : (runImperative natCmp (benchmark_queue 2)
    [(.put 1, {}), (.put 2, {}), (.shutdown true, {})]).unfinished = 0 := by native_decide
#eval runImperative natCmp (benchmark_queue 2) (sampleHistory 3)
example : sampleQueues.all (fun q => (sampleCalls 3).all (fun c => sampleClocks.all (fun clock =>
    sameStep (step natCmp q c clock) (stepImperative natCmp q c clock)))) = true := by native_decide

/-- Equality includes state, return value/exception/continuation, and notifications. -/
theorem commit_equivalence (cmp : Comparator α) (q : Queue α) (d : Decision α) :
    commit cmp q d = commitImperative cmp q d := by
  cases d with
  | enqueue x => cases h : q.kind <;> simp [commit, commitImperative, hookPut, h]
  | dequeue => cases h : q.items <;> simp [commit, commitImperative, h]
  | finish => by_cases h : q.unfinished = 1 <;> simp [commit, commitImperative, h]
  | joined => rfl
  | close b => cases b <;> rfl
  | fail e => rfl
  | suspend p => rfl

theorem equivalence (cmp : Comparator α) (q : Queue α) (call : Call α) (clock : Clock) :
    step cmp q call clock = stepImperative cmp q call clock :=
  commit_equivalence cmp q _

theorem trace_equivalence (cmp : Comparator α) (q : Queue α) (history : List (Call α × Clock)) :
    run cmp q history = runImperative cmp q history := by
  induction history generalizing q with
  | nil => rfl
  | cons event rest ih =>
    rcases event with ⟨c, t⟩
    simp only [run, runImperative, List.foldl_cons]
    rw [equivalence]
    exact ih _

end QueueThreadsafe
end Agent
