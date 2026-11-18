import Mathlib
namespace Agent

/-!
# A single-threaded LRU cache

Translation of the benchmark's `functools.lru_cache`. Keys are lists of Python
integers (Lean `Int`); keyword arguments are empty, as stipulated by `_make_key`.
The result type is arbitrary. A total user function is supplied explicitly;
`calls` records its invocations, including those before `cache_clear`.
The dummy lock has no effect. An MRU-first association list represents the
Python dictionary together with its circular doubly-linked queue: the last
entry is the eviction victim. Pointer identity is not observable through this
interface. Callback exceptions, concurrent threads and reentrant callbacks are
not operations of this total, single-threaded benchmark model.

A decorator is represented by its closure environment `Config`; `decorate`
applies it to a function. `MaxArg.callable` represents direct decoration, while
`invalid` represents any non-integer, non-None, non-callable argument. Python
Booleans, which are integers, are represented by `.integer 0` and `.integer 1`.
-/

namespace FunctoolsLRU

abbrev Key := List Int

def makeKey (args : Key) (_typed : Bool) : Key := args

structure Config where
  maxsize : Option Nat := some 128
  typed : Bool := false
  deriving Repr, DecidableEq

inductive MaxArg (α : Type) where
  | integer (n : Int)
  | none
  | callable (f : Key → α)
  | invalid

def pre_lru_cache (arg : MaxArg α) (_typed : Bool := false) : Bool :=
  match arg with
  | .integer _ | .none => true
  | _ => false

structure CacheState (α : Type) where
  entries : List (Key × α) := []
  hits : Nat := 0
  misses : Nat := 0
  calls : Nat := 0
  deriving Repr, DecidableEq

structure CacheInfo where
  hits : Nat
  misses : Nat
  maxsize : Option Nat
  currsize : Nat
  deriving Repr, DecidableEq

def cache_info (cap : Option Nat) (s : CacheState α) : CacheInfo :=
  ⟨s.hits, s.misses, cap, s.entries.length⟩

def cache_clear (s : CacheState α) : CacheState α :=
  { calls := s.calls }

def lookup (key : Key) : List (Key × α) → Option α
  | [] => none
  | (k, v) :: es => if key = k then some v else lookup key es

def eraseKey (key : Key) (es : List (Key × α)) : List (Key × α) :=
  es.filter (fun e => e.1 != key)

/-- A call returns its value and the new closure state. -/
def step (cap : Option Nat) (f : Key → α) (key : Key)
    (s : CacheState α) : α × CacheState α :=
  match cap with
  | some 0 =>
      (f key, { s with misses := s.misses + 1, calls := s.calls + 1 })
  | none =>
      match lookup key s.entries with
      | some v => (v, { s with hits := s.hits + 1 })
      | none =>
          (f key, { s with entries := (key, f key) :: s.entries, misses := s.misses + 1, calls := s.calls + 1 })
  | some (n + 1) =>
      match lookup key s.entries with
      | some v =>
          (v, { s with entries := (key, v) :: eraseKey key s.entries, hits := s.hits + 1 })
      | none =>
          (f key, { s with entries := (key, f key) :: s.entries.take n, misses := s.misses + 1, calls := s.calls + 1 })

def run (cap : Option Nat) (f : Key → α) :
    List Key → CacheState α → List α × CacheState α
  | [], s => ([], s)
  | key :: keys, s =>
      let (v, s') := step cap f key s
      let (vs, s'') := run cap f keys s'
      (v :: vs, s'')

structure Wrapper (α : Type) where
  userFunction : Key → α
  config : Config
  state : CacheState α

def decorate (cfg : Config) (f : Key → α) : Wrapper α :=
  ⟨f, cfg, {}⟩

def wrapperCall (w : Wrapper α) (args : Key) : α × Wrapper α :=
  let (v, s) := step w.config.maxsize w.userFunction (makeKey args w.config.typed) w.state
  (v, { w with state := s })

def wrapperClear (w : Wrapper α) : Wrapper α :=
  { w with state := cache_clear w.state }

def cache_parameters (w : Wrapper α) : Config := w.config

def typeError : String := "Expected first argument to be an integer or None"

/-- `lru_cache` returns a decorator closure, whose environment is `Config`. -/
def lru_cache (arg : MaxArg α := .integer 128) (typed : Bool := false) :
    Except String Config :=
  match arg with
  | .integer n => .ok ⟨some n.toNat, typed⟩
  | .none => .ok ⟨none, typed⟩
  | _ => .error typeError

inductive Decoration (α : Type) where
  | decorator (config : Config)
  | wrapped (wrapper : Wrapper α)

def Decoration.config : Decoration α → Config
  | .decorator cfg => cfg
  | .wrapped w => w.config

def benchmark_lru_cache (arg : MaxArg α := .integer 128) (typed : Bool := false) :
    Except String (Decoration α) :=
  match arg with
  | .callable f => .ok (.wrapped (decorate ⟨some 128, typed⟩ f))
  | _ => (lru_cache arg typed).map Decoration.decorator

/-- Configuration visible to the caller; invalid arguments have no configuration. -/
def effectiveConfig (arg : MaxArg α) (typed : Bool) : Option Config :=
  match arg with
  | .integer n => some ⟨some n.toNat, typed⟩
  | .none => some ⟨none, typed⟩
  | .callable _ => some ⟨some 128, typed⟩
  | .invalid => none

def observedConfig (r : Except String (Decoration α)) : Option Config :=
  match r with
  | .ok d => some d.config
  | .error _ => none

def selectedFunction (arg : MaxArg α) (fallback : Key → α) : Key → α :=
  match arg with
  | .callable f => f
  | _ => fallback

def instantiate (d : Decoration α) (f : Key → α) : Wrapper α :=
  match d with
  | .decorator cfg => decorate cfg f
  | .wrapped w => w

/-- Applying the benchmark result and then calling it on an entire trace. -/
def benchmarkRun (arg : MaxArg α) (typed : Bool) (f : Key → α) (xs : List Key) :
    Except String (List α × CacheState α) :=
  match benchmark_lru_cache arg typed with
  | .error e => .error e
  | .ok d =>
      let w := instantiate d f
      .ok (run w.config.maxsize w.userFunction xs w.state)

-- Unit tests, including every scenario in the supplied Python check.
def timesTen (xs : Key) : Int := xs.sum * 10

def basicInputs : List Key :=
  [7, 9, 7, 9, 7, 9, 8, 8, 8, 9, 9, 9, 8, 8, 8, 7].map (fun n => [n])

def basicRun := run (some 2) timesTen basicInputs ({} : CacheState Int)

example : basicRun.1 = basicInputs.map timesTen := by native_decide
example : cache_info (some 2) basicRun.2 = ⟨12, 4, some 2, 2⟩ := by native_decide
example : basicRun.2.calls = 4 := by native_decide
example : basicRun.2.entries = [([7], 70), ([8], 80)] := by native_decide
example : cache_info (some 2) (cache_clear basicRun.2) = ⟨0, 0, some 2, 0⟩ := by native_decide
example : (cache_clear basicRun.2).calls = 4 := by native_decide

def addRun := run none (fun xs : Key => xs.sum)
  [[1, 2], [1, 2], [2, 3], [2, 3]] ({} : CacheState Int)
example : cache_info none addRun.2 = ⟨2, 2, none, 2⟩ ∧ addRun.2.calls = 2 := by native_decide

def mulRun := run (some 0) (fun xs : Key => xs.prod)
  [[1, 2], [1, 2], [2, 3]] ({} : CacheState Int)
example : mulRun.1 = [2, 2, 6] ∧ cache_info (some 0) mulRun.2 = ⟨0, 3, some 0, 0⟩ ∧
    mulRun.2.calls = 3 := by native_decide
example : (match lru_cache (α := Int) (.integer (-7)) true with
    | .ok cfg => cfg == ⟨some 0, true⟩ | .error _ => false) = true := by native_decide
example : observedConfig (benchmark_lru_cache (.callable timesTen)) = some ⟨some 128, false⟩ := by native_decide
example : (match benchmark_lru_cache (α := Int) .invalid with
    | .error e => e == typeError | .ok _ => false) = true := by native_decide
example : (wrapperCall (decorate ⟨some 2, true⟩ timesTen) [7]).1 = 70 := by native_decide
#eval cache_info (some 2) basicRun.2
#eval (addRun.1, cache_info none addRun.2, mulRun.1, cache_info (some 0) mulRun.2)

/-- Admissibility for the *benchmark*: direct decoration is also accepted.
`pre_lru_cache` above is the narrower predicate used inside the Python wrapper. -/
def Pre (arg : MaxArg α) (_typed : Bool) : Prop :=
  match arg with
  | .invalid => False
  | _ => True

/-! ## Specifications and kernel-checked proofs -/

def keys_prop (args : Key) (typed : Bool) : Prop := makeKey args typed = args

theorem keys_thm (args : Key) (typed : Bool) : keys_prop args typed := rfl

def configuration_prop (arg : MaxArg α) (typed : Bool) : Prop :=
  observedConfig (benchmark_lru_cache arg typed) = effectiveConfig arg typed ∧
  (benchmark_lru_cache arg typed = .error typeError ↔ ¬ Pre arg typed)

theorem configuration_thm (arg : MaxArg α) (typed : Bool) : configuration_prop arg typed := by
  cases arg <;> simp [configuration_prop, benchmark_lru_cache, lru_cache,
    observedConfig, effectiveConfig, Decoration.config, decorate, Pre, Except.map]

def direct_prop (f : Key → α) (typed : Bool) : Prop :=
  benchmark_lru_cache (.callable f) typed =
    .ok (.wrapped (decorate ⟨some 128, typed⟩ f))

theorem direct_thm (f : Key → α) (typed : Bool) : direct_prop f typed := rfl

def normalization_prop {α : Type} (n : Int) (typed : Bool) : Prop :=
  lru_cache (α := α) (.integer n) typed = .ok ⟨some n.toNat, typed⟩ ∧
  (n < 0 → n.toNat = 0)

theorem normalization_thm (n : Int) (typed : Bool) : normalization_prop (α := α) n typed := by
  refine ⟨rfl, ?_⟩
  intro h
  omega

def clear_prop (cap : Option Nat) (s : CacheState α) : Prop :=
  cache_info cap (cache_clear s) = ⟨0, 0, cap, 0⟩ ∧
  (cache_clear s).entries = [] ∧ (cache_clear s).calls = s.calls

theorem clear_thm (cap : Option Nat) (s : CacheState α) : clear_prop cap s := by
  exact ⟨rfl, rfl, rfl⟩

/-- Disabled caching always executes the callback and never changes the cache. -/
def disabled_prop (f : Key → α) (k : Key) (s : CacheState α) : Prop :=
  step (some 0) f k s =
    (f k, { s with misses := s.misses + 1, calls := s.calls + 1 })

theorem disabled_thm (f : Key → α) (k : Key) (s : CacheState α) : disabled_prop f k s := rfl

/-- Unbounded caching never removes or reorders an existing entry. -/
def unbounded_prop (f : Key → α) (k : Key) (s : CacheState α) : Prop :=
  step none f k s = match lookup k s.entries with
  | some v => (v, { s with hits := s.hits + 1 })
  | none => (f k, { s with entries := (k, f k) :: s.entries, misses := s.misses + 1, calls := s.calls + 1 })

theorem unbounded_thm (f : Key → α) (k : Key) (s : CacheState α) : unbounded_prop f k s := rfl

/-- Exact LRU transition: promote a hit; on a miss keep the newest `n` old
entries. Thus at capacity `n+1` exactly the oldest entry is evicted. -/
def lru_policy_prop (n : Nat) (f : Key → α) (k : Key) (s : CacheState α) : Prop :=
  step (some (n + 1)) f k s = match lookup k s.entries with
  | some v => (v, { s with entries := (k, v) :: eraseKey k s.entries, hits := s.hits + 1 })
  | none => (f k, { s with entries := (k, f k) :: s.entries.take n, misses := s.misses + 1, calls := s.calls + 1 })

theorem lru_policy_thm (n : Nat) (f : Key → α) (k : Key) (s : CacheState α) :
    lru_policy_prop n f k s := rfl

/-- Every cached value is the value of the supplied user function. -/
def Sound (f : Key → α) (s : CacheState α) : Prop :=
  ∀ e ∈ s.entries, e.2 = f e.1

def Unique (s : CacheState α) : Prop := (s.entries.map Prod.fst).Nodup

def Fits (cap : Option Nat) (s : CacheState α) : Prop :=
  match cap with
  | none => True
  | some n => s.entries.length ≤ n

def Valid (cap : Option Nat) (f : Key → α) (s : CacheState α) : Prop :=
  Sound f s ∧ Unique s ∧ Fits cap s

private theorem lookup_mem {k : Key} {es : List (Key × α)} {v : α}
    (h : lookup k es = some v) : (k, v) ∈ es := by
  induction es with
  | nil => simp [lookup] at h
  | cons e es ih =>
      rcases e with ⟨j, w⟩
      by_cases hj : k = j
      · simp [lookup, hj] at h
        subst j
        subst w
        simp
      · simp [lookup, hj] at h
        exact List.mem_cons_of_mem _ (ih h)

private theorem lookup_none_iff (k : Key) (es : List (Key × α)) :
    lookup k es = none ↔ k ∉ es.map Prod.fst := by
  induction es with
  | nil => simp [lookup]
  | cons e es ih =>
      rcases e with ⟨j, w⟩
      by_cases hj : k = j <;> simp [lookup, hj, ih]

private theorem erase_length_lt {k : Key} {es : List (Key × α)} {v : α}
    (h : lookup k es = some v) : (eraseKey k es).length < es.length := by
  induction es with
  | nil => simp [lookup] at h
  | cons e es ih =>
      rcases e with ⟨j, w⟩
      by_cases hj : k = j
      · subst j
        have hle := List.length_filter_le (fun e : Key × α => e.1 != k) es
        simpa [eraseKey] using Nat.lt_succ_of_le hle
      · have hh : lookup k es = some v := by simpa [lookup, hj] using h
        have ht := ih hh
        simpa [eraseKey, Ne.symm hj] using Nat.succ_lt_succ ht

private theorem sound_lookup {f : Key → α} {s : CacheState α} {k : Key} {v : α}
    (hs : Sound f s) (h : lookup k s.entries = some v) : v = f k :=
  hs (k, v) (lookup_mem h)

private theorem step_sound (cap : Option Nat) (f : Key → α) (k : Key)
    (s : CacheState α) (hs : Sound f s) : Sound f (step cap f k s).2 := by
  have herase : ∀ e ∈ eraseKey k s.entries, e.2 = f e.1 := by
    intro e he
    exact hs e (List.mem_of_mem_filter he)
  have htake : ∀ n, ∀ e ∈ s.entries.take n, e.2 = f e.1 := by
    intro n e he
    exact hs e (List.mem_of_mem_take he)
  cases cap with
  | none =>
      cases h : lookup k s.entries with
      | none => simpa [step, h, Sound] using And.intro (Eq.refl (f k)) hs
      | some v => simpa [step, h, Sound] using hs
  | some n =>
      cases n with
      | zero => exact hs
      | succ n =>
          cases h : lookup k s.entries with
          | none => simpa [step, h, Sound] using And.intro (Eq.refl (f k)) (htake n)
          | some v => simpa [step, h, Sound] using And.intro (sound_lookup hs h) herase

private theorem step_value (cap : Option Nat) (f : Key → α) (k : Key)
    (s : CacheState α) (hs : Sound f s) : (step cap f k s).1 = f k := by
  cases cap with
  | none =>
      cases h : lookup k s.entries with
      | none => simp [step, h]
      | some v => simpa [step, h] using sound_lookup hs h
  | some n =>
      cases n with
      | zero => rfl
      | succ n =>
          cases h : lookup k s.entries with
          | none => simp [step, h]
          | some v => simpa [step, h] using sound_lookup hs h

private theorem step_unique (cap : Option Nat) (f : Key → α) (k : Key)
    (s : CacheState α) (hu : Unique s) : Unique (step cap f k s).2 := by
  have herase : ((eraseKey k s.entries).map Prod.fst).Nodup :=
    hu.sublist (List.Sublist.map _ List.filter_sublist)
  have hnot : k ∉ (eraseKey k s.entries).map Prod.fst := by
    simp [eraseKey, List.mem_map, List.mem_filter]
  have htake : ∀ n, ((s.entries.take n).map Prod.fst).Nodup :=
    fun n => hu.sublist ((List.take_sublist n s.entries).map _)
  cases cap with
  | none =>
      cases h : lookup k s.entries with
      | none =>
          have hn := (lookup_none_iff k s.entries).mp h
          simpa [step, h, Unique] using And.intro hn hu
      | some v => simpa [step, h, Unique] using hu
  | some n =>
      cases n with
      | zero => exact hu
      | succ n =>
          cases h : lookup k s.entries with
          | none =>
              have hn := (lookup_none_iff k s.entries).mp h
              have hnt : k ∉ (s.entries.take n).map Prod.fst :=
                fun hm => hn (((List.take_sublist n s.entries).map Prod.fst).subset hm)
              simpa [step, h, Unique] using And.intro hnt (htake n)
          | some v => simpa [step, h, Unique] using And.intro hnot herase

private theorem step_fits (cap : Option Nat) (f : Key → α) (k : Key)
    (s : CacheState α) (hc : Fits cap s) : Fits cap (step cap f k s).2 := by
  cases cap with
  | none => trivial
  | some n =>
      cases n with
      | zero => exact hc
      | succ n =>
          cases h : lookup k s.entries with
          | none => simp [Fits, step, h, List.length_take]
          | some v =>
              have ht := erase_length_lt h
              simp only [Fits] at hc
              simp only [step, h, Fits, List.length_cons]
              omega

private theorem step_valid (cap : Option Nat) (f : Key → α) (k : Key)
    (s : CacheState α) (hs : Valid cap f s) : Valid cap f (step cap f k s).2 :=
  ⟨step_sound cap f k s hs.1, step_unique cap f k s hs.2.1, step_fits cap f k s hs.2.2⟩

private theorem empty_valid (cap : Option Nat) (f : Key → α) :
    Valid cap f ({} : CacheState α) := by
  cases cap <;> simp [Valid, Sound, Unique, Fits]

/-- Correct outputs for every trace, not just the benchmark's examples. -/
def results_prop (cap : Option Nat) (f : Key → α) (s : CacheState α) (xs : List Key) : Prop :=
  Sound f s → (run cap f xs s).1 = xs.map f

theorem results_thm (cap : Option Nat) (f : Key → α) (s : CacheState α) (xs : List Key) :
    results_prop cap f s xs := by
  intro hs
  induction xs generalizing s with
  | nil => rfl
  | cons k xs ih =>
      simp only [run, List.map_cons]
      rw [step_value cap f k s hs, ih _ (step_sound cap f k s hs)]

/-- Distinct dictionary keys, correct cached values, and the capacity bound
hold after arbitrary traces, starting from any well-formed state. -/
def invariant_prop (cap : Option Nat) (f : Key → α) (s : CacheState α) (xs : List Key) : Prop :=
  Valid cap f s → Valid cap f (run cap f xs s).2

theorem invariant_thm (cap : Option Nat) (f : Key → α) (s : CacheState α) (xs : List Key) :
    invariant_prop cap f s xs := by
  intro hs
  induction xs generalizing s with
  | nil => exact hs
  | cons k xs ih => exact ih _ (step_valid cap f k s hs)

private theorem step_accounting (cap : Option Nat) (f : Key → α) (k : Key) (s : CacheState α) :
    (step cap f k s).2.hits + (step cap f k s).2.misses = s.hits + s.misses + 1 ∧
    (step cap f k s).2.calls + (step cap f k s).2.hits = s.calls + s.hits + 1 := by
  cases cap with
  | none => cases h : lookup k s.entries <;> simp [step, h] <;> omega
  | some n =>
      cases n with
      | zero => simp [step]; omega
      | succ n => cases h : lookup k s.entries <;> simp [step, h] <;> omega

/-- Each call is exactly one hit or miss, and the callback runs exactly on misses. -/
def accounting_prop (cap : Option Nat) (f : Key → α) (s : CacheState α) (xs : List Key) : Prop :=
  (run cap f xs s).2.hits + (run cap f xs s).2.misses = s.hits + s.misses + xs.length ∧
  (run cap f xs s).2.calls + (run cap f xs s).2.hits = s.calls + s.hits + xs.length

theorem accounting_thm (cap : Option Nat) (f : Key → α) (s : CacheState α) (xs : List Key) :
    accounting_prop cap f s xs := by
  induction xs generalizing s with
  | nil => simp [accounting_prop, run]
  | cons k xs ih =>
      have hi := ih (step cap f k s).2
      have ht := step_accounting cap f k s
      simp only [accounting_prop, run, List.length_cons] at *
      omega


/-- Both call and clear preserve the decorator's public parameters. -/
def parameters_prop (w : Wrapper α) (k : Key) : Prop :=
  cache_parameters (wrapperCall w k).2 = cache_parameters w ∧
  cache_parameters (wrapperClear w) = cache_parameters w

theorem parameters_thm (w : Wrapper α) (k : Key) : parameters_prop w k := by
  exact ⟨rfl, rfl⟩

/-- The benchmark's simplified key function ignores `typed`. -/
def typed_prop (cap : Option Nat) (f : Key → α) (s : CacheState α)
    (k : Key) (t₁ t₂ : Bool) : Prop :=
  let a := wrapperCall ⟨f, ⟨cap, t₁⟩, s⟩ k
  let b := wrapperCall ⟨f, ⟨cap, t₂⟩, s⟩ k
  a.1 = b.1 ∧ a.2.state = b.2.state

theorem typed_thm (cap : Option Nat) (f : Key → α) (s : CacheState α)
    (k : Key) (t₁ t₂ : Bool) : typed_prop cap f s k t₁ t₂ := by
  exact ⟨rfl, rfl⟩

private theorem step_remembers (cap : Option Nat) (f : Key → α) (k : Key)
    (s : CacheState α) (hc : cap ≠ some 0) :
    lookup k (step cap f k s).2.entries = some (step cap f k s).1 := by
  cases cap with
  | none => cases h : lookup k s.entries <;> simp [step, h, lookup]
  | some n =>
      cases n with
      | zero => exact (hc rfl).elim
      | succ n => cases h : lookup k s.entries <;> simp [step, h, lookup]

/-- An immediate repeated call hits and does not reexecute the user function. -/
def repeat_prop (cap : Option Nat) (f : Key → α) (k : Key) (s : CacheState α) : Prop :=
  cap ≠ some 0 →
  let first := step cap f k s
  let second := step cap f k first.2
  second.1 = first.1 ∧ second.2.hits = first.2.hits + 1 ∧
  second.2.misses = first.2.misses ∧ second.2.calls = first.2.calls

theorem repeat_thm (cap : Option Nat) (f : Key → α) (k : Key) (s : CacheState α) :
    repeat_prop cap f k s := by
  intro hc
  cases cap with
  | none => cases h : lookup k s.entries <;> simp [step, h, lookup]
  | some n =>
      cases n with
      | zero => exact (hc rfl).elim
      | succ n => cases h : lookup k s.entries <;> simp [step, h, lookup]

/-- The external benchmark execution agrees with its resolved configuration
and uses the supplied callable rather than the fallback on direct decoration. -/
def execution_prop (arg : MaxArg α) (typed : Bool) (f : Key → α) (xs : List Key) : Prop :=
  benchmarkRun arg typed f xs =
    match effectiveConfig arg typed with
    | none => .error typeError
    | some cfg => .ok (run cfg.maxsize (selectedFunction arg f) xs {})

theorem execution_thm (arg : MaxArg α) (typed : Bool) (f : Key → α) (xs : List Key) :
    execution_prop arg typed f xs := by
  cases arg <;> rfl


/-- In a full cache a miss removes exactly the final (least-recently-used)
entry, rather than an arbitrary entry or the most recently used entry. -/
def eviction_prop (n : Nat) (f : Key → α) (k : Key) (s : CacheState α) : Prop :=
  s.entries.length = n + 1 → lookup k s.entries = none →
  (step (some (n + 1)) f k s).2.entries = (k, f k) :: s.entries.dropLast

theorem eviction_thm (n : Nat) (f : Key → α) (k : Key) (s : CacheState α) :
    eviction_prop n f k s := by
  intro hlen hmiss
  simp [step, hmiss, List.dropLast_eq_take, hlen]

/-! ## Post-condition
Besides the individual laws, the post-condition connects the externally
resolved decorator to correct results, a well-formed final cache, and exact
statistics. It applies to every finite call trace and every total user function.
-/

def Post_prop (arg : MaxArg α) (typed : Bool) (f : Key → α) (xs : List Key) : Prop :=
  configuration_prop arg typed ∧ execution_prop arg typed f xs ∧
  ∃ cfg, effectiveConfig arg typed = some cfg ∧
    let g := selectedFunction arg f
    let s : CacheState α := {}
    let final := (run cfg.maxsize g xs s).2
    results_prop cfg.maxsize g s xs ∧ invariant_prop cfg.maxsize g s xs ∧
    accounting_prop cfg.maxsize g s xs ∧ clear_prop cfg.maxsize final ∧
    benchmarkRun arg typed f xs = .ok (xs.map g, final) ∧
    Valid cfg.maxsize g final ∧ final.hits + final.misses = xs.length ∧
    final.calls = final.misses

/-! ## Bounded property-based tests
We enumerate every trace of length at most four over four keys (341 traces),
five capacity modes, and three different callbacks. Further checks vary both
`typed` values, invalid/direct arguments, negative sizes, and initial counters.
These are executable evidence only: no named theorem uses `native_decide`.
-/

def sampleKeys : List Key := [[], [-1], [2], [1, 2]]
def traces : Nat → List (List Key)
  | 0 => [[]]
  | n + 1 => [] :: sampleKeys.flatMap (fun k => (traces n).map (k :: ·))
def sampleCaps : List (Option Nat) := [some 0, some 1, some 2, some 3, none]
def sampleFunctions : List (Key → Int) := [List.sum, List.prod, timesTen]

def allScenarios (p : Option Nat → (Key → Int) → List Key → Bool) : Bool :=
  sampleCaps.all fun cap => sampleFunctions.all fun f => (traces 4).all (p cap f)

def sampleArgs : List (MaxArg Int) :=
  [.integer (-3), .integer 0, .integer 1, .integer 2, .integer 128,
   .none, .callable timesTen, .invalid]

def soundCheck (f : Key → Int) (s : CacheState Int) : Bool :=
  s.entries.all (fun e => e.2 == f e.1)

def validCheck (cap : Option Nat) (f : Key → Int) (s : CacheState Int) : Bool :=
  soundCheck f s && decide (s.entries.map Prod.fst).Nodup &&
    match cap with
    | none => true
    | some n => decide (s.entries.length ≤ n)

def clearCheck (cap : Option Nat) (s : CacheState Int) : Bool :=
  cache_info cap (cache_clear s) == ⟨0, 0, cap, 0⟩ &&
  (cache_clear s).entries == [] && (cache_clear s).calls == s.calls

def runView (r : Except String (List Int × CacheState Int)) :
    Option String × Option (List Int × CacheState Int) :=
  match r with
  | .error e => (some e, none)
  | .ok p => (none, some p)

def configurationCheck (arg : MaxArg Int) (typed : Bool) : Bool :=
  observedConfig (benchmark_lru_cache arg typed) == effectiveConfig arg typed &&
  match arg, benchmark_lru_cache arg typed with
  | .invalid, .error e => e == typeError
  | .invalid, .ok _ => false
  | _, .error _ => false
  | _, .ok _ => true

def executionCheck (arg : MaxArg Int) (typed : Bool) (f : Key → Int) (xs : List Key) : Bool :=
  runView (benchmarkRun arg typed f xs) == runView
    (match effectiveConfig arg typed with
     | none => .error typeError
     | some cfg => .ok (run cfg.maxsize (selectedFunction arg f) xs {}))

-- PBT: keys_prop.
example : (sampleKeys.all fun k => [false, true].all fun t => makeKey k t == k) = true := by native_decide
-- PBT: configuration_prop, including the invalid case.
example : (sampleArgs.all fun a => [false, true].all (configurationCheck a)) = true := by native_decide
-- PBT: direct_prop; inspect the wrapped closure by executing many arguments.
example : (sampleFunctions.all fun f => [false, true].all fun t =>
    match benchmark_lru_cache (.callable f) t with
    | .ok (.wrapped w) => w.config == ⟨some 128, t⟩ && w.state == ({} : CacheState Int) &&
        sampleKeys.all (fun k => (wrapperCall w k).1 == f k)
    | _ => false) = true := by native_decide
-- PBT: normalization_prop, including a range of negative integers.
example : ((List.range 41).all fun i => [false, true].all fun t =>
    let n : Int := (i : Int) - 20
    match lru_cache (α := Int) (.integer n) t with
    | .ok cfg => cfg == ⟨some n.toNat, t⟩ && (!decide (n < 0) || decide (n.toNat = 0))
    | .error _ => false) = true := by native_decide
-- PBT: clear_prop.
example : allScenarios (fun cap f xs => clearCheck cap (run cap f xs {}).2) = true := by native_decide
-- PBT: disabled_prop, also from nonzero counters and nonempty states.
example : allScenarios (fun cap f xs => sampleKeys.all fun k =>
    let s := (run cap f xs {}).2
    step (some 0) f k s == (f k, { s with misses := s.misses + 1, calls := s.calls + 1 })) = true := by native_decide
-- PBT: unbounded_prop.
example : allScenarios (fun cap f xs => sampleKeys.all fun k =>
    let s := (run cap f xs {}).2
    step none f k s == (match lookup k s.entries with
      | some v => (v, { s with hits := s.hits + 1 })
      | none => (f k, { s with entries := (k, f k) :: s.entries, misses := s.misses + 1, calls := s.calls + 1 }))) = true := by native_decide
-- PBT: lru_policy_prop.
example : allScenarios (fun cap f xs => sampleKeys.all fun k => (List.range 4).all fun n =>
    let s := (run cap f xs {}).2
    step (some (n + 1)) f k s == (match lookup k s.entries with
      | some v => (v, { s with entries := (k, v) :: eraseKey k s.entries, hits := s.hits + 1 })
      | none => (f k, { s with entries := (k, f k) :: s.entries.take n, misses := s.misses + 1, calls := s.calls + 1 }))) = true := by native_decide
-- PBT: results_prop, starting both empty and from an already populated cache.
example : allScenarios (fun cap f xs =>
    let s := (run cap f (xs.reverse) {}).2
    (run cap f xs {}).1 == xs.map f &&
    (!soundCheck f s || (run cap f xs s).1 == xs.map f)) = true := by native_decide
-- PBT: invariant_prop, including continuation from a populated state.
example : allScenarios (fun cap f xs =>
    let s := (run cap f xs {}).2
    validCheck cap f s && (!validCheck cap f s || validCheck cap f (run cap f xs.reverse s).2)) = true := by native_decide
-- PBT: accounting_prop, with arbitrary nonzero starting counters.
example : allScenarios (fun cap f xs =>
    let s : CacheState Int := { (run cap f xs {}).2 with hits := 7, misses := 11, calls := 19 }
    let final := (run cap f xs s).2
    final.hits + final.misses == s.hits + s.misses + xs.length &&
    final.calls + final.hits == s.calls + s.hits + xs.length) = true := by native_decide
-- PBT: parameters_prop.
example : allScenarios (fun cap f xs => sampleKeys.all fun k => [false, true].all fun t =>
    let w : Wrapper Int := ⟨f, ⟨cap, t⟩, (run cap f xs {}).2⟩
    cache_parameters (wrapperCall w k).2 == cache_parameters w &&
    cache_parameters (wrapperClear w) == cache_parameters w) = true := by native_decide
-- PBT: typed_prop.
example : allScenarios (fun cap f xs => sampleKeys.all fun k =>
    let s := (run cap f xs {}).2
    let a := wrapperCall ⟨f, ⟨cap, false⟩, s⟩ k
    let b := wrapperCall ⟨f, ⟨cap, true⟩, s⟩ k
    a.1 == b.1 && a.2.state == b.2.state) = true := by native_decide
-- PBT: repeat_prop. The disabled mode is its explicitly excluded antecedent.
example : allScenarios (fun cap f xs => sampleKeys.all fun k =>
    let first := step cap f k (run cap f xs {}).2
    let second := step cap f k first.2
    cap == some 0 || (second.1 == first.1 && second.2.hits == first.2.hits + 1 &&
      second.2.misses == first.2.misses && second.2.calls == first.2.calls)) = true := by native_decide
-- PBT: execution_prop, including errors and direct decoration.
example : (sampleArgs.all fun a => [false, true].all fun t => sampleFunctions.all fun f =>
    (traces 4).all (executionCheck a t f)) = true := by native_decide
-- PBT: eviction_prop; test all full nonempty traces and every absent candidate.
example : allScenarios (fun cap f xs => sampleKeys.all fun k =>
    let s := (run cap f xs {}).2
    let n := s.entries.length - 1
    !(decide (s.entries.length = n + 1) && (lookup k s.entries == none)) ||
      (step (some (n + 1)) f k s).2.entries == (k, f k) :: s.entries.dropLast) = true := by native_decide

/-- Boolean form of the full post-condition, evaluated only for admissible arguments. -/
def postCheck (arg : MaxArg Int) (typed : Bool) (f : Key → Int) (xs : List Key) : Bool :=
  configurationCheck arg typed && executionCheck arg typed f xs &&
  match effectiveConfig arg typed, benchmarkRun arg typed f xs with
  | some cfg, .ok (values, final) =>
      let g := selectedFunction arg f
      values == xs.map g && validCheck cfg.maxsize g final &&
      final.hits + final.misses == xs.length && final.calls == final.misses &&
      final.calls + final.hits == xs.length && clearCheck cfg.maxsize final
  | _, _ => false

-- PBT: Post_prop. The filter is precisely the public benchmark precondition.
example : (sampleArgs.all fun a =>
    match a with
    | .invalid => true
    | _ => [false, true].all fun t => sampleFunctions.all fun f =>
        (traces 4).all (postCheck a t f)) = true := by native_decide
#eval (traces 4).length
#eval allScenarios (fun cap f xs => validCheck cap f (run cap f xs {}).2)
#eval postCheck (.integer 2) false timesTen basicInputs

/-- Total correctness of all successful benchmark modes. Invalid arguments
are covered by `configuration_thm` and `execution_thm` instead. -/
theorem correctness_thm (arg : MaxArg α) (typed : Bool) (f : Key → α) (xs : List Key) :
    Pre arg typed → Post_prop arg typed f xs := by
  intro hp
  have hcfg : ∃ cfg, effectiveConfig arg typed = some cfg := by
    cases arg <;> simp_all [Pre, effectiveConfig]
  obtain ⟨cfg, hcfg⟩ := hcfg
  refine ⟨configuration_thm arg typed, execution_thm arg typed f xs, cfg, hcfg, ?_⟩
  let g := selectedFunction arg f
  let final := (run cfg.maxsize g xs ({} : CacheState α)).2
  have hv := empty_valid cfg.maxsize g
  have hr := results_thm cfg.maxsize g {} xs
  have hi := invariant_thm cfg.maxsize g {} xs
  have ha := accounting_thm cfg.maxsize g {} xs
  refine ⟨hr, hi, ha, clear_thm cfg.maxsize final, ?_, hi hv, ?_, ?_⟩
  · have he := execution_thm arg typed f xs
    unfold execution_prop at he
    rw [hcfg] at he
    simp only at he
    rw [he]
    have hout := hr hv.1
    exact congrArg Except.ok (Prod.ext hout rfl)
  · have h := ha.1
    simpa [accounting_prop, final] using h
  · have h₁ := ha.1
    have h₂ := ha.2
    change final.hits + final.misses = 0 + 0 + xs.length at h₁
    change final.calls + final.hits = 0 + 0 + xs.length at h₂
    change final.calls = final.misses
    omega

/-! ## Imperative implementation
The mutation below is local to `Id.run`: the closure's entries, hits, misses,
and callback counter are updated separately. The trace runner uses a `for`
loop; it does not call the functional trace runner.
-/

def stepImperative (cap : Option Nat) (f : Key → α) (k : Key)
    (s : CacheState α) : α × CacheState α := Id.run do
  let mut entries := s.entries
  let mut hits := s.hits
  let mut misses := s.misses
  let mut calls := s.calls
  match cap with
  | some 0 =>
      misses := misses + 1
      calls := calls + 1
      let result := f k
      return (result, ⟨entries, hits, misses, calls⟩)
  | none =>
      match lookup k entries with
      | some result =>
          hits := hits + 1
          return (result, ⟨entries, hits, misses, calls⟩)
      | none =>
          misses := misses + 1
          calls := calls + 1
          let result := f k
          entries := (k, result) :: entries
          return (result, ⟨entries, hits, misses, calls⟩)
  | some (n + 1) =>
      match lookup k entries with
      | some result =>
          entries := eraseKey k entries
          entries := (k, result) :: entries
          hits := hits + 1
          return (result, ⟨entries, hits, misses, calls⟩)
      | none =>
          misses := misses + 1
          calls := calls + 1
          let result := f k
          entries := entries.take n
          entries := (k, result) :: entries
          return (result, ⟨entries, hits, misses, calls⟩)

/-- An initial output accumulator makes the loop invariant explicit. -/
def runImperativeAux (cap : Option Nat) (f : Key → α) (xs : List Key)
    (s : CacheState α) (acc : List α) : List α × CacheState α := Id.run do
  let mut state := s
  let mut output := acc
  for k in xs do
    let (v, next) := stepImperative cap f k state
    state := next
    output := output ++ [v]
  return (output, state)

def runImperative (cap : Option Nat) (f : Key → α) (xs : List Key)
    (s : CacheState α) : List α × CacheState α :=
  runImperativeAux cap f xs s []

def clearImperative (s : CacheState α) : CacheState α := Id.run do
  let mut state := s
  state := { state with entries := [] }
  state := { state with hits := 0 }
  state := { state with misses := 0 }
  return state

def benchmark_lru_cacheImperative (arg : MaxArg α := .integer 128)
    (typed : Bool := false) : Except String (Decoration α) := Id.run do
  match arg with
  | .integer n =>
      let mut size := n
      if size < 0 then
        size := 0
      return .ok (.decorator ⟨some size.toNat, typed⟩)
  | .none => return .ok (.decorator ⟨none, typed⟩)
  | .callable f => return .ok (.wrapped (decorate ⟨some 128, typed⟩ f))
  | .invalid => return .error typeError

def benchmarkRunImperative (arg : MaxArg α) (typed : Bool) (f : Key → α)
    (xs : List Key) : Except String (List α × CacheState α) := Id.run do
  match benchmark_lru_cacheImperative arg typed with
  | .error e => return .error e
  | .ok d =>
      let w := instantiate d f
      let result := runImperative w.config.maxsize w.userFunction xs w.state
      return .ok result

-- Imperative unit tests and bounded cross-implementation tests.
example : runImperative (some 2) timesTen basicInputs {} = basicRun := by native_decide
example : runImperative none List.sum [[1, 2], [1, 2], [2, 3], [2, 3]] {} = addRun := by native_decide
example : runImperative (some 0) List.prod [[1, 2], [1, 2], [2, 3]] {} = mulRun := by native_decide
example : cache_info (some 2) (clearImperative basicRun.2) = ⟨0, 0, some 2, 0⟩ := by native_decide
example : allScenarios (fun cap f xs => runImperative cap f xs {} == run cap f xs {}) = true := by native_decide
example : (sampleArgs.all fun a => [false, true].all fun t => sampleFunctions.all fun f =>
    (traces 4).all fun xs =>
      runView (benchmarkRunImperative a t f xs) == runView (benchmarkRun a t f xs)) = true := by native_decide
#eval cache_info (some 2) (runImperative (some 2) timesTen basicInputs {}).2

/-! ## Kernel-checked functional/imperative equivalence -/

theorem step_equivalence_thm (cap : Option Nat) (f : Key → α) (k : Key) (s : CacheState α) :
    step cap f k s = stepImperative cap f k s := by
  cases cap with
  | none => cases h : lookup k s.entries <;> simp [step, stepImperative, h]
  | some n =>
      cases n with
      | zero => rfl
      | succ n => cases h : lookup k s.entries <;> simp [step, stepImperative, h]

private theorem imperative_loop_cons (cap : Option Nat) (f : Key → α) (k : Key)
    (xs : List Key) (s : CacheState α) (acc : List α) :
    runImperativeAux cap f (k :: xs) s acc =
      runImperativeAux cap f xs (stepImperative cap f k s).2
        (acc ++ [(stepImperative cap f k s).1]) := by
  simp [runImperativeAux]

private theorem imperative_loop_invariant (cap : Option Nat) (f : Key → α)
    (xs : List Key) (s : CacheState α) (acc : List α) :
    runImperativeAux cap f xs s acc = (acc ++ (run cap f xs s).1, (run cap f xs s).2) := by
  induction xs generalizing s acc with
  | nil => simp [runImperativeAux, run]
  | cons k xs ih =>
      rw [imperative_loop_cons, ih, ← step_equivalence_thm]
      simp [run, List.append_assoc]

theorem functional_imperative_thm (cap : Option Nat) (f : Key → α)
    (xs : List Key) (s : CacheState α) :
    run cap f xs s = runImperative cap f xs s := by
  simp [runImperative, imperative_loop_invariant]

theorem clear_equivalence_thm (s : CacheState α) : cache_clear s = clearImperative s := rfl

theorem decorator_equivalence_thm (arg : MaxArg α) (typed : Bool) :
    benchmark_lru_cache arg typed = benchmark_lru_cacheImperative arg typed := by
  cases arg with
  | integer n =>
      by_cases hn : n < 0
      · have hz : n.toNat = 0 := by omega
        simp [benchmark_lru_cache, benchmark_lru_cacheImperative, lru_cache, Except.map, hn, hz]
      · simp [benchmark_lru_cache, benchmark_lru_cacheImperative, lru_cache, Except.map, hn]
  | none => rfl
  | callable f => rfl
  | invalid => rfl

/-- Equality includes outputs, complete cache state, statistics, and errors. -/
theorem equivalence_thm (arg : MaxArg α) (typed : Bool) (f : Key → α) (xs : List Key) :
    benchmarkRun arg typed f xs = benchmarkRunImperative arg typed f xs := by
  unfold benchmarkRun benchmarkRunImperative
  rw [← decorator_equivalence_thm]
  cases h : benchmark_lru_cache arg typed with
  | error e => rfl
  | ok d => simp [functional_imperative_thm]

end FunctoolsLRU
end Agent
