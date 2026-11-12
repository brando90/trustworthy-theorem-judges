import Mathlib

namespace ShellQuote

/-! ## Implementation

A faithful port of Python's `shlex.quote`.  Since the Lean function is typed
`String → String`, the Python pre-condition `isinstance(s, str)` is discharged by
typing, hence `Pre` is `True`.  All the real work is done on `List Char`, which
keeps the proofs free of `String` internals. -/

/-- The POSIX-safe character set: `[A-Za-z0-9]` together with `_@%+=:,./-`. -/
def isSafeChar (c : Char) : Bool :=
  c.isAlphanum || ['_', '@', '%', '+', '=', ':', ',', '.', '/', '-'].contains c

/-- `'` is replaced by `'"'"`; every other character is kept as is. -/
def escapeCharList (c : Char) : List Char :=
  if c = '\'' then ['\'', '"', '\'', '"', '\''] else [c]

/-- Python's `s.replace("'", "'\"'\"'")`. -/
def escapeAll : List Char → List Char
  | []      => []
  | c :: cs => escapeCharList c ++ escapeAll cs

/-- The core of `shlex.quote`, on character lists. -/
def quoteChars (cs : List Char) : List Char :=
  if cs.isEmpty then ['\'', '\'']
  else if cs.all isSafeChar then cs
  else '\'' :: (escapeAll cs ++ ['\''])

/-- `benchmark_quote` / `quote`. -/
def quote (s : String) : String := ⟨quoteChars s.data⟩

/-! ## Tests (from `check`) -/

example : quoteChars [] = ['\'', '\''] := by native_decide
example : quoteChars ['a', 'b', 'c'] = ['a', 'b', 'c'] := by native_decide
example : quoteChars ['a', ' ', 'b', ' ', 'c'] = ['\'', 'a', ' ', 'b', ' ', 'c', '\''] := by
  native_decide
example : quoteChars ['a', '\'', 'b']
    = ['\'', 'a', '\'', '"', '\'', '"', '\'', 'b', '\''] := by native_decide

example : quote "" = "''" := by native_decide
example : quote "abc" = "abc" := by native_decide
example : quote "a b c" = "'a b c'" := by native_decide
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide

/-! ## Auxiliary lemmas -/

theorem isEmpty_eq_false_of_ne_nil {cs : List Char} (h : cs ≠ []) : ¬ (cs.isEmpty = true) := by
  cases cs with
  | nil => exact absurd rfl h
  | cons a t => simp

theorem mk_data_eq (s : String) : (⟨s.data⟩ : String) = s := rfl

/-- A quote-free list is left untouched by the escaping pass. -/
theorem escapeAll_of_no_quote (cs : List Char) (h : ∀ c ∈ cs, c ≠ '\'') :
    escapeAll cs = cs := by
  induction cs with
  | nil => rfl
  | cons a t ih =>
    have ha : a ≠ '\'' := h a (by simp)
    have ht : ∀ c ∈ t, c ≠ '\'' := fun c hc => h c (by simp [hc])
    simp [escapeAll, escapeCharList, ha, ih ht]

/-! ## Behaviour of `quoteChars` -/

theorem quoteChars_nil : quoteChars [] = ['\'', '\''] := rfl

theorem quoteChars_safe (cs : List Char) (h1 : cs ≠ []) (h2 : cs.all isSafeChar = true) :
    quoteChars cs = cs := by
  have hne : ¬ (cs.isEmpty = true) := isEmpty_eq_false_of_ne_nil h1
  unfold quoteChars
  rw [if_neg hne, if_pos h2]

theorem quoteChars_unsafe (cs : List Char) (h1 : cs ≠ []) (h2 : cs.all isSafeChar = false) :
    quoteChars cs = '\'' :: (escapeAll cs ++ ['\'']) := by
  have hne : ¬ (cs.isEmpty = true) := isEmpty_eq_false_of_ne_nil h1
  have h2' : ¬ (cs.all isSafeChar = true) := by simp [h2]
  unfold quoteChars
  rw [if_neg hne, if_neg h2']

/-- The result of quoting is never empty. -/
theorem quoteChars_ne_nil (cs : List Char) : quoteChars cs ≠ [] := by
  unfold quoteChars
  split
  · simp
  · rename_i h
    split
    · intro hc
      apply h
      rw [hc]
    · simp

/-! ## Behaviour of `quote` -/

theorem quote_data_ne_nil (s : String) : (quote s).data ≠ [] := quoteChars_ne_nil s.data

theorem quote_ne_empty (s : String) : quote s ≠ "" := by native_decide

theorem quote_empty_data (s : String) (h : s.data = []) : (quote s).data = ['\'', '\''] := by
  have : quoteChars s.data = ['\'', '\''] := by rw [h]
  exact this

theorem quote_safe (s : String) (h1 : s.data ≠ []) (h2 : s.data.all isSafeChar = true) :
    quote s = s := by
  show (⟨quoteChars s.data⟩ : String) = s
  rw [quoteChars_safe s.data h1 h2]

theorem quote_unsafe (s : String) (h1 : s.data ≠ []) (h2 : s.data.all isSafeChar = false) :
    (quote s).data = '\'' :: (escapeAll s.data ++ ['\'']) :=
  quoteChars_unsafe s.data h1 h2

/-! ## Specification -/

/-- `pre_quote`: the input must be a string — automatic from the Lean type. -/
def Pre (_s : String) : Prop := True

def Post (s : String) : Prop :=
  (quote s).data ≠ [] ∧
  (s.data = [] → (quote s).data = ['\'', '\'']) ∧
  (s.data ≠ [] → s.data.all isSafeChar = true → quote s = s) ∧
  (s.data ≠ [] → s.data.all isSafeChar = false →
      (quote s).data = '\'' :: (escapeAll s.data ++ ['\'']))

theorem correctness (s : String) : Pre s → Post s := by
  intro _
  exact ⟨quote_data_ne_nil s,
         fun h => quote_empty_data s h,
         fun h1 h2 => quote_safe s h1 h2,
         fun h1 h2 => quote_unsafe s h1 h2⟩

end ShellQuote