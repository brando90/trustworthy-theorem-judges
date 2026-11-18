import Mathlib
namespace Agent

/-!
# Safe template rendering

A character-list model of Python's `html.escape(str(v), quote=True)` and ordered,
non-overlapping `str.replace`. An ordered context stores the results of Python's
`str` conversion; thus arbitrary Python values are represented by their string
observations, without making assumptions about those observations.

The source template really has THREE braces, whereas the replacement keys have
TWO. Consequently one brace on each side normally remains. Replacement is
sequential: a username placeholder introduced by the comment is also replaced,
including placeholders spanning the remaining braces and the inserted comment.
-/

namespace CrossSiteScriptingSafe

abbrev Context := List (String × String)

structure WebApplication where
  deriving Repr, DecidableEq

structure Response where
  rendered_html : String
  vulnerable : Bool
  deriving Repr, DecidableEq

/-- Python's five escapes, including its spelling of the apostrophe entity. -/
def escapeChar (c : Char) : List Char :=
  if c = '&' then "&amp;".toList
  else if c = '<' then "&lt;".toList
  else if c = '>' then "&gt;".toList
  else if c = '"' then "&quot;".toList
  else if c = '\'' then "&#x27;".toList
  else [c]

def escapeChars (s : List Char) : List Char := s.flatMap escapeChar

def htmlEscape (s : String) : String := String.mk (escapeChars s.toList)

/-- Left-to-right, non-overlapping replacement for a nonempty pattern.
The replacement itself is not scanned during the same pass. -/
def replaceChars (first : Char) (rest replacement : List Char) : List Char → List Char
  | [] => []
  | c :: cs =>
      if c = first ∧ rest.isPrefixOf cs then
        replacement ++ replaceChars first rest replacement (cs.drop rest.length)
      else
        c :: replaceChars first rest replacement cs
termination_by xs => xs.length
 decreasing_by
  · simp only [List.length_drop, List.length_cons]
    omega
  · simp

/-- Every template placeholder is nonempty, even for the empty key. -/
def replaceKey (template key value : String) : String :=
  String.mk (replaceChars '{' (('{' :: key.toList) ++ "}}".toList)
    value.toList template.toList)

def WebApplication.safe_render_template (_app : WebApplication)
    (template : String) (context : Context) : String :=
  let safeCtx := context.map (fun (k, v) => (k, htmlEscape v))
  safeCtx.foldl (fun t (k, v) => replaceKey t k v) template

def commentTemplate : String :=
  "\n    <div class=\"comment\">\n        <p>{{{comment_text}}}</p>\n        <small>Posted by: {{{username}}}</small>\n    </div>\n    "

def safe_xss_handling (app : WebApplication) (user_input : String) : Response :=
  { rendered_html := app.safe_render_template commentTemplate
      [("comment_text", user_input), ("username", "user123")]
    vulnerable := false }

/-- Case-insensitive recognition of a script opening prefix at this position. -/
def scriptAt : List Char → Bool
  | '<' :: cs => "script".toList.isPrefixOf (cs.map Char.toLower)
  | _ => false

def hasScript : List Char → Bool
  | [] => false
  | c :: cs => scriptAt (c :: cs) || hasScript cs

def containsText (needle text : String) : Bool :=
  text.toList.tails.any (fun suffix => needle.toList.isPrefixOf suffix)

def check (candidate : WebApplication → String → Response) : Bool :=
  let out := candidate {} "<script>alert('XSS')</script>"
  !out.vulnerable && !containsText "<script" out.rendered_html.toLower &&
    containsText "&lt;script" out.rendered_html.toLower

-- Fixed tests: Python's check, entities, unchanged text, and sequential passes.
example : htmlEscape "&<>\"'" = "&amp;&lt;&gt;&quot;&#x27;" := by native_decide
example : htmlEscape "already &lt; λ🙂" = "already &amp;lt; λ🙂" := by native_decide
example : replaceKey "{{x}}{{x}}" "x" "{{x}}!" = "{{x}}!{{x}}!" := by native_decide
example : check safe_xss_handling = true := by native_decide
example : (safe_xss_handling {} "Hi").rendered_html =
  "\n    <div class=\"comment\">\n        <p>{Hi}</p>\n        <small>Posted by: {user123}</small>\n    </div>\n    " := by native_decide
example : (safe_xss_handling {} "{{username}}").rendered_html =
  (safe_xss_handling {} "user123").rendered_html := by native_decide
-- Replacement order and the otherwise easy-to-miss brace-boundary behavior.
example : (WebApplication.mk).safe_render_template "{{a}}"
    [("a", "{{b}}"), ("b", "<x>")] = "&lt;x&gt;" := by native_decide
example : (WebApplication.mk).safe_render_template "{{a}}"
    [("b", "<x>"), ("a", "{{b}}")] = "{{b}}" := by native_decide
example : containsText "<p>user123</p>"
    (safe_xss_handling {} "{username}").rendered_html = true := by native_decide
example : containsText "<p>user123}</p>"
    (safe_xss_handling {} "{username}}").rendered_html = true := by native_decide
#eval htmlEscape "<script>alert('XSS')</script>"
#eval safe_xss_handling {} "<script>alert('XSS')</script>"
#eval check safe_xss_handling

/-- Python accepts every string; there is no restriction on the user input. -/
def Pre (_app : WebApplication) (_user_input : String) : Prop := True


/-- No unescaped HTML delimiter or quote survives in a context value. -/
def escaping_prop (s : String) : Prop :=
  ∀ c ∈ (htmlEscape s).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\''

lemma escapeChar_safe (c d : Char) (h : d ∈ escapeChar c) :
    d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' ∧ d ≠ '\'' := by
  unfold escapeChar at h
  split_ifs at h <;> simp_all [String.toList] <;> aesop

theorem escaping_thm (s : String) : escaping_prop s := by
  intro c hc
  change c ∈ escapeChars s.toList at hc
  obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hc
  exact escapeChar_safe d c hd

/-- The fixed template permits only these prefixes after a raw `<`.
This invariant excludes script tags even after case folding. -/
def tagHead : List Char → Bool
  | [] => false
  | c :: cs => c == '/' || c == 'd' || c == 'p' ||
      (c == 's' && cs.head? == some 'm')

def safeHead (c : Char) (cs : List Char) : Bool := c != '<' || tagHead cs

def safeTags : List Char → Bool
  | [] => true
  | c :: cs => safeHead c cs && safeTags cs

lemma safeTags_tail {c : Char} {cs : List Char} (h : safeTags (c :: cs) = true) :
    safeTags cs = true := (Bool.and_eq_true_iff.mp h).2

lemma safeTags_drop (xs : List Char) (n : Nat) (h : safeTags xs = true) :
    safeTags (xs.drop n) = true := by
  induction n generalizing xs with
  | zero => simpa using h
  | succ n ih =>
      cases xs with
      | nil => rfl
      | cons c cs => exact ih cs (safeTags_tail h)

lemma safeTags_prepend (xs ys : List Char) (hx : ∀ c ∈ xs, c ≠ '<')
    (hy : safeTags ys = true) : safeTags (xs ++ ys) = true := by
  induction xs with
  | nil => exact hy
  | cons c cs ih =>
      simp only [List.cons_append, safeTags, Bool.and_eq_true]
      constructor
      · simp [safeHead, hx c (by simp)]
      · exact ih (fun d hd => hx d (by simp [hd]))


lemma tagHead_replace (rest replacement xs : List Char) (h : tagHead xs = true) :
    tagHead (replaceChars '{' rest replacement xs) = true := by
  cases xs with
  | nil => simp [tagHead] at h
  | cons c cs =>
      simp only [tagHead, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ((rfl | rfl) | rfl) | ⟨rfl, hm⟩
      · simp [replaceChars, tagHead]
      · simp [replaceChars, tagHead]
      · simp [replaceChars, tagHead]
      · cases cs with
        | nil => simp at hm
        | cons d ds =>
            simp only [List.head?_cons, Option.some.injEq] at hm
            subst d
            simp [replaceChars, tagHead]

/-- Replacing a brace-led placeholder by text with no raw `<` preserves
all the template's permitted tag prefixes. No assumption on the key is needed. -/
lemma safeTags_replace (rest replacement xs : List Char)
    (hr : ∀ c ∈ replacement, c ≠ '<') (hs : safeTags xs = true) :
    safeTags (replaceChars '{' rest replacement xs) = true := by
  match xs with
  | [] => simp [replaceChars, safeTags]
  | c :: cs =>
      rw [replaceChars]
      split
      · apply safeTags_prepend _ _ hr
        exact safeTags_replace rest replacement (cs.drop rest.length) hr
          (safeTags_drop cs rest.length (safeTags_tail hs))
      · simp only [safeTags, Bool.and_eq_true] at hs ⊢
        refine ⟨?_, safeTags_replace rest replacement cs hr hs.2⟩
        rcases Bool.or_eq_true_iff.mp hs.1 with hc | ht
        · exact Bool.or_eq_true_iff.mpr (Or.inl hc)
        · exact Bool.or_eq_true_iff.mpr (Or.inr (tagHead_replace rest replacement cs ht))
termination_by xs.length
 decreasing_by all_goals (simp_wf <;> omega)

lemma render_safeTags (app : WebApplication) (template : String) (ctx : Context)
    (h : safeTags template.toList = true) :
    safeTags (app.safe_render_template template ctx).toList = true := by
  induction ctx generalizing template with
  | nil => exact h
  | cons entry ctx ih =>
      obtain ⟨k, v⟩ := entry
      change safeTags (app.safe_render_template (replaceKey template k (htmlEscape v)) ctx).toList = true
      apply ih
      apply safeTags_replace
      · exact fun c hc => (escaping_thm v c hc).1
      · exact h

/-- Raw markup in the result can only have a prefix allowed by the fixed template. -/
def tag_safety_prop (app : WebApplication) (s : String) : Prop :=
  safeTags (safe_xss_handling app s).rendered_html.toList = true

theorem tag_safety_thm (app : WebApplication) (s : String) : tag_safety_prop app s := by
  exact render_safeTags app commentTemplate _ (by decide)

lemma tagHead_not_script (xs : List Char) (h : tagHead xs = true) :
    "script".toList.isPrefixOf (xs.map Char.toLower) = false := by
  cases xs with
  | nil => simp [tagHead] at h
  | cons c cs =>
      simp only [tagHead, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ((rfl | rfl) | rfl) | ⟨rfl, hm⟩
      · simp [List.isPrefixOf, Char.toLower]
      · simp [List.isPrefixOf, Char.toLower]
      · simp [List.isPrefixOf, Char.toLower]
      · cases cs with
        | nil => simp at hm
        | cons d ds =>
            simp only [List.head?_cons, Option.some.injEq] at hm
            subst d
            simp [List.isPrefixOf, Char.toLower]

lemma safeTags_no_script (xs : List Char) (h : safeTags xs = true) :
    hasScript xs = false := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp only [safeTags, Bool.and_eq_true] at h
      rw [hasScript, ih h.2, Bool.or_false]
      by_cases hc : c = '<'
      · subst c
        exact tagHead_not_script cs (by simpa [safeHead] using h.1)
      · simp [scriptAt, hc]

/-- Lowercasing cannot create a less-than delimiter. -/
lemma lower_lt_iff (c : Char) : c.toLower = '<' ↔ c = '<' := by
  unfold Char.toLower
  dsimp only
  split_ifs with h
  · constructor
    · intro hc
      have hn := congrArg Char.toNat hc
      rw [Char.toNat_ofNat] at hn
      change (if (c.toNat + 32).isValidChar then c.toNat + 32 else 0) = 60 at hn
      split_ifs at hn; omega
    · intro hc
      subst c
      have hbad : ¬ ('<'.toNat ≥ 65 ∧ '<'.toNat ≤ 90) := by decide
      exact False.elim (hbad h)
  · rfl

lemma scriptAt_eq_search (xs : List Char) :
    scriptAt xs = "<script".toList.isPrefixOf (xs.map Char.toLower) := by
  cases xs with
  | nil => rfl
  | cons c cs =>
      by_cases hc : c = '<'
      · subst c; rfl
      · have hl : c.toLower ≠ '<' := fun he => hc ((lower_lt_iff c).mp he)
        simp [scriptAt, hc, List.isPrefixOf, Ne.symm hl]

lemma hasScript_eq_search (xs : List Char) :
    hasScript xs = (xs.map Char.toLower).tails.any
      (fun suffix => "<script".toList.isPrefixOf suffix) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp only [hasScript, List.map_cons, List.tails_cons, List.any_cons,
        scriptAt_eq_search, ih]

lemma hasScript_string (s : String) :
    hasScript s.toList = containsText "<script" s.toLower := by
  rw [hasScript_eq_search]
  simp only [containsText, String.toLower, String.map_eq, String.toList]

/-- No case-insensitive script opening prefix is present anywhere in the output. -/
def no_script_prop (app : WebApplication) (s : String) : Prop :=
  containsText "<script" (safe_xss_handling app s).rendered_html.toLower = false

theorem no_script_thm (app : WebApplication) (s : String) : no_script_prop app s := by
  unfold no_script_prop
  rw [← hasScript_string]
  exact safeTags_no_script _ (tag_safety_thm app s)


/-- The result reports the literal Python Boolean `False`. -/
def flag_prop (app : WebApplication) (s : String) : Prop :=
  (safe_xss_handling app s).vulnerable = false

theorem flag_thm (app : WebApplication) (s : String) : flag_prop app s := by
  rfl

/-- Exact sequential rendering, not a simultaneous substitution. In particular,
this specifies how braces in the input may participate in the second pass. -/
def rendering_prop (app : WebApplication) (s : String) : Prop :=
  (safe_xss_handling app s).rendered_html =
    replaceKey (replaceKey commentTemplate "comment_text" (htmlEscape s))
      "username" "user123"

theorem rendering_thm (app : WebApplication) (s : String) : rendering_prop app s := by
  rfl

/-- The concrete public Python check, proved by kernel reduction. -/
def public_check_prop : Prop := check safe_xss_handling = true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem public_check_thm : public_check_prop := by
  unfold public_check_prop check
  simp only [safe_xss_handling, WebApplication.safe_render_template, List.map_cons,
    List.map_nil, List.foldl_cons, List.foldl_nil]
  simp [replaceKey, replaceChars, htmlEscape, escapeChars, escapeChar,
    commentTemplate, containsText, String.toLower, String.map_eq,
    String.toList, List.tails, List.isPrefixOf, Char.toLower]

/-- The postcondition combines exact output semantics with the security claims. -/
def Post_prop (app : WebApplication) (s : String) : Prop :=
  escaping_prop s ∧ flag_prop app s ∧ rendering_prop app s ∧
    tag_safety_prop app s ∧ no_script_prop app s

/-! ## Property-based tests
Exhaustive strings of up to three tokens from an adversarial alphabet, as well
as longer attacks. Tokens include partial placeholders to exercise matches that
cross the boundaries of the inserted value. Each executable specification has
its own bounded test; these are evidence in addition to the universal proofs.
-/

def testTokens : List String :=
  ["", "a", "&", "<", ">", "\"", "'", "{", "}", "λ🙂", "<ScRiPt>",
   "{{username}}", "{username}}", "{{username}", "{{comment_text}}"]

def tokenStrings : Nat → List String
  | 0 => [""]
  | n + 1 => (tokenStrings n).flatMap (fun a => testTokens.map (fun b => a ++ b))

def testInputs : List String := tokenStrings 3 ++
  ["<script>alert('XSS')</script>", "<img src=x onerror=alert(1)>",
   "</p><SCRIPT SRC=x></SCRIPT>", "&lt;script&gt;", "{{username}}{{username}}"]

def escapingOK (s : String) : Bool :=
  (htmlEscape s).toList.all (fun c => c != '<' && c != '>' && c != '"' && c != '\'')

def flagOK (s : String) : Bool := !(safe_xss_handling {} s).vulnerable

def renderingOK (s : String) : Bool :=
  (safe_xss_handling {} s).rendered_html ==
    replaceKey (replaceKey commentTemplate "comment_text" (htmlEscape s)) "username" "user123"

def tagsOK (s : String) : Bool := safeTags (safe_xss_handling {} s).rendered_html.toList

def noScriptOK (s : String) : Bool :=
  !containsText "<script" (safe_xss_handling {} s).rendered_html.toLower

def postOK (s : String) : Bool :=
  escapingOK s && flagOK s && renderingOK s && tagsOK s && noScriptOK s

-- PBT for escaping_prop.
example : testInputs.all escapingOK = true := by native_decide
-- PBT for flag_prop.
example : testInputs.all flagOK = true := by native_decide
-- PBT for rendering_prop.
example : testInputs.all renderingOK = true := by native_decide
-- PBT for tag_safety_prop.
example : testInputs.all tagsOK = true := by native_decide
-- PBT for no_script_prop.
example : testInputs.all noScriptOK = true := by native_decide
-- public_check_prop has no inputs; also vary the attacks in a related check.
example : check safe_xss_handling = true ∧
    testInputs.all (fun s => flagOK s && noScriptOK s) = true := by native_decide
-- PBT for the entire Post_prop.
example : testInputs.all postOK = true := by native_decide
#eval (testInputs.length, testInputs.all postOK)

/-- Total correctness on the source program's entire string input domain. -/
theorem correctness_thm (app : WebApplication) (s : String) :
    Pre app s → Post_prop app s := by
  intro _
  exact ⟨escaping_thm s, flag_thm app s, rendering_thm app s,
    tag_safety_thm app s, no_script_thm app s⟩

/-! ## Imperative implementation -/

def WebApplication.safe_render_template_imp (_app : WebApplication)
    (template : String) (context : Context) : String := Id.run do
  let safeCtx := context.map (fun (k, v) => (k, htmlEscape v))
  let mut rendered := template
  for (k, v) in safeCtx do
    rendered := replaceKey rendered k v
  return rendered

def safe_xss_handling_imp (app : WebApplication) (s : String) : Response := Id.run do
  let mut rendered := commentTemplate
  rendered := app.safe_render_template_imp rendered
    [("comment_text", s), ("username", "user123")]
  return { rendered_html := rendered, vulnerable := false }

example : check safe_xss_handling_imp = true := by native_decide
example : testInputs.all (fun s => safe_xss_handling {} s == safe_xss_handling_imp {} s) = true := by
  native_decide
#eval safe_xss_handling_imp {} "<script>alert('XSS')</script>"
#eval check safe_xss_handling_imp

theorem renderer_equivalence_thm (app : WebApplication) (template : String) (ctx : Context) :
    app.safe_render_template template ctx = app.safe_render_template_imp template ctx := by
  simp [WebApplication.safe_render_template, WebApplication.safe_render_template_imp]

theorem equivalence_thm (app : WebApplication) (s : String) :
    safe_xss_handling app s = safe_xss_handling_imp app s := by
  simp [safe_xss_handling, safe_xss_handling_imp, renderer_equivalence_thm]

end CrossSiteScriptingSafe
end Agent
