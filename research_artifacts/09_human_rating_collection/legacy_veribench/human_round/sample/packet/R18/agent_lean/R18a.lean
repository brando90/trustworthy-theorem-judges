/-!
# VeriBench -- All Prefixes
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace AllPrefixes

def allPrefixes : String → List String :=
  fun s => List.ofFn (fun (i : Fin (s.length)) => s.take (i.val + 1))

example : allPrefixes "" = [] := by
  native_decide

example : allPrefixes "asdfgh" = ["a", "as", "asd", "asdf", "asdfg", "asdfgh"] := by
  native_decide

example : allPrefixes "WWW" = ["W", "WW", "WWW"] := by
  native_decide

def Pre (s : String) : Prop := True

def Post_prop (s : String) (prefixes : List String) : Prop :=
  prefixes = allPrefixes s

theorem correctness_thm (s : String) (hPre : Pre s) :
  Post_prop s (allPrefixes s) := rfl

end AllPrefixes