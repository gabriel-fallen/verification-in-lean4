
/-
Famous leftpad function and proofs.
Copied from https://github.com/hwayne/lets-prove-leftpad/tree/master/lean4
which was contributed by me.
-/

def leftpad (n : Nat) (a : Char) (s : String) : String :=
  "".pushn a (n - s.length) ++ s

#eval leftpad 5 'b' "ac"


-- Exercises

-- Length of the result

theorem leftpad_length (n : Nat) (a : Char) (s : String) :
    (leftpad n a s).length = max n (s.length) := by
  sorry


-- Functional correctness (the characters are the right ones)

theorem leftpad_prefix (n : Nat) (a : Char) (s : String) :
    (List.replicate (n - s.length) a).isPrefixOf (leftpad n a s).data := by
  sorry

theorem leftpad_suffix (n : Nat) (a : Char) (s : String) :
    s.data.isSuffixOf (leftpad n a s).data := by
  sorry
