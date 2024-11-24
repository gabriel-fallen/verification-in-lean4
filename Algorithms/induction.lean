
/-
Simple exercises on generalizing induction hypothesis copied from
https://jamesrwilcox.com/InductionExercises.html
-/


-- Reverse

def rev : List α → List α
  | []      => []
  | x :: xs => rev xs ++ [x]

#eval rev [1, 2, 3]


theorem rev_append (xs ys : List α) : rev (xs ++ ys) = rev ys ++ rev xs := by
  induction xs with
  | nil => simp [rev]
  | cons hd tl ih =>
    simp [rev]
    rw [ih]
    apply (List.append_assoc)

theorem rev_rev_id (l : List α) : rev (rev l) = l := by
  induction l with
  | nil => simp [rev]
  | cons hd tl ih =>
    simp [rev]
    rw [rev_append (rev tl) [hd], ih]
    simp [rev]


def rev_tail_aux (acc : List α) : List α → List α
  | [] => acc
  | x :: xs => rev_tail_aux (x :: acc) xs

abbrev rev_tail {α : Type u} := @rev_tail_aux α []

#eval rev_tail [1, 2, 3]


theorem rev_tail_aux_rev (acc l : List α) : rev_tail_aux acc l = rev l ++ acc := by
  induction l generalizing acc with
  | nil => simp [rev, rev_tail_aux]
  | cons x xs ih =>
    simp [rev, rev_tail_aux]
    rw [ih]

theorem rev_tail_rev (l : List α) : rev_tail l = rev l := by
  simp [rev_tail]
  rw [rev_tail_aux_rev [] l, List.append_nil]



-- Sum

def sum : List Nat → Nat
  | []      => 0
  | x :: xs => x + sum xs

#eval sum [0, 2, 3]


def sum_tail_aux (acc : Nat) : List Nat → Nat
  | []      => acc
  | x :: xs => sum_tail_aux (acc + x) xs

abbrev sum_tail := sum_tail_aux 0

#eval sum_tail [0, 2, 3]


theorem add_left_sum_tail_aux (x acc : Nat) (xs : List Nat) : x + sum_tail_aux acc xs = sum_tail_aux (x + acc) xs := by
  induction xs generalizing x acc with
  | nil => simp [sum_tail_aux]
  | cons h tl ih =>
    simp [sum_tail_aux]
    rw [Nat.add_comm acc h, (ih h acc).symm]
    have : sum_tail_aux (x + acc + h) tl = x + (h + sum_tail_aux acc tl) :=
      calc
        sum_tail_aux (x + acc + h) tl = sum_tail_aux ((x + h) + acc) tl := by rw [Nat.add_assoc x acc h, Nat.add_comm acc h, Nat.add_assoc x h acc]
        _ = x + h + sum_tail_aux acc tl := by rw [ih]
        _ = x + (h + sum_tail_aux acc tl) := by omega
    exact this.symm

theorem sum_tail_aux_sum : ∀ acc l, sum_tail_aux acc l = acc + sum l := by
  intros acc l
  induction l with
  | nil => simp  [sum_tail_aux, sum]
  | cons x xs ih =>
    simp  [sum_tail_aux, sum]
    rw [Nat.add_comm acc x, (add_left_sum_tail_aux x acc xs).symm, ih]
    omega

theorem sum_tail_correct (l : List Nat) : sum_tail l = sum l := by
  unfold sum_tail
  induction l with
  | nil => simp [sum_tail_aux, sum]
  | cons x xs ih =>
    simp [sum_tail_aux, sum, sum_tail_aux_sum]
