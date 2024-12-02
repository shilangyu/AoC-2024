-- Standard definition of the absolute value
def Nat.abs (x y : Nat) := if x > y then x - y else y - x
-- Alternative definition using the fact that subtraction is saturated for natural numbers, that is, x - y = 0 if x ≤ y
def Nat.dist (x y : Nat) := (x - y) + (y - x)

-- We prove that the two definitions are equivalent
theorem abs_eq_dist : Nat.abs = Nat.dist :=
  by
    -- We prove the equality by extensionality (axiom in Lean I think?)
    funext x y
    unfold Nat.abs Nat.dist
    split -- consider the two cases x > y and ¬(x > y)
    · case _ h =>
      have h : (y <= x) := Nat.le_of_succ_le h
      simp
      exact Nat.sub_eq_zero_of_le h
    · case _ h =>
      simp at *
      exact Nat.sub_eq_zero_of_le h

-- Counting the number of elements in a list is equivalent to the length of a list filtered by that number
theorem count_eq_length_filter (l : List Nat) (x : Nat) : l.count x = (l.filter (Eq x)).length :=
  by
    induction l with
    | nil =>
      simp
    | cons hd tl ih =>
      -- We consider the two cases hd = x and hd ≠ x
      by_cases h : x = hd
      rw [h] at ih
      all_goals { simp [h]; exact ih }
