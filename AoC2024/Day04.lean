import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith


-- A pattern being inside of a list is equivalent to the reverse of the pattern being inside of the reverse of the list
theorem infix_iff_rev_infix (p s : List α): p <:+: s ↔ p.reverse <:+: s.reverse := by
  unfold List.IsInfix
  apply Iff.intro <;> intro h
  · let ⟨s1, t1, h⟩ := h
    exists t1.reverse, s1.reverse
    repeat rw [← List.reverse_append]
    rw [← List.append_assoc, h]
  · let ⟨s1, t1, h⟩ := h
    have p : (s1 ++ p.reverse ++ t1).reverse = s.reverse.reverse := by
      rw [← h]
    simp at p
    rw [← List.append_assoc] at p
    exists t1.reverse, s1.reverse

-- This means to find XMAS backwards, we can just look for SAMX forwards
lemma xmas_smax (str : List Char) :
  "XMAS".toList <:+: str.reverse ↔ "SAMX".toList <:+: str := by
  rw [infix_iff_rev_infix, List.reverse_reverse]
  rfl
