import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith

inductive SafetyDirection where
  | Increasing
  | Decreasing

-- The inductive definition of what it means to be a safe list
inductive Safe {d : SafetyDirection} : List Int → Prop
  | cons {a b : Int}
    (eq : l = (a::b::tail))
    (prop : match d with
    | .Increasing => a+1 = b ∨ a+2 = b ∨ a+3 = b
    | .Decreasing => a-1 = b ∨ a-2 = b ∨ a-3 = b)
    (safe_rest : @Safe d (b::tail)) : Safe l
  | singleton {a : Int} : Safe [a]
  | nil : Safe []

-- It is safe if there exists a direction
def isSafe (l : List Int) : Prop := ∃ d, @Safe d l

-- We can prove that a list is safe by applying the cons rule and ending with a singleton
example : isSafe [1, 2, 3, 5, 8] := by
  exists SafetyDirection.Increasing
  repeat
    apply Safe.cons
    rfl
    simp
  apply Safe.singleton


-- If a list is safe, its tail is also safe
lemma is_safe_induct : isSafe (a :: l) → isSafe l := by
  intro h
  let ⟨ dir, safe ⟩ := h
  cases l with
  | nil =>
    apply Exists.intro
    apply Safe.nil
    all_goals {exact SafetyDirection.Increasing}
  | cons b l =>
    cases safe
    simp_all
    exists dir

-- If a list is safe, the last element is at most bigger than the first element by 3 times the length of the list and is at least smaller than the first element by 3 times the length of the list
theorem safe_bounds (l : List Int) (h : l ≠ []) :
  isSafe l →
  l.head h = s →
  l.getLast h = e →
  e ≤ s + 3 * l.length ∧ e ≥ s - 3 * l.length := by
  intro safe
  revert s e h
  let ⟨ dir, safe ⟩ := safe
  induction safe with
  -- not possible, we assumed the list is not empty
  | nil => intros; contradiction
  | singleton =>
    intro _ _ _ start last
    simp at *
    -- start and last are the same
    rw [← start, last]
    apply And.intro
      <;> apply Int.le_add_of_nonneg_right <;> simp
  | @cons lt tail a b eq prop safe_rest ih =>
    intro s e h start last
    simp [*] at *
    rw [← start] at *
    clear s start eq
    have t := ih (is_safe_induct safe)
    have q : ((b :: tail).getLast (by simp) = e) := by
      have u := @List.getLast_cons Int a (b::tail) (by simp)
      rw [← u]
      assumption
    rw [q] at t
    cases dir <;> simp at * <;>
    · apply Or.by_cases prop <;> intro p
      on_goal 2 => apply Or.by_cases p <;> intro b

      all_goals {
        try rw [← b] at t
        try rw [← p] at t
        apply And.intro <;>
          linarith [And.left t, And.right t]
      }
