import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith

inductive Cell where
  | Empty
  | Obstruction

inductive Direction where
  | Up
  | Down
  | Left
  | Right

def Direction.delta
  | Direction.Up => (0, -1)
  | Direction.Down => (0, 1)
  | Direction.Left => (-1, 0)
  | Direction.Right => (1, 0)

def Direction.rightTurn
  | Direction.Up => Direction.Right
  | Direction.Right => Direction.Down
  | Direction.Down => Direction.Left
  | Direction.Left => Direction.Up


structure Map (n : Nat) where
  data : Vector (Vector Cell n) n
  position : Fin n × Fin n
  direction : Direction

instance {n} : ToString (Map n) where
  toString m := Id.run do
    let mut result := ""
    let (x, y) := m.position
    for j in [:n] do
      for i in [:n] do
        if i == x && j == y then
          result := result ++ match m.direction with
            | Direction.Up => "^"
            | Direction.Down => "v"
            | Direction.Left => "<"
            | Direction.Right => ">"
        else if h : i < n ∧ j < n then
          result := result ++ match (m.data.get (Fin.mk j h.right)).get (Fin.mk i h.left) with
            | Cell.Empty => "."
            | Cell.Obstruction => "#"
      result := result ++ "\n"
    result

def Map.move (m : Map n) : Option (Map n) := do
  let (x, y) <- do
    let (i, j) := m.position
    let (di, dj) := m.direction.delta
    let i' <- (i + di).toNat'
    let j' <- (j + dj).toNat'

    if h : i' < n ∧ j' < n
    then some (Fin.mk i' h.left, Fin.mk j' h.right)
    else none

  match (m.data.get y).get x with
  | .Empty => some { m with position := (x, y) }
  | .Obstruction => some { m with direction := m.direction.rightTurn }

-- Apply move k times
def Map.move_k {n} (m : Map n) (k : Nat) : Option (Map n) := match m.move with
  | none => none
  | some m' => match k with
    | 0 => some m
    | k+1 => m'.move_k k

-- Modulo 4 has only 4 different values
lemma Nat.mod_four_cases (n : Nat) : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
  match h : n % 4 with
  | 0 | 1 | 2 | 3 => simp
  | k+4 => linarith [@Nat.mod_lt n 4 (by simp)]


lemma Nat.mod_exists_mul (n : Nat) : n % p = k → ∃ s, p * s + k = n := by
  intro h
  use n / p
  nth_rw 2 [<-Nat.mod_add_div n p]
  rw [h, Nat.add_comm]


lemma Option.isSome_eq_true (o o' : Option α) : o.isSome = true → o = o' → o'.isSome = true := by
  intro h heq
  cases o
  case none => contradiction
  case some => subst heq; rfl

lemma Map.move_exists_stuck : ∃ n, ∃ m: Map n, ∀ k, (m.move_k k).isSome = true := by
  /-
    .#.
    #^#
    .#.
  -/
  use 3
  let m : Map 3 := { data := #v[#v[Cell.Empty, .Obstruction, .Empty], #v[.Obstruction, .Empty, .Obstruction], #v[.Empty, .Obstruction, .Empty]], position := (1, 1), direction := Direction.Up }
  use m

  intro k

  -- we consider each of the k % 4 cases
  rcases Nat.mod_four_cases k with (hk | hk | hk | hk)
  on_goal 1 => let p := 0
  on_goal 2 => let p := 1
  on_goal 3 => let p := 2
  on_goal 4 => let p := 3
  all_goals {
    have ⟨ s, keq ⟩ := Nat.mod_exists_mul k hk
    -- we know that there is a cycle for each p
    have hcycle : ∀ s, m.move_k p = m.move_k (4*s + p) := by
      intro s
      induction s <;> trivial
    have hcycle := hcycle s
    rw [keq] at hcycle
    -- since there is a cycle we will keep coming back to the same state
    apply Option.isSome_eq_true
    · show (m.move_k p).isSome = true
      simp [Map.move_k]
    · assumption
  }
