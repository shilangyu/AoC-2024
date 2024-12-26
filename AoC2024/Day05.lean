import Mathlib.Tactic.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Finset.Basic

/-
The task defines a linear order. This means, for every X and Y, some `X|Y` is
true (from the strong connectivity property of linear orders). That means all
elements can be ordered into a list. Then, checking whether an update is correct,
it is just a matter of checking if that update is a (non-continuous) subsequence
of the list. This is O(n) rather than O(n^2) for the naive approach.
-/

/-
This works only when assuming we have a linear order. This assumption can be
easily checked: we have a linear order iff the amount of relations is equal to
∑_{i=1}^{n-1} i = n(n-1)/2 and the relations are consistent. Where `n` is the
number of elements in the order. This is true thanks to the strong connectivity
and antisymmetry property of linear orders.

This would be interesting to prove but I have no experience with combinatorics
in Lean.
-/

-- We operate on a finite subset of natural numbers (but everything holds true for any finite set)
abbrev Base := Nat
abbrev Ele := Finset Base

-- We start by defining what it means for an update to be ordered according to a linear order
inductive UpdateOrdered {order : LinearOrder Ele} : List Ele -> Prop where
  | nil : UpdateOrdered []
  | cons :
    UpdateOrdered xs ->
    (∀ y ∈ xs, order.lt x y) ->
    UpdateOrdered (x :: xs)

-- We assume there be a list which uniquely identifies a linear order
-- This can be constructed by sorting the elements.
def linearOrderList (_ : LinearOrder Ele) : List Ele :=
  -- this could be implemented by collecting all elements of Ele and sorting
  []

-- The produced list is ordered by the linear order
lemma linearOrderListInvariant (order : LinearOrder Ele) : (linearOrderList order).Pairwise order.lt := by simp [linearOrderList]

-- Being a sublist with the middle means we are a sublist without it
lemma List.sublist_middle {l1 l2 l3 l : List α} : (l1 ++ l2 ++ l3).Sublist l → (l1 ++ l3).Sublist l := by
  intro h
  trans (l1 ++ l2 ++ l3)
  · simp
  · exact h

-- Specialization of `List.sublist_middle`
lemma sublist_cons_cons : (x :: y :: zs).Sublist l → (x :: zs).Sublist l := by
  intro h
  have p : (x :: y :: zs) = ([x] ++ [y] ++ zs) := by rfl
  rw [p] at h
  exact List.sublist_middle h

-- If we have some pairwise relation and a sublist from cons, then the head is in relation with the tail
lemma List.sublist_cons_pairwise :  (h :: t).Sublist l → List.Pairwise R l → ∀ x ∈ t, R h x := by
  intro hs hp x hm
  apply @List.pairwise_iff_forall_sublist.mp hp h x

  induction t with
  | nil => contradiction
  | cons y ys ih =>
    cases hm with
    | head => trans (h :: x :: ys) <;> simp [hs]
    | tail h hm =>
      apply ih
      · exact sublist_cons_cons hs
      · assumption

-- Invariant of being a sublist of a linear order list: all next elements are larger
lemma linearOrderList_cons :
  (x :: xs).Sublist (linearOrderList order) ->
  ∀ y ∈ xs, order.lt x y := by
    induction xs with
    | nil => intros; contradiction
    | cons y ys ih =>
      intro h z hz
      cases hz with
      | head =>
        apply List.sublist_cons_pairwise
        · exact h
        · exact linearOrderListInvariant order
        · simp
      | tail _ hz => exact ih (sublist_cons_cons h) z hz


-- Main theorem: if we check whether an update is a sublist of a linear order list, then it is ordered
theorem updateOrderedSublist (update : List Ele) (order : LinearOrder Ele) :
  update.Sublist (linearOrderList order) ->
  @UpdateOrdered order update := by
    induction update with
    | nil =>
      intro h
      constructor
    | cons x xs ih =>
      intro h
      constructor
      · exact ih (List.sublist_of_cons_sublist h)
      · exact linearOrderList_cons h
