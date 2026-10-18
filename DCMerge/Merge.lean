import DCMerge.Main

/-!
# Figure 1: the `Merge` algorithm and its work

This file is not part of the writeup's proof; it makes precise the sentence
"each cost tree corresponds to a run of `Merge`" from Section 2.

We implement `Merge(A, B)` from Figure 1 on lists of naturals, instrumented with a work
counter that uses the writeup's cost model: the sequential base case and the copy of `B`
cost `|A| + |B|`, and the binary search at an internal node costs `lg |B|`. We then show
that every run's work is the weight of some cost tree, so Theorem 2.1 bounds it.
-/

open Lg

namespace CostTree

/-- Transport a cost tree along equalities of its labels (does not change the weight). -/
def cast {n m n' m' : ℕ} (h1 : n = n') (h2 : m = m') (T : CostTree n m) : CostTree n' m' :=
  h1 ▸ h2 ▸ T

@[simp] theorem weight_cast {n m n' m' : ℕ} (h1 : n = n') (h2 : m = m') (T : CostTree n m) :
    (T.cast h1 h2).weight = T.weight := by
  subst h1; subst h2; rfl

end CostTree

/-- `Merge(A, B)` from Figure 1, returning `(output, work)`. Inputs with
`|A| + |B| ≤ grain` count as "small". The position of `A[i]` in `B` is the number of
elements of `B` less than `A[i]` (what binary search computes on a sorted `B`). -/
def merge (grain : ℕ) (A B : List ℕ) : List ℕ × ℕ :=
  if A.length + B.length ≤ grain then
    (A.merge B (fun a b => decide (a ≤ b)), A.length + B.length)
  else if h : A.length = 0 then
    (B, A.length + B.length)
  else
    let i := A.length / 2
    let x := A[i]'(by omega)
    let j := B.countP (fun y => decide (y < x))
    let L := merge grain (A.take i) (B.take j)
    let R := merge grain (A.drop (i + 1)) (B.drop j)
    (L.1 ++ x :: R.1, lg B.length + L.2 + R.2)
termination_by A.length
decreasing_by all_goals simp; omega

/-- The work of every run of `merge` is the weight of a cost tree with root label
`(|A|, |B|)`. -/
theorem merge_work_is_cost_tree (grain : ℕ) (A B : List ℕ) :
    ∃ T : CostTree A.length B.length, (merge grain A B).2 = T.weight := by
  induction h : A.length using Nat.strong_induction_on generalizing A B with
  | _ N ih =>
  subst h
  rw [merge]
  split_ifs with hs h0
  · exact ⟨.leaf _ _, rfl⟩
  · exact ⟨.leaf _ _, rfl⟩
  · dsimp only
    set i := A.length / 2
    set j := B.countP (fun y => decide (y < A[i]'(by omega)))
    have hj : j ≤ B.length := List.countP_le_length
    obtain ⟨Tl, hl⟩ := ih _ (by simp; omega) (A.take i) (B.take j) rfl
    obtain ⟨Tr, hr⟩ := ih _ (by simp; omega) (A.drop (i + 1)) (B.drop j) rfl
    refine ⟨.node j hj (by omega)
      (Tl.cast (by simp; omega) (by simp; omega))
      (Tr.cast (by simp; omega) (by simp)), ?_⟩
    simp only [CostTree.weight, CostTree.weight_cast]
    rw [hl, hr]

/-- **Linear work for `Merge`.** Every run of `merge` on inputs of sizes `n = |A|` and
`m = |B|` does at most `11 n + 5 m + 7 ≤ 18 (n + m)` work. -/
theorem merge_work_le (grain : ℕ) (A B : List ℕ) :
    (merge grain A B).2 ≤ 11 * A.length + 5 * B.length + 7 := by
  obtain ⟨T, hT⟩ := merge_work_is_cost_tree grain A B
  exact hT ▸ T.theorem_2_1

theorem merge_work_le' (grain : ℕ) (A B : List ℕ) :
    (merge grain A B).2 ≤ 18 * (A.length + B.length) := by
  obtain ⟨T, hT⟩ := merge_work_is_cost_tree grain A B
  rw [hT]
  rcases Nat.eq_zero_or_pos (A.length + B.length) with h | h
  · cases T with
    | leaf => simp [CostTree.weight]; omega
    | node p hp hn l r => omega
  · have := T.theorem_2_1; omega
