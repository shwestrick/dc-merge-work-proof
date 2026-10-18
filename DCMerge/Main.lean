import DCMerge.CostTree
import DCMerge.EvenSpreading
import DCMerge.LevelSum

/-!
# Section 3. Proof of Theorem 2.1

Every cost tree `T` with root label `(n, m)` has `‖T‖ ∈ O(n + m)`; explicitly
`‖T‖ ≤ 11 n + 5 m + 7`, and hence `‖T‖ ≤ 18 (n + m)`.
-/

open Finset Lg

namespace CostTree

variable {n m : ℕ}

/-- `‖T‖` splits into the internal nodes and the leaf nodes. -/
theorem weight_eq (T : CostTree n m) : T.weight = T.leafWeight + T.internalWeight := by
  induction T with
  | leaf n m => simp [weight, leafWeight, internalWeight]
  | node p hp hn l r ihl ihr => simp only [weight, leafWeight, internalWeight, ihl, ihr]; ring

/-- The total weight of all leaf nodes is exactly `n + m - i`, where `i` is the number of
internal nodes: each internal node consumes one unit of `n`, and `m` is partitioned onto
the leaves. -/
theorem leafWeight_add_numInternal (T : CostTree n m) :
    T.leafWeight + T.numInternal = n + m := by
  induction T with
  | leaf n m => simp [leafWeight, numInternal]
  | @node n m p hp hn l r ihl ihr =>
    simp only [leafWeight, numInternal]
    omega

theorem leafWeight_le (T : CostTree n m) : T.leafWeight ≤ n + m := by
  have := T.leafWeight_add_numInternal; omega

/-- `M_d ≤ m`: each layer partitions (part of) the input size `m`. -/
theorem M_le (T : CostTree n m) (d : ℕ) : T.M d ≤ m := by
  induction T generalizing d with
  | leaf => simp [M, levelM]
  | @node n m p hp hn l r ihl ihr =>
    cases d with
    | zero => simp [M, levelM]
    | succ d =>
      have h1 := ihl d; have h2 := ihr d
      simp only [M, levelM, List.sum_append] at *
      omega

/-- `k_d ≤ 2^d`: the tree is binary. -/
theorem k_le (T : CostTree n m) (d : ℕ) : T.k d ≤ 2 ^ d := by
  induction T generalizing d with
  | leaf => simp [k, levelM]
  | @node n m p hp hn l r ihl ihr =>
    cases d with
    | zero => simp [k, levelM]
    | succ d =>
      have h1 := ihl d; have h2 := ihr d
      simp only [k, levelM, List.length_append, pow_succ] at *
      omega

/-- Both children of an internal node have height one less: if every depth of the parent
is below `d + 1 ≥ lg (n + 1)`, the children's depths are below `d`. -/
theorem child_lg_le {n d : ℕ} (h : lg (n + 1) ≤ d + 1) :
    lg (n / 2 + 1) ≤ d ∧ lg (n - 1 - n / 2 + 1) ≤ d := by
  rw [lg_le_iff, pow_succ] at h
  exact ⟨lg_le_iff.mpr (by omega), lg_le_iff.mpr (by omega)⟩

/-- Grouping the internal nodes by depth. Internal nodes only occur at depths
`d < lg (n + 1)` (an internal node at depth `d` has `1 ≤ n_v ≤ n / 2^d`), so the internal
weight is the sum over those levels of `∑_{v at depth d} lg m_v`. -/
theorem internalWeight_eq_sum (T : CostTree n m) (H : ℕ) (hH : lg (n + 1) ≤ H) :
    T.internalWeight = ∑ d ∈ range H, ((T.levelM d).map lg).sum := by
  induction T generalizing H with
  | leaf => simp [internalWeight, levelM]
  | @node n m p hp hn l r ihl ihr =>
    obtain ⟨H, rfl⟩ : ∃ H', H = H' + 1 := by
      refine ⟨H - 1, ?_⟩
      have : 1 ≤ lg (n + 1) := by
        by_contra h0
        have := lg_le_iff.mp (show lg (n + 1) ≤ 0 by omega)
        simp at this; omega
      omega
    obtain ⟨hl, hr⟩ := child_lg_le hH
    rw [sum_range_succ']
    simp only [levelM, List.map_append, List.sum_append, sum_add_distrib, internalWeight,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ihl H hl, ihr H hr]
    ring

/-- The "even spreading" bound for one level, applied to the level padded with zeros
to exactly `2^d` elements:
`∑_{v at depth d} lg m_v = ∑_{v at depth d} lg m_v + (2^d - k_d) lg 0 ≤ 2^d lg(M_d/2^d) + O(2^d)`;
then `M_d ≤ m`. -/
theorem level_le (T : CostTree n m) (d : ℕ) :
    ((T.levelM d).map lg).sum ≤ 2 ^ d * lg (m / 2 ^ d) + 3 * 2 ^ d := by
  set L := T.levelM d
  have hk : L.length ≤ 2 ^ d := T.k_le d
  have hM : L.sum ≤ m := T.M_le d
  -- padding for `2^d` elements total, with `m_v = 0`
  set padded := L ++ List.replicate (2 ^ d - L.length) 0
  have hpad_lg : (padded.map lg).sum = (L.map lg).sum := by
    simp [padded, List.map_replicate]
  have hpad_len : padded.length = 2 ^ d := by simp [padded]; omega
  have hpad_sum : padded.sum = L.sum := by simp [padded]
  -- direct application of Lemma 4.1 to the padded layer, whose total is exactly `M_d`
  have h := EvenSpreading.lemma_4_1 padded L.sum hpad_sum.le
  rw [hpad_lg, hpad_len] at h
  -- `M_d ≤ m`
  have h2 : lg (L.sum / 2 ^ d) ≤ lg (m / 2 ^ d) := lg_mono (Nat.div_le_div_right hM)
  have h3 := Nat.mul_le_mul_left (2 ^ d) h2
  omega

/-- The internal nodes have linear weight. -/
theorem internalWeight_le (T : CostTree n m) : T.internalWeight ≤ 10 * n + 4 * m + 7 := by
  set D := lg (n + 1)
  rw [T.internalWeight_eq_sum D le_rfl]
  calc ∑ d ∈ range D, ((T.levelM d).map lg).sum
      ≤ ∑ d ∈ range D, (2 ^ d * lg (m / 2 ^ d) + 3 * 2 ^ d) :=
        sum_le_sum fun d _ => T.level_le d
    _ = ∑ d ∈ range D, 2 ^ d * lg (m / 2 ^ d) + 3 * ∑ d ∈ range D, 2 ^ d := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ (4 * (n + 1) + 4 * m + 3) + 3 * (2 * n) := by
        gcongr
        · -- Lemma 5.2, with `lg (n + 1)` levels
          exact LevelSum.lemma_5_2 (n + 1) m
        · -- the `O(k_d)` terms: `∑_{d < D} 2^d = 2^D - 1 ≤ 2 n`
          have h1 := sum_two_pow D
          have h2 : 2 ^ D < 2 * (n + 1) := two_pow_lg_lt (by omega)
          omega
    _ = 10 * n + 4 * m + 7 := by ring

/-- **Theorem 2.1** (precise form). Every cost tree `T` with root label `(n, m)` has
`‖T‖ ≤ 11 n + 5 m + 7`. -/
theorem theorem_2_1 (T : CostTree n m) : T.weight ≤ 11 * n + 5 * m + 7 := by
  rw [weight_eq]
  have := T.leafWeight_le
  have := T.internalWeight_le
  omega

/-- **Theorem 2.1.** Every cost tree `T` with root label `(n, m)` has `‖T‖ ∈ O(n + m)`:
a single constant `C` works for all cost trees. -/
theorem theorem_2_1_bigO : ∃ C, ∀ (n m : ℕ) (T : CostTree n m), T.weight ≤ C * (n + m) := by
  refine ⟨18, fun n m T => ?_⟩
  rcases Nat.eq_zero_or_pos (n + m) with h | h
  · -- `(0, 0)` admits only a leaf, of weight `0`
    cases T with
    | leaf => simp [weight]; omega
    | node p hp hn l r => omega
  · have := T.theorem_2_1; omega

/-- There are at most `n` internal nodes (each consumes one unit of `n`). -/
theorem numInternal_le (T : CostTree n m) : T.numInternal ≤ n := by
  induction T with
  | leaf => simp [numInternal]
  | @node n m p hp hn l r ihl ihr => simp only [numInternal]; omega

/-- Not in the writeup: the bound survives charging an extra unit of work per internal
node (for writing the pivot `A[i]` to the output, and for the `+1` by which a real binary
search over `m` elements, `lg (m + 1)` comparisons, can exceed `lg m`). -/
theorem weight_add_numInternal_le (T : CostTree n m) :
    T.weight + T.numInternal ≤ 12 * n + 5 * m + 7 := by
  have := T.theorem_2_1
  have := T.numInternal_le
  omega

end CostTree
