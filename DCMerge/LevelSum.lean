import DCMerge.Lg

/-!
# Section 5. Technical Lemma: Level Summation

We prove `∑_{d < lg n} 2^d lg(m / 2^d) ∈ O(n + m)` (Lemma 5.2), with the explicit
bound `4 n + 4 m + 3`, via the auxiliary Lemma 5.1.
-/

open Finset Lg

namespace LevelSum

/-- The exact identity from the proof of Lemma 5.1:
`∑_{i=1}^k i 2^(k-i) = 2^(k+1) - k - 2` (stated without truncated subtraction). -/
theorem sum_eq (k : ℕ) : (∑ i ∈ Icc 1 k, i * 2 ^ (k - i)) + k + 2 = 2 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero, mul_one]
    have h : ∑ i ∈ Icc 1 k, i * 2 ^ (k + 1 - i) = 2 * ∑ i ∈ Icc 1 k, i * 2 ^ (k - i) := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [mem_Icc] at hi
      rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]
      ring
    rw [h, pow_succ 2 (k + 1)]
    omega

/-- **Lemma 5.1** (Largest term dominates). `∑_{i=1}^k i 2^(k-i) ≤ 2^(k+1)`. -/
theorem lemma_5_1 (k : ℕ) : ∑ i ∈ Icc 1 k, i * 2 ^ (k - i) ≤ 2 ^ (k + 1) := by
  have := sum_eq k; omega

/-- Reindexing `i = K - d`: `∑_{d < K} 2^d (K - d) = ∑_{i=1}^K i 2^(K-i)`. -/
theorem reindex (K : ℕ) :
    ∑ d ∈ range K, 2 ^ d * (K - d) = ∑ i ∈ Icc 1 K, i * 2 ^ (K - i) := by
  refine sum_nbij' (fun d => K - d) (fun i => K - i) ?_ ?_ ?_ ?_ ?_
  · intro d hd; simp only [mem_range, mem_Icc] at *; omega
  · intro i hi; simp only [mem_range, mem_Icc] at *; omega
  · intro d hd; simp only [mem_range] at *; omega
  · intro i hi; simp only [mem_Icc] at *; omega
  · intro d hd
    simp only [mem_range] at hd
    rw [show K - (K - d) = d by omega, mul_comm]

/-- `lg (m / 2^d) ≤ B - d` (truncated) where `B = lg m`. -/
theorem lg_div_le (m d : ℕ) : lg (m / 2 ^ d) ≤ lg m - d := by
  rw [lg_le_iff]
  apply Nat.div_le_of_le_mul
  rw [← pow_add]
  exact (le_two_pow_lg m).trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **Lemma 5.2** (Level sum). `∑_{d < lg n} 2^d lg(m/2^d) ∈ O(n + m)`; explicitly,
it is at most `4 n + 4 m + 3`. -/
theorem lemma_5_2 (n m : ℕ) :
    ∑ d ∈ range (lg n), 2 ^ d * lg (m / 2 ^ d) ≤ 4 * n + 4 * m + 3 := by
  -- Let `D ≜ lg n` and `B ≜ lg m`.
  set D := lg n with hD
  set B := lg m with hB
  have hn : 2 ^ D ≤ 2 * n + 1 := two_pow_lg_le n
  have hm : 2 ^ B ≤ 2 * m + 1 := two_pow_lg_le m
  -- We have `lg(m/2^d) ≤ B - d`, so it suffices to bound `∑_{d<D} 2^d (B - d)`.
  have step : ∑ d ∈ range D, 2 ^ d * lg (m / 2 ^ d) ≤ ∑ d ∈ range D, 2 ^ d * (B - d) :=
    sum_le_sum fun d _ => Nat.mul_le_mul_left _ (lg_div_le m d)
  refine step.trans ?_
  rcases lt_or_ge B D with hBD | hDB
  · -- Case `D > B`. Every term with `d ≥ B` is zero; reindex by `i = B - d`.
    have hzero : ∑ d ∈ range D, 2 ^ d * (B - d) = ∑ d ∈ range B, 2 ^ d * (B - d) := by
      symm
      refine sum_subset (range_subset_range.mpr hBD.le) fun d _ hd => ?_
      simp only [mem_range, not_lt] at hd
      simp [Nat.sub_eq_zero_of_le hd]
    rw [hzero, reindex]
    have := lemma_5_1 B
    rw [pow_succ] at this
    -- `≤ 2^(B+1) ≤ 4 m + 2`
    omega
  · -- Case `D ≤ B`. Split `B - d = (B - D) + (D - d)` and reindex the second part.
    have hsplit : ∑ d ∈ range D, 2 ^ d * (B - d)
        = (∑ d ∈ range D, 2 ^ d) * (B - D) + ∑ d ∈ range D, 2 ^ d * (D - d) := by
      rw [sum_mul, ← sum_add_distrib]
      refine sum_congr rfl fun d hd => ?_
      simp only [mem_range] at hd
      rw [← mul_add]; congr 1; omega
    rw [hsplit, reindex]
    -- First term: `(B - D)(2^D - 1) ≤ 2^(B-D) 2^D = 2^B ≤ 2 m + 1`.
    have h1 : (∑ d ∈ range D, 2 ^ d) * (B - D) ≤ 2 * m + 1 := by
      have hg := sum_two_pow D
      have hx : B - D ≤ 2 ^ (B - D) := (Nat.lt_two_pow_self).le
      calc (∑ d ∈ range D, 2 ^ d) * (B - D) ≤ 2 ^ D * 2 ^ (B - D) :=
            Nat.mul_le_mul (by omega) hx
        _ = 2 ^ B := by rw [← pow_add]; congr 1; omega
        _ ≤ 2 * m + 1 := hm
    -- Second term: `≤ 2^(D+1) ≤ 4 n + 2` by Lemma 5.1.
    have h2 := lemma_5_1 D
    rw [pow_succ] at h2
    omega

end LevelSum
