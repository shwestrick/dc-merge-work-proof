import DCMerge.Lg

/-!
# Section 4. Technical Lemma: Even Spreading

**Lemma 4.1.** For any `x₁, …, x_k ∈ ℕ` with `∑ xᵢ ≤ M`,
`∑ lg xᵢ ≤ k lg (M / k) + O(k)`. We prove it with the explicit constant `3 k`.

The proof follows the sketch in the writeup:
1. replace every zero by one (does not change `∑ lg xᵢ` or `k`; total becomes `≤ M + k`);
2. `∑ lg xᵢ ≤ lg ∏ xᵢ + k` (per-element rounding);
3. the *maximization process*: repeatedly move one unit from a larger element to a
   smaller one when they differ by two or more; this increases the product while
   preserving length and total, and ends with every element within one of the average,
   so `∏ xᵢ ≤ (S / k + 1)^k` where `S` is the total;
4. take `lg`.
-/

open Lg

namespace EvenSpreading

/-- **The maximization process** (step 3). For a multiset `s` of naturals with `k`
elements and total `S`, `∏ s ≤ (S / k + 1)^k`.

The proof is the smoothing process from the writeup, by well-founded induction on the
sum of squares (which strictly decreases with each unit move). We always move a unit
from a maximum element `a` to a minimum element `b`; when `a ≤ b + 1` every pair of
elements differs by at most one and the process stops. -/
theorem prod_le_balanced (s : Multiset ℕ) :
    s.prod ≤ (s.sum / Multiset.card s + 1) ^ Multiset.card s := by
  induction h : (s.map (· ^ 2)).sum using Nat.strong_induction_on generalizing s with
  | _ N ih =>
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  obtain ⟨a, ha, hamax⟩ := Multiset.exists_max_image id hs
  obtain ⟨b, hb, hbmin⟩ := Multiset.exists_min_image id hs
  simp only [id] at hamax hbmin
  rcases Nat.lt_or_ge (b + 1) a with hab | hab
  · -- `a` and `b` differ by two or more: move one unit from `a` to `b`.
    have hb' : b ∈ s.erase a := (Multiset.mem_erase_of_ne (by omega)).mpr hb
    set t := (s.erase a).erase b
    have hst : s = a ::ₘ b ::ₘ t := by
      rw [Multiset.cons_erase hb', Multiset.cons_erase ha]
    obtain ⟨e, rfl⟩ : ∃ e, a = b + 2 + e := ⟨a - (b + 2), by omega⟩
    set s' := (b + 1 + e) ::ₘ (b + 1) ::ₘ t
    -- length and total are preserved
    have hcard : Multiset.card s' = Multiset.card s := by simp [s', hst]
    have hsum : s'.sum = s.sum := by simp only [s', hst, Multiset.sum_cons]; ring
    -- the product does not decrease
    have hprod : s.prod ≤ s'.prod := by
      simp only [s', hst, Multiset.prod_cons, ← mul_assoc]
      exact Nat.mul_le_mul_right _ (by nlinarith)
    -- the sum of squares strictly decreases
    have hsq : (s'.map (· ^ 2)).sum < N := by
      rw [← h, hst]
      simp only [s', Multiset.map_cons, Multiset.sum_cons, ← add_assoc]
      apply Nat.add_lt_add_right
      nlinarith
    calc s.prod ≤ s'.prod := hprod
      _ ≤ (s'.sum / Multiset.card s' + 1) ^ Multiset.card s' := ih _ hsq s' rfl
      _ = _ := by rw [hcard, hsum]
  · -- Every element is within one of the minimum `b`, and `b ≤ S / k`.
    have hk : 0 < Multiset.card s := Multiset.card_pos.mpr hs
    have hlow : Multiset.card s • b ≤ s.sum := Multiset.card_nsmul_le_sum hbmin
    have hbavg : b ≤ s.sum / Multiset.card s := by
      rw [smul_eq_mul] at hlow
      exact (Nat.le_div_iff_mul_le hk).mpr (by linarith)
    apply Multiset.prod_le_pow_card
    intro x hx
    have := hamax x hx
    omega

/-- Step 2: per-element rounding. If every element is nonzero,
`∑ lg yᵢ ≤ lg ∏ yᵢ + k`. -/
theorem sum_lg_le_lg_prod (ys : List ℕ) (hys : ∀ y ∈ ys, 1 ≤ y) :
    (ys.map lg).sum ≤ lg ys.prod + ys.length := by
  -- `2 ^ (∑ lg yᵢ) ≤ 2^k ∏ yᵢ`, from `2 ^ lg y ≤ 2 y`.
  have key : 2 ^ (ys.map lg).sum ≤ 2 ^ ys.length * ys.prod := by
    induction ys with
    | nil => simp
    | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.prod_cons, pow_add,
        pow_one]
      have h1 : 2 ^ lg y ≤ 2 * y := (two_pow_lg_lt (hys y (by simp))).le
      have h2 := ih (fun z hz => hys z (by simp [hz]))
      calc 2 ^ lg y * 2 ^ (ys.map lg).sum ≤ (2 * y) * (2 ^ ys.length * ys.prod) :=
            Nat.mul_le_mul h1 h2
        _ = 2 ^ ys.length * 2 * (y * ys.prod) := by ring
  have : 2 ^ (ys.map lg).sum ≤ 2 ^ (lg ys.prod + ys.length) := by
    rw [pow_add, mul_comm]
    exact key.trans (Nat.mul_le_mul_left _ (le_two_pow_lg _))
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

/-- **Lemma 4.1** (Even spreading is worst). For any `x₁, …, x_k ∈ ℕ` with
`∑ xᵢ ≤ M`, we have `∑ lg xᵢ ≤ k lg (M / k) + 3 k`. -/
theorem lemma_4_1 (xs : List ℕ) (M : ℕ) (hM : xs.sum ≤ M) :
    (xs.map lg).sum ≤ xs.length * lg (M / xs.length) + 3 * xs.length := by
  set k := xs.length with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have : xs = [] := List.length_eq_zero_iff.mp (hk ▸ hk0)
    subst this; simp
  -- Step 1: replace each zero by one.
  set ys := xs.map (max 1) with hys
  have hlg : (ys.map lg).sum = (xs.map lg).sum := by
    simp only [ys, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => lg_max_one x
  have hlen : ys.length = k := by simp [ys, hk]
  have hpos : ∀ y ∈ ys, 1 ≤ y := by simp [ys]
  have hsum : ys.sum ≤ M + k := by
    have : ∀ l : List ℕ, (l.map (max 1)).sum ≤ l.sum + l.length := by
      intro l
      induction l with
      | nil => simp
      | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
    have := this xs
    rw [hys]
    omega
  -- Step 2: `∑ lg yᵢ ≤ lg ∏ yᵢ + k`.
  have h2 := sum_lg_le_lg_prod ys hpos
  -- Step 3: the maximization process, `∏ yᵢ ≤ (S/k + 1)^k`.
  have h3 : ys.prod ≤ (ys.sum / k + 1) ^ k := by
    have := prod_le_balanced (ys : Multiset ℕ)
    simpa [hlen] using this
  -- Step 4: take `lg`. Since `S ≤ M + k`, `S / k + 1 ≤ M / k + 2`.
  have havg : ys.sum / k + 1 ≤ M / k + 2 := by
    have : ys.sum / k ≤ (M + k) / k := Nat.div_le_div_right hsum
    rw [Nat.add_div_right _ hkpos] at this
    omega
  have h4 : lg ys.prod ≤ k * (lg (M / k) + 2) :=
    calc lg ys.prod ≤ lg ((ys.sum / k + 1) ^ k) := lg_mono h3
      _ ≤ k * lg (ys.sum / k + 1) := lg_pow_le _ _
      _ ≤ k * lg (M / k + 2) := Nat.mul_le_mul_left _ (lg_mono havg)
      _ ≤ k * (lg (M / k) + 2) := Nat.mul_le_mul_left _ (lg_add_two_le _)
  rw [← hlg]
  rw [hlen] at h2
  nlinarith

end EvenSpreading
