import Mathlib

/-!
# Notation and conventions

The writeup uses `lg` for the *rounded-up* base-two logarithm with `lg 0 = 0`.
This is exactly Mathlib's `Nat.clog 2`. Division is floor division and subtraction
is truncated, which are Lean's defaults on `ℕ`.
-/

/-- Rounded-up base-two logarithm, with `lg 0 = lg 1 = 0`. -/
def lg (n : ℕ) : ℕ := Nat.clog 2 n

namespace Lg

@[simp] theorem lg_zero : lg 0 = 0 := by simp [lg]
@[simp] theorem lg_one : lg 1 = 0 := by simp [lg]

theorem lg_le_iff {x y : ℕ} : lg x ≤ y ↔ x ≤ 2 ^ y :=
  Nat.clog_le_iff_le_pow (by norm_num)

theorem le_two_pow_lg (x : ℕ) : x ≤ 2 ^ lg x := lg_le_iff.mp le_rfl

theorem lg_mono {a b : ℕ} (h : a ≤ b) : lg a ≤ lg b :=
  Nat.clog_mono_right 2 h

/-- For `x ≥ 1`, rounding up loses less than a factor of two: `2 ^ lg x < 2 x`. -/
theorem two_pow_lg_lt {x : ℕ} (hx : 1 ≤ x) : 2 ^ lg x < 2 * x := by
  rcases Nat.lt_or_ge 1 x with h | h
  · have h1 : 2 ^ (lg x).pred < x := Nat.pow_pred_clog_lt_self (by norm_num) h
    have h2 : 0 < lg x := Nat.clog_pos (by norm_num) h
    rw [show lg x = (lg x).pred + 1 from (Nat.succ_pred_eq_of_pos h2).symm, pow_succ]
    omega
  · have : x = 1 := by omega
    subst this; simp

/-- `2 ^ lg x ≤ 2 x + 1` for every `x` (the `+1` handles `x = 0`). -/
theorem two_pow_lg_le (x : ℕ) : 2 ^ lg x ≤ 2 * x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := two_pow_lg_lt hx; omega

theorem lg_two_mul_le (x : ℕ) : lg (2 * x) ≤ lg x + 1 := by
  rw [lg_le_iff, pow_succ]
  have := le_two_pow_lg x
  omega

theorem lg_succ_le (x : ℕ) : lg (x + 1) ≤ lg x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · exact (lg_mono (by omega : x + 1 ≤ 2 * x)).trans (lg_two_mul_le x)

theorem lg_add_two_le (x : ℕ) : lg (x + 2) ≤ lg x + 2 :=
  (lg_succ_le (x + 1)).trans (by have := lg_succ_le x; omega)

theorem lg_pow_le (a k : ℕ) : lg (a ^ k) ≤ k * lg a := by
  rw [lg_le_iff, mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (le_two_pow_lg a) k

theorem lg_max_one (x : ℕ) : lg (max 1 x) = lg x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [max_eq_right hx]

/-- `∑_{d < D} 2^d = 2^D - 1`, stated without truncated subtraction. -/
theorem sum_two_pow (D : ℕ) : (∑ d ∈ Finset.range D, 2 ^ d) + 1 = 2 ^ D := by
  induction D with
  | zero => simp
  | succ D ih => rw [Finset.sum_range_succ, pow_succ]; omega

end Lg
