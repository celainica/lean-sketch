import Mathlib

open Real

theorem chebyshev_identity {x α : ℝ} (hx : x ≠ 0) (h : x + 1 / x = 2 * Real.cos α) :
    ∀ n : ℕ, x ^ n + 1 / x ^ n = 2 * Real.cos (n * α) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [one_add_one_eq_two]
    | 1 => simpa [hx] using h
    | n + 2 =>
      nth_rw 3 [Nat.add_succ]
      push_cast
      rw [add_mul, one_mul]
      have eq1 : cos ((↑n + 1) * α + α) = 2 * cos ((↑n + 1) * α) * cos α - cos (n * α):= by
        rw [two_mul_cos_mul_cos]
        ring_nf
      rw [eq1]
      norm_cast
      have eq2 := ih (n + 1) (by norm_num)
      have eq3 : cos (n * α) = 1 / 2  * (x ^ n + 1 / x ^ n) := by
        rw [ih n (by norm_num)]
        simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.inv_mul_cancel_left]
      have eq4 : cos α = 1 / 2 * (x + 1 / x) := by
        rw [h]
        simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.inv_mul_cancel_left]
      rw [← eq2, eq3, eq4]
      field_simp [hx]
      ring
