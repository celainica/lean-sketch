import Mathlib

open Real

/- Prove that if $x$ is such that $$x +\frac{1}{x}= 2\cos \alpha $$ then, for all $n = 0, 1, 2, . . . ,$
$$x^n ++\frac{1}{x^n}= 2\cos n \alpha .$$ -/
theorem chebyshev_identity {x α : ℝ} (hx : x ≠ 0) (h : x + 1 / x = 2 * Real.cos α) :
    ∀ n : ℕ, x ^ n + 1 / x ^ n = 2 * Real.cos (n * α) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    -- 1. **Case \( n = 0 \)**: $x^0 + \frac{1}{x^0} = 1 + 1 = 2 = 2\cos(0\alpha)$
    | 0 => simp [one_add_one_eq_two]
    -- 2. **Case \( n = 1 \)**: Given \( x + \frac{1}{x} = 2\cos\alpha \), which matches the formula for \( n=1 \).
    | 1 => simpa [hx] using h
    -- Assume the formula holds for all \( k \leq n+1 \). We prove it for \( n+2 \).
    | n + 2 =>
      nth_rw 3 [Nat.add_succ]
      push_cast
      rw [add_mul, one_mul]
      -- `KeyStep` : Using the trigonometric identity: \[ 2\cos A \cos B = \cos(A+B) + \cos(A-B), \]
      -- we rewrite: \[ \cos((n+2)\alpha) = 2\cos((n+1)\alpha)\cos\alpha - \cos(n\alpha). \]
      have eq1 : cos ((↑n + 1) * α + α) = 2 * cos ((↑n + 1) * α) * cos α - cos (n * α):= by
        rw [two_mul_cos_mul_cos]
        ring_nf
      -- Thus: $$2\cos((n+2)\alpha)= 2(2\cos((n+1)\alpha)\cos\alpha - \cos(n\alpha)) $$
      rw [eq1]
      norm_cast
      -- `KeyStep` : We need to calculate
      -- 2\cos((n+1)\alpha)\cos\alpha - \cos(n\alpha) that using the induction hypothesis
      have eq2 := ih (n + 1) (by norm_num)
      have eq3 : cos (n * α) = 1 / 2  * (x ^ n + 1 / x ^ n) := by
        rw [ih n (by norm_num)]
        simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.inv_mul_cancel_left]
      have eq4 : cos α = 1 / 2 * (x + 1 / x) := by
        rw [h]
        simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.inv_mul_cancel_left]
      -- Finally, by induction hypothesis:
      -- $$\cos((n+1)\alpha)= 1 / 2 (x^{n+1} + 1 / x^{n+1}) $$
      -- $$\cos(n \alpha) = 1 / 2 (x ^ n + 1 / x ^ n )$$
      rw [← eq2, eq3, eq4]
      -- Then by direct calculation, we're done.
      field_simp [hx]
      ring
