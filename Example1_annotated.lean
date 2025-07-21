import Mathlib

namespace test

open GaussianInt

/-- **Fermat's theorem on the sum of two squares**. Every prime not congruent to 3 mod 4 is the sum
of two squares. Also known as **Fermat's Christmas theorem**. -/
theorem Nat.Prime.sq_add_sq {p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  apply sq_add_sq_of_nat_prime_of_not_irreducible p
  -- Key Step: If `p` is not irreducible in `ℤ[i]`, then `p ^ 2 = a ^ 2 + b ^ 2` for some `a b : ℕ`.
  -- Implicit type conversion from `ℕ` to `ℤ[i]` is used here.
  rwa [_root_.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p]
  -- Key Step: A prime natural number is prime in `ℤ[i]` if and only if it is 3 mod 4.
