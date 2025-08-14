```lean4
***main theorem***:

quadratic_reciprocity:

import Mathlib

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

namespace legendreSym

open ZMod

/-- **The Law of Quadratic Reciprocity**: if `p` and `q` are distinct odd primes, then
`(q / p) * (p / q) = (-1)^((p-1)(q-1)/4)`. -/
theorem quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by
  have hp₁ := (Nat.Prime.eq_two_or_odd <| @Fact.out p.Prime _).resolve_left hp
  have hq₁ := (Nat.Prime.eq_two_or_odd <| @Fact.out q.Prime _).resolve_left hq
  have hq₂ : ringChar (ZMod q) ≠ 2 := (ringChar_zmod_n q).substr hq
  have h :=
    quadraticChar_odd_prime ((ringChar_zmod_n p).substr hp) hq ((ringChar_zmod_n p).substr hpq)
  rw [card p] at h
  have nc : ∀ n r : ℕ, ((n : ℤ) : ZMod r) = n := fun n r => by norm_cast
  have nc' : (((-1) ^ (p / 2) : ℤ) : ZMod q) = (-1) ^ (p / 2) := by norm_cast
  rw [legendreSym, legendreSym, nc, nc, h, map_mul, mul_rotate', mul_comm (p / 2), ← pow_two,
    quadraticChar_sq_one (prime_ne_zero q p hpq.symm), mul_one, pow_mul, χ₄_eq_neg_one_pow hp₁, nc',
    map_pow, quadraticChar_neg_one hq₂, card q, χ₄_eq_neg_one_pow hq₁]



***lemmas***:

quadraticChar_odd_prime:

/-- The value of the quadratic character at an odd prime `p` different from `ringChar F`. -/
theorem quadraticChar_odd_prime [DecidableEq F] (hF : ringChar F ≠ 2) {p : ℕ} [Fact p.Prime]
    (hp₁ : p ≠ 2) (hp₂ : ringChar F ≠ p) :
    quadraticChar F p = quadraticChar (ZMod p) (χ₄ (Fintype.card F) * Fintype.card F) := by
  rw [← quadraticChar_neg_one hF]
  have h := quadraticChar_card_card hF (ne_of_eq_of_ne (ringChar_zmod_n p) hp₁)
    (ne_of_eq_of_ne (ringChar_zmod_n p) hp₂.symm)
  rwa [card p] at h


quadraticChar_neg_one:

/-- For `a : F`, `quadraticChar F a = -1 ↔ ¬ IsSquare a`. -/
theorem quadraticChar_neg_one_iff_not_isSquare {a : F} : quadraticChar F a = -1 ↔ ¬IsSquare a := by
  by_cases ha : a = 0
  · simp only [ha, MulChar.map_zero, zero_eq_neg, one_ne_zero, IsSquare.zero, not_true]
  · rw [quadraticChar_eq_neg_one_iff_not_one ha, quadraticChar_one_iff_isSquare ha]


prime_ne_zero:

lemma prime_ne_zero (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) :
    (q : ZMod p) ≠ 0 := by
  rwa [← Nat.cast_zero, Ne, eq_iff_modEq_nat, Nat.modEq_zero_iff_dvd, ←
    hp.1.coprime_iff_not_dvd, Nat.coprime_primes hp.1 hq.1]

χ₄_eq_neg_one_pow:

/-- Alternative description of `χ₄ n` for odd `n : ℕ` in terms of powers of `-1` -/
theorem χ₄_eq_neg_one_pow {n : ℕ} (hn : n % 2 = 1) : χ₄ n = (-1) ^ (n / 2) := by
  rw [χ₄_nat_eq_if_mod_four]
  simp only [hn, Nat.one_ne_zero, if_false]
  nth_rewrite 3 [← Nat.div_add_mod n 4]
  nth_rewrite 3 [show 4 = 2 * 2 by omega]
  rw [mul_assoc, add_comm, Nat.add_mul_div_left _ _ zero_lt_two, pow_add, pow_mul,
    neg_one_sq, one_pow, mul_one]
  have help : ∀ m : ℕ, m < 4 → m % 2 = 1 → ite (m = 1) (1 : ℤ) (-1) = (-1) ^ (m / 2) := by decide
  exact help _ (Nat.mod_lt n (by omega)) <| (Nat.mod_mod_of_dvd n (by omega : 2 ∣ 4)).trans hn



***definitions***:

legendreSym:

/-- The Legendre symbol of `a : ℤ` and a prime `p`, `legendreSym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a nonzero square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendreSym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendreSym (a : ℤ) : ℤ :=
  quadraticChar (ZMod p) a


ringChar:

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable def ringChar [NonAssocSemiring R] : ℕ := Classical.choose (CharP.existsUnique R)


```