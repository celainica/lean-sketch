```lean4

***main theorem***:

modEq_and_modEq_iff_modEq_mul':

import Mathlib

theorem modEq_and_modEq_iff_modEq_mul' {a b m n : ℕ} (hmn : m.Coprime n) :
    a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n] :=
  ⟨fun h => by
    rw [Nat.modEq_iff_dvd, Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast,
      ← Int.dvd_natAbs, Int.natCast_dvd_natCast] at h
    rw [Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2,
   fun h => ⟨h.of_mul_right _, h.of_mul_left _⟩⟩



***lemmas***:

Coprime.mul_dvd_of_dvd_of_dvd:

theorem Coprime.mul_dvd_of_dvd_of_dvd (hmn : Coprime m n) (hm : m ∣ a) (hn : n ∣ a) : m * n ∣ a :=
  let ⟨_, hk⟩ := hm
  hk.symm ▸ Nat.mul_dvd_mul_left _ (hmn.symm.dvd_of_dvd_mul_left (hk ▸ hn))

Nat.modEq_iff_dvd:

theorem modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : ℤ) ∣ b - a := by
  rw [ModEq, eq_comm, ← Int.natCast_inj, Int.natCast_mod, Int.natCast_mod,
  Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]



***definitions***:

none
```

