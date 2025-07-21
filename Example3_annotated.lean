import Mathlib

open Real

/- Find the maximal value of
$$ S=\sqrt[3]{\frac{a}{b+7}}+\sqrt[3]{\frac{b}{c+7}}+\sqrt[3]{\frac{c}{d+7}}+\sqrt[3]{\frac{d}{a+7}} $$
where $a, b, c, d$ are nonnegative real numbers which satisfy $a+b+c+d=100$. -/
theorem inequality :
    IsGreatest {S : ℝ | ∃ a b c d : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ a + b + c + d = 100 ∧
          S = (a / (b + 7)) ^ ((1 : ℝ) / 3) + (b / (c + 7)) ^ ((1 : ℝ) / 3) +
            (c / (d + 7)) ^ ((1 : ℝ) / 3) + (d / (a + 7)) ^ ((1 : ℝ) / 3)} (8 / 7 ^ ((1 : ℝ) / 3)) := by
  have lem0 {x : ℝ} (hx : 0 ≤ x) : (x ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = x := by
    have := rpow_rpow_inv hx (show (3 : ℝ) ≠ 0 by norm_num)
    simpa only [one_div] using this
  constructor
  · -- 1. Show $\frac{8}{7^{1/3}}$ can be reached
    use 1, 49, 1, 49
    norm_num
    have eq1 : ((1 : ℝ) / 56) ^ ((1 : ℝ) / 3) = 1 / 2 * 1 / 7 ^ ((1 : ℝ) / 3) := by
    -- simplify $$\sqrt[3]{\frac{1}{56}} = \frac{1}{2 \cdot 7^{1/3}}, $$
      field_simp
      rw [← mul_assoc, mul_comm _ 2, mul_assoc]
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
      rw [show (1 : ℝ) / 8 =  (1 / 2) ^ (3 : ℝ) by norm_num]
      rw [lem0 (by norm_num)]
      simp
    have eq2 : ((49 : ℝ) / 8) ^ ((1 : ℝ) / 3) = 7 / 2 * 1 / (7 ^ ((1 : ℝ) / 3)) := by
      -- simplify \sqrt[3]{\frac{49}{8}} = \frac{7^{2/3}}{2}.
      calc
        _ = ((7 / (2 : ℝ)) ^ (3 : ℝ) * ((1 : ℝ) / 7)) ^ ((1 : ℝ) / 3) := by congr 1 ; norm_num
        _ = ((7 / 2) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) * (1 / 7) ^ ((1 : ℝ) / 3) := by
          apply Real.mul_rpow <;> norm_num
        _ = 7 / 2 * (1 / 7) ^ ((1 : ℝ) / 3) := by
          congr
          rw [one_div, rpow_rpow_inv] <;> norm_num
        _ = _ := by
          congr
          · simp only [mul_one]
          · field_simp
            rw [← Real.mul_rpow] <;> norm_num
    rw [eq1, eq2]
    ring
    -- Thus,
    -- $$S = 2 \left( \frac{1}{2 \cdot 7^{1/3}} + \frac{7^{2/3}}{2} \right) = \frac{1 + 7}{7^{1/3}} = \frac{8}{7^{1/3}}.$$
  · -- 2. General Bound via AM-GM
    intro S hS
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hsum, hS⟩ := hS
    have lem1 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
        (x * y * z) ^ ((1 : ℝ) / 3) = x ^ ((1 : ℝ) / 3) * y ^ ((1 : ℝ) / 3) * z ^ ((1 : ℝ) / 3) := by
      rw [Real.mul_rpow (Left.mul_nonneg hx hy) hz, Real.mul_rpow hx hy]
    have ha1 : 0 ≤ a + 7 := add_nonneg ha (by norm_num)
    have hb1 : 0 ≤ b + 7 := add_nonneg hb (by norm_num)
    have hc1 : 0 ≤ c + 7 := add_nonneg hc (by norm_num)
    have hd1 : 0 ≤ d + 7 := add_nonneg hd (by norm_num)
    have ha2 : 0 ≤ 7 / (a + 7) := by
      rw [div_nonneg_iff] ; left
      norm_num
      exact ha1
    have hb2 : 0 ≤ 7 / (b + 7) := by
      rw [div_nonneg_iff] ; left
      norm_num
      exact hb1
    have hc2 : 0 ≤ 7 / (c + 7) := by
      rw [div_nonneg_iff] ; left
      norm_num
      exact hc1
    have hd2 : 0 ≤ 7 / (d + 7) := by
      rw [div_nonneg_iff] ; left
      norm_num
      exact hd1
    have ha3 : 0 ≤ a / (a + 7) := by
      rw [div_nonneg_iff] ; left
      exact ⟨ha, ha1⟩
    have hb3 : 0 ≤ b / (b + 7) := by
      rw [div_nonneg_iff] ; left
      exact ⟨hb, hb1⟩
    have hc3 : 0 ≤ c / (c + 7) := by
      rw [div_nonneg_iff] ; left
      exact ⟨hc, hc1⟩
    have hd3 : 0 ≤ d / (d + 7) := by
      rw [div_nonneg_iff] ; left
      exact ⟨hd, hd1⟩
    have ha4 : 0 ≤ (a + 7) / 64 := by
      rw [div_nonneg_iff] ; left
      norm_num
      exact ha1
    have hb4 : 0 ≤ (b + 7) / 64 := by
      rw [div_nonneg_iff] ; left
      norm_num
      exact hb1
    have hc4 : 0 ≤ (c + 7) / 64 := by
      rw [div_nonneg_iff] ; left
      norm_num
      exact hc1
    have hd4 : 0 ≤ (d + 7) / 64 := by
      rw [div_nonneg_iff] ; left
      norm_num
      exact hd1
    have ha5 : 0 ≤ a / (b + 7) := by
      rw [div_nonneg_iff] ; left
      exact ⟨ha, hb1⟩
    have hb5 : 0 ≤ b / (c + 7) := by
      rw [div_nonneg_iff] ; left
      exact ⟨hb, hc1⟩
    have hc5 : 0 ≤ c / (d + 7) := by
      rw [div_nonneg_iff] ; left
      exact ⟨hc, hd1⟩
    have hd5 : 0 ≤ d / (a + 7) := by
      rw [div_nonneg_iff] ; left
      exact ⟨hd, ha1⟩
    have leq1 : (7 / 64) ^ ((1 : ℝ) / 3) * (a / (b + 7)) ^ ((1 : ℝ) / 3) ≤
        1 / 3 * (7 / (b + 7) + a / (a + 7) + (a + 7) / 64) := by
      -- For each term, apply AM-GM inequality $$ \sqrt[3]{\frac{7}{64} \cdot \frac{x}{y+7}} \leq
      -- \frac{1}{3} \left( \frac{7}{y+7} + \frac{x}{x+7} + \frac{x+7}{64} \right).$$
      calc
        _ = (7 / (b + 7) * (a / (a + 7)) * ((a + 7) / 64)) ^ ((1 : ℝ) / 3) := by
          rw [← Real.mul_rpow (by norm_num) ha5]
          congr 1
          field_simp ; ring
        -- `KeyStep` : Rewrite the inequality like this then use the AM-GM inequality
        _ = (7 / (b + 7)) ^ ((1 : ℝ) / 3) * (a / (a + 7)) ^ ((1 : ℝ) / 3) * ((a + 7) / 64) ^ ((1 : ℝ) / 3) :=
          lem1 hb2 ha3 ha4
        _ ≤ 1 / 3 * (7 / (b + 7)) + 1 / 3 * (a / (a + 7)) + 1 / 3 * ((a + 7) / 64) := by
          refine Real.geom_mean_le_arith_mean3_weighted ?_ ?_ ?_ hb2 ha3 ha4 ?_ <;> norm_num
          -- apply AM-GM inequality
        _ = 1 / 3 * (7 / (b + 7) + a / (a + 7) + (a + 7) / 64) := by ring
    have leq2 : (7 / 64) ^ ((1 : ℝ) / 3) * (b / (c + 7)) ^ ((1 : ℝ) / 3) ≤
        1 / 3 * (7 / (c + 7) + b / (b + 7) + (b + 7) / 64) := by
      -- Similar to leq1
      calc
        _ = (7 / (c + 7) * (b / (b + 7)) * ((b + 7) / 64)) ^ ((1 : ℝ) / 3) := by
          rw [← Real.mul_rpow (by norm_num) hb5]
          congr 1
          field_simp ; ring
        _ = (7 / (c + 7)) ^ ((1 : ℝ) / 3) * (b / (b + 7)) ^ ((1 : ℝ) / 3) * ((b + 7) / 64) ^ ((1 : ℝ) / 3) :=
          lem1 hc2 hb3 hb4
        _ ≤ 1 / 3 * (7 / (c + 7)) + 1 / 3 * (b / (b + 7)) + 1 / 3 * ((b + 7) / 64) := by
          refine Real.geom_mean_le_arith_mean3_weighted ?_ ?_ ?_ hc2 hb3 hb4 ?_ <;> norm_num
        _ = 1 / 3 * (7 / (c + 7) + b / (b + 7) + (b + 7) / 64) := by ring
    have leq3 : (7 / 64) ^ ((1 : ℝ) / 3) * (c / (d + 7)) ^ ((1 : ℝ) / 3) ≤
        1 / 3 * (7 / (d + 7) + c / (c + 7) + (c + 7) / 64) := by
      -- Similar to leq1
      calc
        _ = ((7 / (d + 7)) * (c / (c + 7)) * ((c + 7) / 64)) ^ ((1 : ℝ) / 3) := by
          rw [← Real.mul_rpow (by norm_num) hc5]
          congr 1
          field_simp ; ring
        _ = (7 / (d + 7)) ^ ((1 : ℝ) / 3) * (c / (c + 7)) ^ ((1 : ℝ) / 3) * ((c + 7) / 64) ^ ((1 : ℝ) / 3) :=
          lem1 hd2 hc3 hc4
        _ ≤ 1 / 3 * (7 / (d + 7)) + 1 / 3 * (c / (c + 7)) + 1 / 3 * ((c + 7) / 64) := by
          refine Real.geom_mean_le_arith_mean3_weighted ?_ ?_ ?_ hd2 hc3 hc4 ?_ <;> norm_num
        _ = 1 / 3 * (7 / (d + 7) + c / (c + 7) + (c + 7) / 64) := by ring
    have leq4 : (7 / 64) ^ ((1 : ℝ) / 3) * (d / (a + 7)) ^ ((1 : ℝ) / 3) ≤
        1 / 3 * (7 / (a + 7) + d / (d + 7) + (d + 7) / 64) := by
      -- Similar to leq1
      calc
        _ = ((7 / (a + 7)) * (d / (d + 7)) * ((d + 7) / 64)) ^ ((1 : ℝ) / 3) := by
          rw [← Real.mul_rpow (by norm_num) hd5]
          congr 1
          field_simp ; ring
        _ = (7 / (a + 7)) ^ ((1 : ℝ) / 3) * (d / (d + 7)) ^ ((1 : ℝ) / 3) * ((d + 7) / 64) ^ ((1 : ℝ) / 3) :=
          lem1 ha2 hd3 hd4
        _ ≤ 1 / 3 * (7 / (a + 7)) + 1 / 3 * (d / (d + 7)) + 1 / 3 * ((d + 7) / 64) := by
          refine Real.geom_mean_le_arith_mean3_weighted ?_ ?_ ?_ ha2 hd3 hd4 ?_ <;> norm_num
        _ = 1 / 3 * (7 / (a + 7) + d / (d + 7) + (d + 7) / 64) := by ring
    have leq5 : (7 / 64) ^ ((1 : ℝ) / 3) * S ≤ 1 / 3 * (7 / (a + 7) + d / (d + 7) + (d + 7) / 64) +
        1 / 3 * (7 / (b + 7) + a / (a + 7) + (a + 7) / 64) +
        1 / 3 * (7 / (c + 7) + b / (b + 7) + (b + 7) / 64) +
        1 / 3 * (7 / (d + 7) + c / (c + 7) + (c + 7) / 64) := by
      -- Summing over all four terms
      rw [hS]
      linarith only [leq1, leq2, leq3, leq4]
    have eq1 : 1 / 3 * (7 / (a + 7) + d / (d + 7) + (d + 7) / 64) +
        1 / 3 * (7 / (b + 7) + a / (a + 7) + (a + 7) / 64) +
        1 / 3 * (7 / (c + 7) + b / (b + 7) + (b + 7) / 64) +
        1 / 3 * (7 / (d + 7) + c / (c + 7) + (c + 7) / 64)
        = 2 := by
      -- using \(a + b + c + d = 100\), the right-hand side simplifies to 2
      have sumeq : (a + 7) / 64 + (b + 7) / 64 + (c + 7) / 64 + (d + 7) / 64 = 128 / 64 := by
        calc
          _ = ((a + b + c + d) + 4 * 7) / 64 := by ring
          _ = 128 / 64 := by rw [hsum] ; norm_num
      have eqa : 7 / (a + 7) + a / (a + 7) = 1 := by
        field_simp ; rw [add_comm]
      have eqb : 7 / (b + 7) + b / (b + 7) = 1 := by
        field_simp ; rw [add_comm]
      have eqc : 7 / (c + 7) + c / (c + 7) = 1 := by
        field_simp ; rw [add_comm]
      have eqd : 7 / (d + 7) + d / (d + 7) = 1 := by
        field_simp ; rw [add_comm]
      calc
        _ = 1 / 3 * ((7 / (a + 7) + a / (a + 7)) + (7 / (b + 7) + b / (b + 7)) +
            (7 / (c + 7) + c / (c + 7)) + (7 / (d + 7) + d / (d + 7)) +
            ((a + 7) / 64 + (b + 7) / 64 + (c + 7) / 64 + (d + 7) / 64)) := by linarith only
        _ = 1 / 3 * (1 + 1 + 1 + 1 + 128 / 64) := by simp [sumeq, eqa, eqb, eqc, eqd]
        _ = 2 := by norm_num
    rw [eq1] at leq5
    clear* -leq5 lem0
    -- Thus, \$$\frac{7^{1/3}}{4} \cdot S \leq 2$.
    have eq2 : ((7 : ℝ) / 64) ^ ((1 : ℝ) / 3) = 7 ^ ((1 : ℝ) / 3) / 4 := by
      calc
        _ = ((7 : ℝ) / 4 ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by congr 1 ; norm_num
        _ = 7 ^ ((1 : ℝ) / 3) / 4 := by
          rw [Real.div_rpow (by norm_num) (by norm_num)]
          rw [lem0 (by norm_num)]
    rw [eq2] at leq5
    -- Show $S \leq \frac{8}{7^{1/3}}$ by leq5.
    rw [← mul_le_mul_left (a := 7 ^ ((1 : ℝ) / 3) / 4)]
    · apply leq5.trans
      simp
      norm_num
    · rw [div_pos_iff] ; left
      norm_num
      apply rpow_pos_of_pos
      norm_num
