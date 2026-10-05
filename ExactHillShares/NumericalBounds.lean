import ExactHillShares.TailDomination

namespace ExactHillShares

/-- Every maximum item is a lower bound on the formula. -/
theorem le_multiFormula_max {q : ℕ} {T p : ℝ} (hp : 0 ≤ p) :
    p ≤ multiFormula q T p := by
  have hk : (0 : ℝ) ≤ formulaIndex q T p := Nat.cast_nonneg _
  have hi := le_envelope_left q (formulaIndex q T p) T p
  change _ ≤ multiFormula q T p at hi
  nlinarith [mul_nonneg hk hp]

/-- A q≥2 envelope is at least the average total load. -/
theorem total_div_le_envelope {q : ℕ} (hq : 2 ≤ q)
    {T : ℝ} (hT : 0 < T) (k : ℕ) (p : ℝ) :
    T / q ≤ envelope q k T p := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hD : 0 < (q : ℝ) * ((k : ℝ) + 1) ^ 2 + (k : ℝ) + 2 := by positivity
  have hratio : (1 : ℝ) / q ≤ (((k : ℝ) + 1) * ((k : ℝ) + 2)) /
      ((q : ℝ) * ((k : ℝ) + 1) ^ 2 + (k : ℝ) + 2) := by
    apply (div_le_div_iff₀ hq0 hD).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ (q : ℝ) - 1) hk]
  have hnorm := le_trans hratio (envelope_minimum (by omega : 0 < q) k (p / T))
  have hs := mul_le_mul_of_nonneg_left hnorm (le_of_lt hT)
  rw [envelope_normalize hT] at hs
  simpa only [mul_one_div] using hs

/-- The numerical formula is at least the average load. -/
theorem total_div_le_multiFormula {q : ℕ} (hq : 2 ≤ q)
    {T p : ℝ} (hT : 0 < T) : T / q ≤ multiFormula q T p :=
  total_div_le_envelope hq hT _ _

/-- Removing at least one item is possible unless the whole mass is one item. -/
theorem multiFormula_lt_total {q : ℕ} (hq : 2 ≤ q) {T p : ℝ}
    (hp : 0 < p) (hpT : p < T) : multiFormula q T p < T := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  apply lt_of_le_of_lt (multiFormula_le_average (by omega) hp (le_of_lt hpT))
  apply (div_lt_iff₀ hq0).mpr
  nlinarith [mul_pos (by linarith : 0 < (q : ℝ) - 1) (sub_pos.mpr hpT)]

@[simp] theorem multiFormula_single_item (q : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    multiFormula q T T = T := by
  simp [multiFormula, formulaIndex, envelope, max_eq_left hT]

theorem le_twoFormula_max {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    x ≤ twoFormula x := by
  unfold twoFormula
  split_ifs with h1 h2 h3 h4
  · exact le_max_left _ _
  · linarith
  · linarith
  · linarith
  · exact le_multiFormula_max (le_of_lt hx)

theorem half_le_twoFormula {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (1 : ℝ) / 2 ≤ twoFormula x := by
  unfold twoFormula
  split_ifs with h1 h2 h3 h4
  · have ha := le_max_left x (1 - x)
    have hb := le_max_right x (1 - x)
    linarith
  · linarith
  · linarith
  · linarith
  · simpa using (total_div_le_multiFormula (q := 2) (p := x) (by norm_num) (by norm_num : (0 : ℝ) < 1))

/-- A lower bound for the low-maximum branch used in Lemma 5.1. -/
theorem envelope_two_width {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    x / 2 ≤ 2 * envelope 2 k 1 x - 1 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨ha, hb⟩ := (envelope_le_iff (by norm_num : 0 < (2 : ℕ))).mp
    (le_refl (envelope 2 k 1 x))
  norm_num at hb
  have hmul := mul_nonneg (by linarith : 0 ≤ (k : ℝ) - 2) hx
  nlinarith

/-- Lemma 5.1: the exact-formula feasible interval has linear width. -/
theorem twoFormula_width {x : ℝ} (hx : 0 < x) (hxthird : x ≤ 1 / 3) :
    (3 / 7 : ℝ) * x ≤ 2 * twoFormula x - 1 := by
  unfold twoFormula
  split_ifs with h1 h2 h3 h4
  · have heq : x = 1 / 3 := le_antisymm hxthird h1
    subst x
    norm_num
  · linarith
  · linarith
  · linarith
  · have hsmall : x < 1 / 5 := lt_of_not_ge h4
    have hindex : 2 ≤ formulaIndex 2 1 x := by
      apply (Nat.le_floor_iff (div_nonneg (by linarith : 0 ≤ 1 - x) (by positivity : 0 ≤ (2 : ℝ) * x))).mpr
      apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) * x)).mpr
      norm_num
      linarith
    have hw := envelope_two_width hindex (le_of_lt hx)
    change x / 2 ≤ 2 * multiFormula 2 1 x - 1 at hw
    linarith

/-- The scaled form of Lemma 5.1. -/
theorem twoFormula_scaled_width {T p : ℝ} (hT : 0 < T) (hp : 0 < p)
    (hpT : p / T ≤ 1 / 3) :
    (3 / 7 : ℝ) * p ≤ 2 * (T * twoFormula (p / T)) - T := by
  have hw := mul_le_mul_of_nonneg_left (twoFormula_width (div_pos hp hT) hpT) (le_of_lt hT)
  have heq : T * ((3 / 7 : ℝ) * (p / T)) = (3 / 7 : ℝ) * p := by field_simp; ring
  rw [heq] at hw
  nlinarith

end ExactHillShares
