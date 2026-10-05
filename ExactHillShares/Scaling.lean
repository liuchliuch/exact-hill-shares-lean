import ExactHillShares.NumericalBounds

namespace ExactHillShares

/-- Positive normalization preserves the floor interval index. -/
theorem formulaIndex_normalize {q : ℕ} {T p : ℝ}
    (hq : 0 < q) (hT : 0 < T) (hp : 0 < p) :
    formulaIndex q 1 (p / T) = formulaIndex q T p := by
  unfold formulaIndex
  congr 1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  field_simp

/-- Homogeneity of the multi-agent numerical formula. -/
theorem multiFormula_normalize {q : ℕ} {T p : ℝ}
    (hq : 0 < q) (hT : 0 < T) (hp : 0 < p) :
    T * multiFormula q 1 (p / T) = multiFormula q T p := by
  unfold multiFormula
  rw [formulaIndex_normalize hq hT hp, envelope_normalize hT]

/-- Homogeneity of the unified formula. -/
theorem numericalBound_normalize {q : ℕ} {T p : ℝ}
    (hq : 0 < q) (hT : 0 < T) (hp : 0 < p) :
    T * numericalBound q 1 (p / T) = numericalBound q T p := by
  unfold numericalBound
  split_ifs with hq2
  · simp
  · exact multiFormula_normalize hq hT hp

/-- Formula under a positive change of units. -/
theorem numericalBound_scale {q : ℕ} {t T p : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hT : 0 < T) (hp : 0 < p) :
    numericalBound q (t * T) (t * p) = t * numericalBound q T p := by
  rw [← numericalBound_normalize hq (mul_pos ht hT) (mul_pos ht hp),
    ← numericalBound_normalize hq hT hp]
  have hr : t * p / (t * T) = p / T := by field_simp; ring
  rw [hr]
  ring

/-- Normalized tail domination expressed using the single all-counts formula. -/
theorem numericalBound_tail_normalized {q k : ℕ} {a C p : ℝ}
    (hq : 2 ≤ q) (hp : 0 < p) (hpT : p ≤ 1 - C)
    (hpa : p ≤ a) (hprefix : a + (k : ℝ) * p ≤ C)
    (hcross : envelope (q + 1) k 1 a < C + p) :
    numericalBound q (1 - C) p ≤ envelope (q + 1) k 1 a := by
  by_cases hq2 : q = 2
  · subst q
    simpa [numericalBound] using twoFormula_tail_domination hp hpT hpa hprefix hcross
  · simpa [numericalBound, hq2] using
      multiFormula_tail_domination (by omega : 3 ≤ q) hp hpT hpa hprefix hcross

/-- Corollary 4.5 in numerical form, before the ordered-prefix and semantic bridges.
The conclusion concerns the universal formula for every tail with these total
and maximum values, rather than merely the particular remaining sequence. -/
theorem numericalBound_tail_scaled {q k : ℕ} {T a C p : ℝ}
    (hq : 2 ≤ q) (hT : 0 < T) (hp : 0 < p) (hpT : p ≤ T - C)
    (hpa : p ≤ a) (hprefix : a + (k : ℝ) * p ≤ C)
    (hcross : envelope (q + 1) k T a < C + p) :
    numericalBound q (T - C) p ≤ envelope (q + 1) k T a := by
  have hq0 : 0 < q := by omega
  have htail : 0 < T - C := lt_of_lt_of_le hp hpT
  have hp' : 0 < p / T := div_pos hp hT
  have hT' : 0 < 1 - C / T := by
    have : C < T := by linarith
    have : C / T < 1 := (div_lt_one hT).mpr this
    linarith
  have hpa' : p / T ≤ a / T := (div_le_div_iff_of_pos_right hT).mpr hpa
  have hpT' : p / T ≤ 1 - C / T := by
    have hh := (div_le_div_iff_of_pos_right hT).mpr hpT
    have heq : (T - C) / T = 1 - C / T := by field_simp
    rwa [heq] at hh
  have hprefix' : a / T + (k : ℝ) * (p / T) ≤ C / T := by
    have hh := (div_le_div_iff_of_pos_right hT).mpr hprefix
    convert hh using 1 <;> ring
  have hcross' : envelope (q + 1) k 1 (a / T) < C / T + p / T := by
    have hh := (div_lt_div_iff_of_pos_right hT).mpr hcross
    have heq : envelope (q + 1) k T a / T = envelope (q + 1) k 1 (a / T) := by
      rw [← envelope_normalize hT]
      field_simp
    rw [heq] at hh
    convert hh using 1 <;> ring
  have hs := mul_le_mul_of_nonneg_left
    (numericalBound_tail_normalized hq hp' hpT' hpa' hprefix' hcross') (le_of_lt hT)
  rw [envelope_normalize hT] at hs
  have heq : T * numericalBound q (1 - C / T) (p / T) = numericalBound q (T - C) p := by
    rw [← numericalBound_scale hq0 hT hT' hp']
    congr 1 <;> field_simp
  rwa [heq] at hs

end ExactHillShares
