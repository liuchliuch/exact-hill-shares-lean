import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp


/-! Numerical functions appearing in Section 4 of the manuscript.
These definitions do not identify the functions with a worst-case MMS supremum;
that identification is a separate theorem. -/
namespace ExactHillShares
noncomputable section

/-- The two affine branches of the integer-indexed upper envelope. -/
def envelope (q h : ℕ) (T p : ℝ) : ℝ :=
  max (((h : ℝ) + 1) * p)
    ((((h : ℝ) + 2) / ((q : ℝ) * ((h : ℝ) + 1))) * (T - p))

/-- The interval index in the exact formula. -/
def formulaIndex (q : ℕ) (T p : ℝ) : ℕ :=
  ⌊(T - p) / ((q : ℝ) * p)⌋₊

/-- The formula of Proposition 4.1 (before its semantic identification). -/
def multiFormula (q : ℕ) (T p : ℝ) : ℝ :=
  envelope q (formulaIndex q T p) T p

/-- The exceptional two-agent formula of Proposition 4.2, on normalized inputs. -/
def twoFormula (x : ℝ) : ℝ :=
  if 1 / 3 ≤ x then max x (1 - x)
  else if 2 / 7 ≤ x then 2 * x
  else if 7 / 27 ≤ x then (2 + 3 * x) / 5
  else if 1 / 5 ≤ x then 3 * (1 - x) / 4
  else multiFormula 2 1 x

/-- A unified, homogeneous numerical formula for all agent counts at least two. -/
def numericalBound (q : ℕ) (T p : ℝ) : ℝ :=
  if q = 2 then T * twoFormula (p / T) else multiFormula q T p

lemma le_envelope_left (q h : ℕ) (T p : ℝ) :
    ((h : ℝ) + 1) * p ≤ envelope q h T p := le_max_left _ _

lemma le_envelope_right (q h : ℕ) (T p : ℝ) :
    (((h : ℝ) + 2) / ((q : ℝ) * ((h : ℝ) + 1))) * (T - p) ≤
      envelope q h T p := le_max_right _ _

/-- Clearing the positive denominator separates the two obstructions. -/
lemma envelope_le_iff {q h : ℕ} {T p d : ℝ} (hq : 0 < q) :
    envelope q h T p ≤ d ↔
      ((h : ℝ) + 1) * p ≤ d ∧
      ((h : ℝ) + 2) * (T - p) ≤ d * ((q : ℝ) * ((h : ℝ) + 1)) := by
  have hden : 0 < (q : ℝ) * ((h : ℝ) + 1) := by positivity
  unfold envelope
  rw [max_le_iff, div_mul_eq_mul_div, div_le_iff₀ hden]

lemma formulaIndex_bounds {q : ℕ} {T p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hpT : p ≤ T) :
    (formulaIndex q T p : ℝ) * ((q : ℝ) * p) ≤ T - p ∧
    T - p < ((formulaIndex q T p : ℝ) + 1) * ((q : ℝ) * p) := by
  have hden : 0 < (q : ℝ) * p := by positivity
  constructor
  · exact (le_div_iff₀ hden).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr hpT) (le_of_lt hden)))
  · exact (div_lt_iff₀ hden).mp (Nat.lt_floor_add_one _)

/-- Every indexed envelope dominates the floor-indexed formula (equation 4).
The assertion is purely algebraic and is valid for every positive agent count. -/
theorem multiFormula_le_envelope {q : ℕ} {T p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hpT : p ≤ T) (h : ℕ) :
    multiFormula q T p ≤ envelope q h T p := by
  let k := formulaIndex q T p
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hdenK : 0 < (q : ℝ) * ((k : ℝ) + 1) := by positivity
  have hdenH : 0 < (q : ℝ) * ((h : ℝ) + 1) := by positivity
  obtain ⟨hlo, hhi⟩ := formulaIndex_bounds hq hp hpT
  change (k : ℝ) * ((q : ℝ) * p) ≤ T - p at hlo
  change T - p < ((k : ℝ) + 1) * ((q : ℝ) * p) at hhi
  change envelope q k T p ≤ envelope q h T p
  rcases lt_trichotomy h k with hhk | heq | hkh
  · have hhkR : (h : ℝ) + 1 ≤ k := by exact_mod_cast hhk
    apply (envelope_le_iff hq).mpr
    have hright := le_envelope_right q h T p
    rw [div_mul_eq_mul_div] at hright
    have hright' := (div_le_iff₀ hdenH).mp hright
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ (h : ℝ) + 2)
      have hgap := mul_nonneg (by nlinarith : 0 ≤ (k : ℝ) - (h : ℝ) - 1)
        (le_of_lt (mul_pos hq0 hp))
      have : (((k : ℝ) + 1) * p) * ((q : ℝ) * ((h : ℝ) + 1)) ≤
          envelope q h T p * ((q : ℝ) * ((h : ℝ) + 1)) := by nlinarith
      exact (mul_le_mul_right hdenH).mp this
    · have hmass : 0 ≤ T - p := sub_nonneg.mpr hpT
      have hratio : ((k : ℝ) + 2) / ((q : ℝ) * ((k : ℝ) + 1)) ≤
          ((h : ℝ) + 2) / ((q : ℝ) * ((h : ℝ) + 1)) := by
        apply (div_le_div_iff₀ hdenK hdenH).mpr
        nlinarith [mul_nonneg (le_of_lt hq0) (by nlinarith : 0 ≤ (k : ℝ) - h)]
      have hs := le_trans (mul_le_mul_of_nonneg_right hratio hmass)
        (le_envelope_right q h T p)
      rw [div_mul_eq_mul_div] at hs
      exact (div_le_iff₀ hdenK).mp hs
  · subst h
    exact le_rfl
  · have hkhR : (k : ℝ) + 1 ≤ h := by exact_mod_cast hkh
    apply (envelope_le_iff hq).mpr
    have hleft := le_envelope_left q h T p
    constructor
    · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hp)) hleft
    · have hmul := mul_le_mul_of_nonneg_left (le_of_lt hhi)
        (by positivity : 0 ≤ (k : ℝ) + 2)
      have hlarge : ((k : ℝ) + 2) * p ≤ envelope q h T p := by
        exact le_trans (mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hp)) hleft
      have hlarge' := mul_le_mul_of_nonneg_right hlarge (le_of_lt hdenK)
      nlinarith

/-- The usual greedy-balancing upper bound also holds for the numerical formula. -/
theorem multiFormula_le_average {q : ℕ} {T p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hpT : p ≤ T) :
    multiFormula q T p ≤ (T + ((q : ℝ) - 1) * p) / q := by
  let k := formulaIndex q T p
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  obtain ⟨hlo, hhi⟩ := formulaIndex_bounds hq hp hpT
  change (k : ℝ) * ((q : ℝ) * p) ≤ T - p at hlo
  change T - p < ((k : ℝ) + 1) * ((q : ℝ) * p) at hhi
  change envelope q k T p ≤ _
  apply (envelope_le_iff hq).mpr
  constructor
  · apply (le_div_iff₀ hq0).mpr
    nlinarith
  · have heq : ((T + ((q : ℝ) - 1) * p) / q) *
        ((q : ℝ) * ((k : ℝ) + 1)) =
        (T + ((q : ℝ) - 1) * p) * ((k : ℝ) + 1) := by
      field_simp
      ring
    rw [heq]
    nlinarith

/-- Appendix B, equation 13, including every exceptional interval. -/
theorem twoFormula_le_envelope {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (h : ℕ) (hh : 2 ≤ h) :
    twoFormula x ≤ envelope 2 h 1 x := by
  have hhR : (3 : ℝ) ≤ (h : ℝ) + 1 := by exact_mod_cast (show 3 ≤ h + 1 by omega)
  have hthree : 3 * x ≤ envelope 2 h 1 x :=
    le_trans (mul_le_mul_of_nonneg_right hhR (le_of_lt hx)) (le_envelope_left 2 h 1 x)
  unfold twoFormula
  split_ifs with h1 h2 h3 h4
  · exact le_trans (max_le (by linarith) (by linarith)) hthree
  · exact le_trans (by linarith) hthree
  · exact le_trans (by linarith) hthree
  · exact le_trans (by linarith) hthree
  · exact multiFormula_le_envelope (by norm_num) hx hx1 h

/-- The two-agent formula never exceeds the greedy two-bin upper bound. -/
theorem twoFormula_le_average {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    twoFormula x ≤ (1 + x) / 2 := by
  unfold twoFormula
  split_ifs with h1 h2 h3 h4
  · exact max_le (by linarith) (by linarith)
  · linarith
  · linarith
  · linarith
  · simpa only [Nat.cast_ofNat, sub_self, sub_zero, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using (multiFormula_le_average (q := 2) (T := 1) (by norm_num) hx hx1)

/-- The envelope is homogeneous under normalization of the instance. -/
lemma envelope_normalize {T : ℝ} (hT : 0 < T) (q h : ℕ) (p : ℝ) :
    T * envelope q h 1 (p / T) = envelope q h T p := by
  unfold envelope
  rw [mul_max_of_nonneg _ _ (le_of_lt hT)]
  congr 1
  · field_simp
  · have hn : T * (1 - p / T) = T - p := by field_simp
    calc
      T * (((↑h + 2) / (↑q * (↑h + 1))) * (1 - p / T)) =
          ((↑h + 2) / (↑q * (↑h + 1))) * (T * (1 - p / T)) := by ring
      _ = _ := by rw [hn]

/-- Scaled form of the Appendix B envelope comparison. -/
theorem twoFormula_scaled_le_envelope {T p : ℝ} (hT : 0 < T)
    (hp : 0 < p) (hpT : p ≤ T) (h : ℕ) (hh : 2 ≤ h) :
    T * twoFormula (p / T) ≤ envelope 2 h T p := by
  have hx : 0 < p / T := div_pos hp hT
  have hx1 : p / T ≤ 1 := (div_le_one hT).mpr hpT
  have hs := mul_le_mul_of_nonneg_left (twoFormula_le_envelope hx hx1 h hh) (le_of_lt hT)
  rwa [envelope_normalize hT] at hs

/-- Scaled universal two-bin balancing envelope. -/
theorem twoFormula_scaled_le_average {T p : ℝ} (hT : 0 < T)
    (hp : 0 < p) (hpT : p ≤ T) :
    T * twoFormula (p / T) ≤ (T + p) / 2 := by
  have hs := mul_le_mul_of_nonneg_left
    (twoFormula_le_average (div_pos hp hT) ((div_le_one hT).mpr hpT)) (le_of_lt hT)
  convert hs using 1 <;> field_simp <;> ring

end
end ExactHillShares
