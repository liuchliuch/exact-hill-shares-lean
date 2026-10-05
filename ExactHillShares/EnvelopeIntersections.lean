import ExactHillShares.Formula

namespace ExactHillShares

/-- The branch-switch point stated immediately after Proposition 4.1. -/
theorem envelope_branch_intersection (q h : ℕ) (hq : 0 < q) :
    let x : ℝ := ((h : ℝ) + 2) / ((q : ℝ) * ((h : ℝ) + 1)^2 + (h : ℝ) + 2)
    ((h : ℝ) + 1) * x =
      (((h : ℝ) + 2) / ((q : ℝ) * ((h : ℝ) + 1))) * (1 - x) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  have hD : (0 : ℝ) < (q : ℝ) * ((h : ℝ) + 1)^2 + (h : ℝ) + 2 := by positivity
  dsimp only
  field_simp
  <;> ring

/-- Adjacent envelopes meet at the stated floor-interval boundary. -/
theorem envelope_adjacent_intersection (q h : ℕ) (hq : 0 < q) :
    envelope q h 1 (1 / ((q : ℝ) * ((h : ℝ) + 1) + 1)) =
      envelope q (h + 1) 1 (1 / ((q : ℝ) * ((h : ℝ) + 1) + 1)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (h : ℝ) + 2 := by positivity
  let D : ℝ := (q : ℝ) * ((h : ℝ) + 1) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have e1 : (((h : ℝ) + 2) / ((q : ℝ) * ((h : ℝ) + 1))) * (1 - 1 / D) =
      ((h : ℝ) + 2) / D := by
    dsimp [D]
    field_simp
    <;> ring
  have e2 : (((h : ℝ) + 3) / ((q : ℝ) * ((h : ℝ) + 2))) * (1 - 1 / D) =
      (((h : ℝ) + 3) * ((h : ℝ) + 1) / ((h : ℝ) + 2)) / D := by
    dsimp [D]
    field_simp
    <;> ring
  have hleft : ((h : ℝ) + 1) / D ≤ ((h : ℝ) + 2) / D :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hD)
  have hright : (((h : ℝ) + 3) * ((h : ℝ) + 1) / ((h : ℝ) + 2)) / D ≤
      ((h : ℝ) + 2) / D := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hD)
    apply (div_le_iff₀ h2).mpr
    nlinarith
  change envelope q h 1 (1 / D) = envelope q (h + 1) 1 (1 / D)
  unfold envelope
  push_cast
  have eh : (h : ℝ) + 1 + 1 = (h : ℝ) + 2 := by ring
  have eh' : (h : ℝ) + 1 + 2 = (h : ℝ) + 3 := by ring
  rw [eh, eh', e1, e2]
  simp only [mul_one_div]
  rw [max_eq_right hleft, max_eq_left hright]

end ExactHillShares
