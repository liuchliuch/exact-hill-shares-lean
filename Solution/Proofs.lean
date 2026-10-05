import Challenge.Definitions
import ExactHillShares

/-! Bridges from the implementation to independently written paper contracts.
This module does not import the expected theorem placeholders. -/
namespace PaperContract
noncomputable section
open scoped BigOperators

private theorem exactMaximum_iff {m : ℕ} (c : Fin m → ℝ) (a : ℝ) :
    exactMaximum m c a ↔ ExactHillShares.IsNormalizedExact c a := by
  constructor
  · rintro ⟨hn, hs, hu, ha⟩
    exact ⟨fun j => ⟨hn j, hu j⟩, hs, ha⟩
  · rintro ⟨h, hs, ha⟩
    exact ⟨fun j => (h j).1, hs, fun j => (h j).2, ha⟩

private theorem exactShare_eq (n : ℕ) (a : ℝ) :
    exactShare n a = ExactHillShares.hill n a := by
  unfold exactShare ExactHillShares.hill ExactHillShares.hillValues
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, exactMaximum_iff]
  constructor
  · rintro ⟨m, c, hc, hz⟩
    exact ⟨m, c, hc, hz.symm⟩
  · rintro ⟨m, c, hc, hz⟩
    exact ⟨m, c, hc, hz.symm⟩

private theorem ordinaryFormula_eq (n : ℕ) (a : ℝ) :
    ordinaryFormula n a = ExactHillShares.multiFormula n 1 a := by
  unfold ordinaryFormula ExactHillShares.multiFormula ExactHillShares.envelope
    ExactHillShares.formulaIndex
  rw [div_mul_eq_mul_div]

private theorem twoFormula_eq (a : ℝ) :
    twoFormula a = ExactHillShares.twoFormula a := by
  simp only [twoFormula, ExactHillShares.twoFormula, ordinaryFormula_eq]

private theorem formula_eq (n : ℕ) (a : ℝ) :
    formula n a = ExactHillShares.numericalBound n 1 a := by
  simp [formula, ExactHillShares.numericalBound, twoFormula_eq, ordinaryFormula_eq]

theorem exact_share_formula : SupremumFormula := by
  intro n hn a ha ha1
  rw [exactShare_eq, formula_eq]
  exact ExactHillShares.hill_eq_numericalBound hn ha ha1

theorem feasible_interval_width : FeasibleIntervalWidth := by
  intro a ha ha3
  rw [exactShare_eq, ExactHillShares.hill_eq_twoFormula ha (by linarith)]
  exact ExactHillShares.twoFormula_width ha ha3

theorem ordered_tail_domination : OrderedTailDomination := by
  intro n m s hn hsm c hanti hnonneg htotal hcross hres
  change ExactHillShares.prefixCost c m = 1 at htotal
  rw [exactShare_eq] at hcross
  change ExactHillShares.hill n (c 0) < ExactHillShares.prefixCost c (s + 1) at hcross
  change 0 < 1 - ExactHillShares.prefixCost c s at hres
  have hres' : 0 < ExactHillShares.prefixCost c m - ExactHillShares.prefixCost c s := by
    simpa only [htotal] using hres
  have hp := ExactHillShares.next_pos_of_residual_pos c s m hanti (by omega) hres'
  have hpT := ExactHillShares.next_le_residual c s m hnonneg hsm
  rw [htotal] at hpT
  have hhead : 0 < c 0 := hp.trans_le (hanti (Nat.zero_le s))
  have hhead1 : c 0 ≤ 1 := by
    have h := ExactHillShares.next_le_residual c 0 m hnonneg (by omega)
    rw [htotal] at h
    simpa [ExactHillShares.prefixCost] using h
  rw [ExactHillShares.hill_eq_numericalBound (by omega) hhead hhead1] at hcross
  have h := ExactHillShares.ordered_numerical_tail c m s (n - 1)
    (by omega) hanti hnonneg hsm hres' (by simpa [htotal, Nat.sub_add_cancel (by omega : 1 ≤ n)] using hcross)
  rw [htotal, Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
  rw [← ExactHillShares.hillBound_eq_numericalBound (by omega) hres hp hpT,
    ← ExactHillShares.hill_eq_numericalBound (by omega) hhead hhead1] at h
  simpa only [exactShare_eq, prefixMass, ExactHillShares.prefixCost,
    ExactHillShares.hillBound] using h

theorem simultaneous_guarantee : RealExistence := by
  intro n m hn c a hc
  obtain ⟨owner, howner⟩ := ExactHillShares.simultaneous_hill_allocation hn c a
    (fun i => (exactMaximum_iff _ _).mp (hc i))
  refine ⟨owner, fun i => ?_⟩
  rw [exactShare_eq]
  exact howner i

/-- Adapt the actual output-only vector program to the independently specified
optional-owner interface. The impossible zero-agent case returns failure. -/
def allocate : RationalAllocator := fun n _m c =>
  if hn : 0 < n then
    (ExactHillShares.Algorithm.allocatePaper hn c).map ExactHillShares.PointerLift.read
  else none

theorem rational_allocator_correct : RationalCorrectness allocate := by
  intro n m hn c a hc
  obtain ⟨out, hout, hs⟩ := ExactHillShares.Algorithm.allocatePaper_hill_safe hn c a
    (fun i => (exactMaximum_iff _ _).mp (hc i))
  refine ⟨ExactHillShares.PointerLift.read out, ?_, fun i => ?_⟩
  · simp [allocate, show 0 < n by omega, hout]
  · rw [exactShare_eq]
    exact hs i

end
end PaperContract
