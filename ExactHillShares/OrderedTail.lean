import ExactHillShares.OrderedPrefix
import ExactHillShares.Scaling

namespace ExactHillShares

/-- Corollary 4.5 for actual ordered rows, with the formula still explicitly
distinguished from the semantic Hill supremum. All prefix mass hypotheses
in the numerical kernel are discharged from order and strict crossing. -/
theorem ordered_numerical_tail (a : ℕ → ℝ) (m s q : ℕ)
    (hq : 2 ≤ q) (hanti : Antitone a) (hnonneg : ∀ i, 0 ≤ a i)
    (hsm : s < m)
    (hres : 0 < prefixCost a m - prefixCost a s)
    (hcross : numericalBound (q + 1) (prefixCost a m) (a 0) <
      prefixCost a (s + 1)) :
    numericalBound q (prefixCost a m - prefixCost a s) (a s) ≤
      numericalBound (q + 1) (prefixCost a m) (a 0) := by
  have hqne : q + 1 ≠ 2 := by omega
  let k := formulaIndex (q + 1) (prefixCost a m) (a 0)
  have hformula : numericalBound (q + 1) (prefixCost a m) (a 0) =
      envelope (q + 1) k (prefixCost a m) (a 0) := by
    simp [numericalBound, hqne, multiFormula, k]
  have hd : ((k : ℝ) + 1) * a 0 ≤
      numericalBound (q + 1) (prefixCost a m) (a 0) := by
    rw [hformula]
    exact le_envelope_left _ _ _ _
  have hprefix := crossing_removed_mass a k s _ hanti hnonneg hd hcross
  have hp := next_pos_of_residual_pos a s m hanti (Nat.le_of_lt hsm) hres
  have hpT := next_le_residual a s m hnonneg hsm
  have hC : 0 ≤ prefixCost a s := by
    unfold prefixCost
    exact Finset.sum_nonneg (fun i hi => hnonneg i)
  have hT : 0 < prefixCost a m := by linarith
  have hcross' : envelope (q + 1) k (prefixCost a m) (a 0) <
      prefixCost a s + a s := by
    simpa only [hformula, prefixCost_succ] using hcross
  rw [hformula]
  exact numericalBound_tail_scaled hq hT hp hpT (hanti (Nat.zero_le s)) hprefix hcross'

end ExactHillShares
