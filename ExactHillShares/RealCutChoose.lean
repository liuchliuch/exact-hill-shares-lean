import ExactHillShares.Foundations
import Mathlib.Tactic.FinCases

/-!
# Two-agent cut-and-choose for real-valued additive costs

The first agent cuts at an attained two-bin minimax partition, and the second
agent chooses a bin of cost at most half of its total. Neither valuation needs
to be nonnegative.
-/

open scoped BigOperators

namespace ExactHillShares

/-- Two-agent cut-and-choose, with an MMS bound for the cutter and an average
bound for the chooser. This is valid for arbitrary real-valued item costs. -/
theorem real_cut_choose {m : ℕ} (v w : Fin m → ℝ) (dv dw : ℝ)
    (hv : mms 2 v ≤ dv) (hw : (∑ j, w j) / 2 ≤ dw) :
    ∃ a : Fin m → Fin 2, load v a 0 ≤ dv ∧ load w a 1 ≤ dw := by
  classical
  obtain ⟨a, ha⟩ := (mms_le_iff (by decide : 0 < 2) v dv).1 hv
  have hsum : load w a 0 + load w a 1 = ∑ j, w j := by
    simpa only [Fin.sum_univ_two] using sum_load w a
  by_cases hchoice : load w a 1 ≤ dw
  · exact ⟨a, ha 0, hchoice⟩
  · have hother : load w a 0 ≤ dw := by linarith
    let b : Fin m → Fin 2 := fun j => if a j = 0 then 1 else 0
    have hswap (u : Fin m → ℝ) :
        load u b 0 = load u a 1 ∧ load u b 1 = load u a 0 := by
      constructor <;> unfold load <;> apply Finset.sum_congr rfl <;> intro j _
      · dsimp only [b]
        generalize a j = k
        fin_cases k <;> simp
      · dsimp only [b]
        generalize a j = k
        fin_cases k <;> simp
    exact ⟨b, (hswap v).1.trans_le (ha 1), (hswap w).2.trans_le hother⟩

end ExactHillShares
