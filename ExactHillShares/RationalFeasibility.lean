import ExactHillShares.Foundations
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order

namespace ExactHillShares

/-- Transfer the genuine real-valued minimax existence theorem to an exact
rational Boolean subset. The algorithm need not compute this witness. -/
theorem rational_feasible_of_hillBound {k : ℕ} (c : Fin k → ℚ)
    {T p D : ℚ} (hT : 0 < T)
    (hc : ∀ j, 0 ≤ c j ∧ c j ≤ p) (hsum : (∑ j, c j) = T)
    (hp : ∃ j, c j = p)
    (hbound : hillBound 2 (T : ℝ) (p : ℝ) ≤ (D : ℝ)) :
    ∃ b : Fin k → Bool,
      T - D ≤ (∑ j, if b j then c j else 0) ∧
        (∑ j, if b j then c j else 0) ≤ D := by
  classical
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hcR : ∀ j, 0 ≤ (c j : ℝ) ∧ (c j : ℝ) ≤ (p : ℝ) := by
    intro j
    exact_mod_cast hc j
  have hsumR : (∑ j, (c j : ℝ)) = (T : ℝ) := by exact_mod_cast hsum
  have hpR : ∃ j, (c j : ℝ) = (p : ℝ) := by
    obtain ⟨j, hj⟩ := hp
    exact ⟨j, by exact_mod_cast hj⟩
  have hm := (mms_le_hillBound (n := 2) (by decide) hTR hcR hsumR hpR).trans hbound
  obtain ⟨a, ha⟩ := (mms_le_iff (by decide : 0 < (2 : ℕ)) (fun j => (c j : ℝ)) D).mp hm
  let b : Fin k → Bool := fun j => decide (a j = 0)
  have hselected : ((∑ j, if b j then c j else 0 : ℚ) : ℝ) =
      load (fun j => (c j : ℝ)) a 0 := by
    simp only [Rat.cast_sum, load, b, decide_eq_true_eq]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  have hboth := sum_load (fun j => (c j : ℝ)) a
  rw [Fin.sum_univ_two, hsumR] at hboth
  have hzero := ha 0
  have hone := ha 1
  have hupper : ((∑ j, if b j then c j else 0 : ℚ) : ℝ) ≤ (D : ℝ) := by
    rw [hselected]
    exact hzero
  have hlower : (T : ℝ) - D ≤ ((∑ j, if b j then c j else 0 : ℚ) : ℝ) := by
    rw [hselected]
    linarith
  refine ⟨b, ?_, ?_⟩
  · exact_mod_cast hlower
  · exact_mod_cast hupper

end ExactHillShares
