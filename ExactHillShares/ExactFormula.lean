import ExactHillShares.ExactFormulaUpper
import ExactHillShares.ExactFormulaLower
import ExactHillShares.SubsetSelection
import ExactHillShares.Scaling
import ExactHillShares.ExactFormulaTwo

/-!
# The semantic exact Hill formula

The equalities in this file identify the genuine supremum `hill` with the closed
form. Their upper bounds use finite exchange-stable allocations and proved subset
selection; their lower bounds use explicit normalized finite extremal instances.
-/

namespace ExactHillShares

/-- An unconditional upper envelope in every nonexceptional positive-index case. -/
theorem mms_le_envelope {m n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    (hnk : k + 2 ≤ n * k) {v : Fin m → ℝ} {α : ℝ}
    (hα : 0 < α) (hv : IsNormalizedExact v α) :
    mms n v ≤ envelope n k 1 α := by
  apply mms_le_envelope_of_selection hn hk hnk hα hv
  intro S hS hM hsmall
  exact subset_selection_claim5 S v α k hα hk hM hS (fun _ => hsmall)

/-- The finite packing upper bound for three or more bins. -/
theorem mms_le_multiFormula {m n : ℕ} (hn : 3 ≤ n) {v : Fin m → ℝ} {α : ℝ}
    (hα : 0 < α) (hv : IsNormalizedExact v α) : mms n v ≤ multiFormula n 1 α := by
  unfold multiFormula
  by_cases hk0 : formulaIndex n 1 α = 0
  · rw [hk0]
    exact mms_le_envelope_zero (by omega) hα hv
  · have hk : 1 ≤ formulaIndex n 1 α := by omega
    have hprod := Nat.mul_le_mul_right (formulaIndex n 1 α) hn
    apply mms_le_envelope (by omega) hk (by omega) hα hv

/-- Proposition 4.1 at unit total mass, with a genuine supremum on the left. -/
theorem hill_eq_multiFormula {n : ℕ} (hn : 3 ≤ n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) : hill n α = multiFormula n 1 α := by
  apply le_antisymm
  · apply (hill_le_iff (by omega) hα hα1 _).2
    intro m v hv
    exact mms_le_multiFormula hn hα hv
  · exact multiFormula_le_hill (by omega) hα hα1

/-- Proposition 4.1 with arbitrary positive total mass. -/
theorem hillBound_eq_multiFormula {n : ℕ} (hn : 3 ≤ n) {T p : ℝ}
    (hT : 0 < T) (hp : 0 < p) (hpT : p ≤ T) :
    hillBound n T p = multiFormula n T p := by
  unfold hillBound
  rw [hill_eq_multiFormula hn (div_pos hp hT) ((div_le_one hT).2 hpT)]
  exact multiFormula_normalize (by omega) hT hp

/-- The two-agent formula below the exceptional interval. -/
theorem hill_two_eq_multiFormula_of_le_fifth {α : ℝ}
    (hα : 0 < α) (hα5 : α ≤ 1 / 5) : hill 2 α = multiFormula 2 1 α := by
  have hα1 : α ≤ 1 := by linarith
  apply le_antisymm
  · apply (hill_le_iff (by omega) hα hα1 _).2
    intro m v hv
    have hk : 2 ≤ formulaIndex 2 1 α := by
      apply Nat.le_floor
      apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) * α)).2
      norm_num
      linarith
    exact mms_le_envelope (by omega) (by omega) (by omega) hα hv
  · exact multiFormula_le_hill (by omega) hα hα1

/-- The two-agent formula above the exceptional interval. -/
theorem hill_two_eq_max_of_third_le {α : ℝ}
    (hα3 : 1 / 3 ≤ α) (hα1 : α ≤ 1) : hill 2 α = max α (1 - α) := by
  have hα : 0 < α := by linarith
  apply le_antisymm
  · apply (hill_le_iff (by omega) hα hα1 _).2
    intro m v hv
    simpa [envelope] using mms_le_envelope_zero (n := 2) (by omega) hα hv
  · have hh := twoFormula_le_hill hα hα1
    rw [twoFormula, if_pos hα3] at hh
    exact hh

/-- Proposition 4.2, identifying all five branches with the genuine supremum. -/
theorem hill_eq_twoFormula {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    hill 2 α = twoFormula α := by
  apply le_antisymm
  · by_cases hα3 : 1 / 3 ≤ α
    · rw [hill_two_eq_max_of_third_le hα3 hα1, twoFormula, if_pos hα3]
    · by_cases hα5 : 1 / 5 ≤ α
      · apply (hill_le_iff (by omega) hα hα1 _).2
        intro m v hv
        exact mms_le_twoFormula_exceptional hα5 (le_of_lt (lt_of_not_ge hα3)) hv
      · rw [hill_two_eq_multiFormula_of_le_fifth hα (le_of_lt (lt_of_not_ge hα5))]
        rw [twoFormula, if_neg hα3, if_neg (by linarith : ¬ (2 / 7 : ℝ) ≤ α),
          if_neg (by linarith : ¬ (7 / 27 : ℝ) ≤ α), if_neg hα5]
  · exact twoFormula_le_hill hα hα1

/-- The unified formula agrees with the homogeneous semantic Hill bound. -/
theorem hillBound_eq_numericalBound {n : ℕ} (hn : 2 ≤ n) {T p : ℝ}
    (hT : 0 < T) (hp : 0 < p) (hpT : p ≤ T) :
    hillBound n T p = numericalBound n T p := by
  by_cases hn2 : n = 2
  · subst n
    change T * hill 2 (p / T) = T * twoFormula (p / T)
    rw [hill_eq_twoFormula (div_pos hp hT) ((div_le_one hT).2 hpT)]
  · rw [hillBound_eq_multiFormula (by omega) hT hp hpT]
    simp only [numericalBound, if_neg hn2]

/-- Unified closed form for the original normalized exact-maximum supremum. -/
theorem hill_eq_numericalBound {n : ℕ} (hn : 2 ≤ n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) : hill n α = numericalBound n 1 α := by
  simpa [hillBound] using hillBound_eq_numericalBound hn (by norm_num : (0 : ℝ) < 1) hα hα1

/-- Semantic upper bound for any residual finite valuation. -/
theorem mms_le_numericalBound {m n : ℕ} (hn : 2 ≤ n) {v : Fin m → ℝ} {T p : ℝ}
    (hT : 0 < T) (hp : 0 < p) (hpT : p ≤ T)
    (hv : ∀ j, 0 ≤ v j ∧ v j ≤ p) (hsum : (∑ j, v j) = T)
    (hmax : ∃ j, v j = p) : mms n v ≤ numericalBound n T p := by
  rw [← hillBound_eq_numericalBound hn hT hp hpT]
  exact mms_le_hillBound (by omega) hT hv hsum hmax

/-- Corollary 4.5's semantic comparison, with its exact floor index and genuine
supremum bounds on both sides. The finite prefix lemmas supply `hprefix`. -/
theorem hillBound_tail_domination {q : ℕ} {T α C p : ℝ}
    (hq : 2 ≤ q) (hT : 0 < T) (hp : 0 < p) (hpT : p ≤ T - C)
    (hpα : p ≤ α) (hαT : α ≤ T)
    (hprefix : α + (formulaIndex (q + 1) T α : ℝ) * p ≤ C)
    (hcross : hillBound (q + 1) T α < C + p) :
    hillBound q (T - C) p ≤ hillBound (q + 1) T α := by
  have hα : 0 < α := hp.trans_le hpα
  have htail : 0 < T - C := hp.trans_le hpT
  rw [hillBound_eq_multiFormula (by omega) hT hα hαT] at hcross ⊢
  rw [hillBound_eq_numericalBound hq htail hp hpT]
  exact numericalBound_tail_scaled hq hT hp hpT hpα hprefix hcross

end ExactHillShares
