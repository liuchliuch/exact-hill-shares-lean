import ExactHillShares.RealAllocation

namespace ExactHillShares

/-- The omitted single-agent case is the trivial total-cost share. -/
theorem hill_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : hill 1 α = 1 := by
  have hlo := one_le_mul_hill (n := 1) (by decide) hα hα1
  have hhi := hill_le_one (n := 1) (by decide) hα hα1
  norm_num at hlo
  exact le_antisymm hhi hlo

/-- The monotone closure from the introduction, with its domain explicit. -/
noncomputable def monotoneHill (n : ℕ) (α : ℝ) : ℝ :=
  sSup {d | ∃ β, 0 < β ∧ β ≤ α ∧ d = hill n β}

theorem hill_le_monotoneHill {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) : hill n α ≤ monotoneHill n α := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro d ⟨β, hβ, hβα, rfl⟩
    exact hill_le_one hn hβ (hβα.trans hα1)
  · exact ⟨α, hα, le_rfl, rfl⟩

theorem monotoneHill_monotoneOn {n : ℕ} (hn : 0 < n) :
    MonotoneOn (monotoneHill n) (Set.Ioc (0 : ℝ) 1) := by
  intro α hα β hβ hαβ
  apply csSup_le
  · exact ⟨hill n α, α, hα.1, le_rfl, rfl⟩
  · rintro d ⟨γ, hγ, hγα, rfl⟩
    apply le_csSup
    · refine ⟨1, ?_⟩
      rintro d ⟨δ, hδ, hδβ, rfl⟩
      exact hill_le_one hn hδ (hδβ.trans hβ.2)
    · exact ⟨γ, hγ, hγα.trans hαβ, rfl⟩

theorem normalizedExact_max_pos_le_one {m : ℕ} {v : Fin m → ℝ} {α : ℝ}
    (hv : IsNormalizedExact v α) : 0 < α ∧ α ≤ 1 := by
  obtain ⟨j, hj⟩ := hv.2.2
  have hlo : 0 ≤ α := by rw [← hj]; exact (hv.1 j).1
  have hhi : α ≤ 1 := by
    rw [← hj, ← hv.2.1]
    exact Finset.single_le_sum (fun x hx => (hv.1 x).1) (Finset.mem_univ j)
  refine ⟨?_, hhi⟩
  by_contra! hzero
  have ha0 : α = 0 := le_antisymm hzero hlo
  have hz : ∀ j, v j = 0 := fun j => le_antisymm (by simpa [ha0] using (hv.1 j).2) (hv.1 j).1
  have hs := hv.2.1
  simp [hz] at hs

/-- The prior monotone-closure simultaneous guarantee follows as a corollary
of the stronger exact-share theorem, rather than an imported assumption. -/
theorem simultaneous_monotoneHill_allocation {n m : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ)
    (hv : ∀ i, IsNormalizedExact (v i) (α i)) :
    ∃ a : Fin m → Fin n, ∀ i, load (v i) a i ≤ monotoneHill n (α i) := by
  obtain ⟨a, ha⟩ := simultaneous_hill_allocation hn v α hv
  refine ⟨a, fun i => ?_⟩
  obtain ⟨hpos, hle⟩ := normalizedExact_max_pos_le_one (hv i)
  exact (ha i).trans (hill_le_monotoneHill (by omega) hpos hle)

/-- The exact share really decreases on part of its valid domain. -/
theorem hill_three_not_monotone :
    ¬ MonotoneOn (hill 3) (Set.Ioc (0 : ℝ) 1) := by
  have ha : hill 3 (1 / 3 : ℝ) = 4 / 9 := by
    rw [hill_eq_multiFormula (by norm_num) (by norm_num) (by norm_num)]
    norm_num [multiFormula, formulaIndex, envelope,
      Nat.floor_eq_zero.mpr (by norm_num : (2 / 3 : ℝ) < 1)]
  have hb : hill 3 (2 / 5 : ℝ) = 2 / 5 := by
    rw [hill_eq_multiFormula (by norm_num) (by norm_num) (by norm_num)]
    norm_num [multiFormula, formulaIndex, envelope,
      Nat.floor_eq_zero.mpr (by norm_num : (1 / 2 : ℝ) < 1)]
  intro h
  have hh := h (show (1 / 3 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 by norm_num)
    (show (2 / 5 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 by norm_num) (by norm_num : (1 / 3 : ℝ) ≤ 2 / 5)
  rw [ha, hb] at hh
  norm_num at hh

/-- The constant in Lemma 5.1 is attained at the exceptional breakpoint. -/
theorem width_sharp_at_seven_twenty_sevenths :
    2 * hill 2 (7 / 27 : ℝ) - 1 = (3 / 7) * (7 / 27 : ℝ) := by
  rw [hill_eq_twoFormula (by norm_num) (by norm_num)]
  norm_num [twoFormula]

/-- The shared endpoint values quoted in Proposition 4.2. -/
theorem two_agent_endpoint_values :
    hill 2 (1 / 3 : ℝ) = 2 / 3 ∧ hill 2 (2 / 7 : ℝ) = 4 / 7 ∧
      hill 2 (7 / 27 : ℝ) = 5 / 9 ∧ hill 2 (1 / 5 : ℝ) = 3 / 5 := by
  repeat' constructor
  all_goals rw [hill_eq_twoFormula (by norm_num) (by norm_num)]
  all_goals norm_num [twoFormula]

end ExactHillShares
