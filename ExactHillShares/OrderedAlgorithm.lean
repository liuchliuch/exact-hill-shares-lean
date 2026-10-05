import ExactHillShares.Terminal

namespace ExactHillShares.Algorithm

/-- The complete corrected algorithm on common decreasing ranked rows.
There is no unproved terminal callback in this executable definition. -/
def allocateOrdered {n : ℕ} (c : Fin n → ℕ → ℚ) (m : ℕ) : Option (Allocation n) :=
  runWith terminal c n Finset.univ 0 m

theorem allocateOrdered_correct {n : ℕ} (c : Fin n → ℕ → ℚ) (m : ℕ)
    (hn : 0 < n) (hc : ∀ i j, 0 ≤ c i j) (ha : ∀ i, Antitone (c i)) :
    ∃ out, allocateOrdered c m = some out ∧ Safe c Finset.univ 0 m out := by
  apply runWith_correct terminal terminal_correct
  · simp
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  · intro i hi j
    exact hc i j
  · intro i hi
    exact ha i

/-- For normalized rational rows, the verified returned costs meet the
genuine real supremum-defined exact Hill share of every agent. -/
theorem allocateOrdered_hill_correct {n : ℕ} (c : Fin n → ℕ → ℚ) (m : ℕ)
    (hn : 2 ≤ n) (hc : ∀ i j, 0 ≤ c i j) (ha : ∀ i, Antitone (c i))
    (hnorm : ∀ i, mass (c i) 0 m = 1) :
    ∃ out, allocateOrdered c m = some out ∧ Valid Finset.univ 0 m out ∧
      ∀ i, (charge c 0 m out i : ℝ) ≤ hill n (c i 0 : ℝ) := by
  obtain ⟨out, hout, hv, hs⟩ := allocateOrdered_correct c m (by omega) hc ha
  refine ⟨out, hout, hv, fun i => ?_⟩
  have hpos : (0 : ℚ) < mass (c i) 0 m := by rw [hnorm]; norm_num
  have hp : (0 : ℚ) < c i 0 := head_pos (c i) 0 m (ha i) hpos
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    have := hnorm i
    simp [hm0] at this
  have hpT := head_le_mass (c i) 0 m (hc i) hm
  have hp1 : (c i 0 : ℝ) ≤ 1 := by
    rw [hnorm] at hpT
    exact_mod_cast hpT
  have hb := hs i (Finset.mem_univ i)
  have hbR : (charge c 0 m out i : ℝ) ≤
      (bound n (mass (c i) 0 m) (c i 0) : ℝ) := by
    exact_mod_cast (show charge c 0 m out i ≤ bound n (mass (c i) 0 m) (c i 0) by simpa using hb)
  rw [cast_bound hn (ne_of_gt hpos), hnorm] at hbR
  norm_num only [Rat.cast_one] at hbR
  rw [← hill_eq_numericalBound hn (by exact_mod_cast hp) hp1] at hbR
  exact hbR

end ExactHillShares.Algorithm
