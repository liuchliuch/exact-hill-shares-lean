import ExactHillShares.OrderedAlgorithm
import ExactHillShares.GreedyMatching
import ExactHillShares.SingletonAllocation

namespace ExactHillShares.Algorithm
open scoped BigOperators

/-- Decreasing sorted rational rows, extended by zero after the input. -/
def originalRows {n m : ℕ} (cost : Fin n → Fin m → ℚ) (i : Fin n) (r : ℕ) : ℚ :=
  if h : r < m then rationalDescendingCost cost i ⟨r, h⟩ else 0

lemma originalRows_nonneg {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (hc : ∀ i j, 0 ≤ cost i j) : ∀ i r, 0 ≤ originalRows cost i r := by
  intro i r
  unfold originalRows
  split
  · exact hc _ _
  · rfl

lemma originalRows_antitone {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (hc : ∀ i j, 0 ≤ cost i j) : ∀ i, Antitone (originalRows cost i) := by
  intro i r s hrs
  unfold originalRows
  split_ifs with hs hr hr
  · exact rationalDescendingCost_antitone cost i hrs
  · omega
  · exact hc _ _
  · rfl

lemma originalRows_mass {n m : ℕ} (cost : Fin n → Fin m → ℚ) (i : Fin n) :
    mass (originalRows cost i) 0 m = ∑ j, cost i j := by
  rw [mass_eq_fin_sum]
  simp only [Nat.zero_add, originalRows, Fin.is_lt, dite_true]
  have hrev := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin m))
    (rationalSortedCost cost i)
  have hsort := Equiv.sum_comp (Tuple.sort (cost i)) (cost i)
  exact hrev.trans hsort

/-- Read the owner of a valid rank. The default is unreachable under validity. -/
def rankOwners {n m : ℕ} (hn : 0 < n) (out : Allocation n) : Fin m → Fin n :=
  fun r => (out r).getD ⟨0, hn⟩

lemma rankOwners_some {n m : ℕ} (hn : 0 < n) (out : Allocation n)
    (hv : Valid Finset.univ 0 m out) (r : Fin m) :
    out r = some (rankOwners hn out r) := by
  obtain ⟨i, hi, he⟩ := hv.1 r (by omega) (by simp)
  simp [rankOwners, he]

lemma rankOwners_charge {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℚ) (out : Allocation n)
    (hv : Valid Finset.univ 0 m out) (i : Fin n) :
    (∑ r, if rankOwners hn out r = i then rationalDescendingCost cost i r else 0) =
      charge (originalRows cost) 0 m out i := by
  rw [charge, mass_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Nat.zero_add, rankOwners_some hn out hv r]
  simp [originalRows]

/-- Complete rational allocation on original items. The order-lift is an
executable ranked greedy matching and finite inversion. -/
def allocateOriginal {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℚ) :
    Option (Fin m → Fin n) :=
  (allocateOrdered (originalRows cost) m).map fun out =>
    rationalDescendingAllocation cost (rankOwners hn out)

/-- No orderedness, matching, terminal-feasibility, or successful-run hypothesis
is needed: these are established for the actual returned rational program. -/
theorem allocateOriginal_correct {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℚ) (hc : ∀ i j, 0 ≤ cost i j) :
    ∃ out, allocateOriginal hn cost = some out ∧ ∀ i,
      (∑ j, if out j = i then cost i j else 0) ≤
        bound n (∑ j, cost i j) (originalRows cost i 0) := by
  obtain ⟨out, hout, hv, hs⟩ := allocateOrdered_correct (originalRows cost) m hn
    (originalRows_nonneg cost hc) (originalRows_antitone cost hc)
  refine ⟨rationalDescendingAllocation cost (rankOwners hn out), ?_, fun i => ?_⟩
  · simp [allocateOriginal, hout]
  · have hh := rationalDescendingAllocation_safe cost (rankOwners hn out) i
    rw [rankOwners_charge hn cost out hv i] at hh
    have hb := hs i (Finset.mem_univ i)
    rw [Finset.card_univ, Fintype.card_fin, originalRows_mass] at hb
    exact hh.trans hb

/-- The original allocation reaches the genuine exact Hill share for every
normalized rational row. The largest cost is the initial descending entry. -/
theorem allocateOriginal_hill_correct {n m : ℕ} (hn : 2 ≤ n)
    (cost : Fin n → Fin m → ℚ) (hc : ∀ i j, 0 ≤ cost i j)
    (hnorm : ∀ i, ∑ j, cost i j = 1) :
    ∃ out, allocateOriginal (by omega) cost = some out ∧ ∀ i,
      load (fun j => (cost i j : ℝ)) out i ≤ hill n (originalRows cost i 0 : ℝ) := by
  obtain ⟨out, hout, hv, hs⟩ := allocateOrdered_hill_correct (originalRows cost) m hn
    (originalRows_nonneg cost hc) (originalRows_antitone cost hc)
    (fun i => (originalRows_mass cost i).trans (hnorm i))
  refine ⟨rationalDescendingAllocation cost (rankOwners (by omega) out), ?_, fun i => ?_⟩
  · simp [allocateOriginal, hout]
  · have hh := rationalDescendingAllocation_safe cost (rankOwners (by omega) out) i
    rw [rankOwners_charge (by omega) cost out hv i] at hh
    have hcast : (∑ j, if rationalDescendingAllocation cost (rankOwners (by omega) out) j = i
        then (cost i j : ℝ) else 0) ≤ (charge (originalRows cost) 0 m out i : ℝ) := by
      simpa only [Rat.cast_sum, apply_ite, Rat.cast_zero] using
        (Rat.cast_le (K := ℝ)).mpr hh
    exact hcast.trans (hs i)

end ExactHillShares.Algorithm
