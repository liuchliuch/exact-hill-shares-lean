import ExactHillShares.OrderedReduction

namespace ExactHillShares

/-- A constructive version of ranked matching. At the cheapest remaining rank,
choose the least eligible original item, then erase it from all later sets.
The proof arguments only certify that this finite choice cannot fail. -/
def rankedGreedy {ι : Type*} [LinearOrder ι] (m : ℕ)
    (eligible : Fin m → Finset ι) (hcard : ∀ r, r.val + 1 ≤ (eligible r).card) :
    {f : Fin m → ι // Function.Injective f ∧ ∀ r, f r ∈ eligible r} := by
  induction m with
  | zero =>
    exact ⟨Fin.elim0, fun r => Fin.elim0 r, fun r => Fin.elim0 r⟩
  | succ m ih =>
    have hzero : (eligible 0).Nonempty := Finset.card_pos.mp (hcard 0)
    let x := (eligible 0).min' hzero
    have hx : x ∈ eligible 0 := Finset.min'_mem _ _
    let rest : Fin m → Finset ι := fun r => (eligible r.succ).erase x
    have hrest : ∀ r, r.val + 1 ≤ (rest r).card := by
      intro r
      have hc := hcard r.succ
      dsimp only [rest]
      by_cases hm : x ∈ eligible r.succ
      · rw [Finset.card_erase_of_mem hm]
        simp only [Fin.val_succ] at hc
        omega
      · rw [Finset.erase_eq_of_not_mem hm]
        simp only [Fin.val_succ] at hc
        omega
    obtain ⟨g, hg, hgm⟩ := ih rest hrest
    refine ⟨Fin.cases x g, ?_, ?_⟩
    · intro r s hrs
      cases r using Fin.cases with
      | zero =>
        cases s using Fin.cases with
        | zero => rfl
        | succ s =>
          have hn := (Finset.mem_erase.mp (hgm s)).1
          exact False.elim (hn hrs.symm)
      | succ r =>
        cases s using Fin.cases with
        | zero =>
          have hn := (Finset.mem_erase.mp (hgm r)).1
          exact False.elim (hn hrs)
        | succ s => exact congrArg Fin.succ (hg hrs)
    · intro r
      refine Fin.cases ?_ (fun r => ?_) r
      · exact hx
      · exact Finset.mem_of_mem_erase (hgm r)

/-- Actual rational sorted rows use mathlib's finite sorting permutation. -/
def rationalSortedCost {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (i : Fin n) (r : Fin m) : ℚ := cost i (Tuple.sort (cost i) r)

def rationalEligible {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) (r : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun x => cost (owner r) x ≤ rationalSortedCost cost (owner r) r)

theorem rationalEligible_card {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) (r : Fin m) :
    r.val + 1 ≤ (rationalEligible cost owner r).card := by
  have hsub : (Finset.Iic r).image (Tuple.sort (cost (owner r))) ⊆
      rationalEligible cost owner r := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Tuple.monotone_sort (cost (owner r)) (Finset.mem_Iic.mp hj)⟩
  have hc := Finset.card_le_card hsub
  simpa [Finset.card_image_of_injective _ (Tuple.sort (cost (owner r))).injective] using hc

/-- Deterministically computed rank-to-original-item bijection. -/
def rationalGreedyRanks {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) : Fin m → Fin m :=
  (rankedGreedy m (rationalEligible cost owner) (rationalEligible_card cost owner)).val

theorem rationalGreedyRanks_injective {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) : Function.Injective (rationalGreedyRanks cost owner) :=
  (rankedGreedy m (rationalEligible cost owner) (rationalEligible_card cost owner)).property.1

theorem rationalGreedyRanks_safe {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) (r : Fin m) :
    cost (owner r) (rationalGreedyRanks cost owner r) ≤ rationalSortedCost cost (owner r) r :=
  (Finset.mem_filter.mp
    ((rankedGreedy m (rationalEligible cost owner) (rationalEligible_card cost owner)).property.2 r)).2

/-- Computable inverse by a finite search, with uniqueness ensured by the
matching certificate. No classical choice is used by this executable function. -/
def finiteInverse {m : ℕ} (f : Fin m → Fin m) (hf : Function.Bijective f)
    (x : Fin m) : Fin m :=
  let candidates := Finset.univ.filter (fun r => f r = x)
  have h : candidates.Nonempty := by
    obtain ⟨r, hr⟩ := hf.2 x
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
  candidates.min' h

theorem finiteInverse_spec {m : ℕ} (f : Fin m → Fin m) (hf : Function.Bijective f)
    (x : Fin m) : f (finiteInverse f hf x) = x := by
  unfold finiteInverse
  dsimp only
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter (fun r => f r = x)) _)).2

/-- Executable allocation of original items from cheapest-first rank owners. -/
def rationalOriginalAllocation {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) (x : Fin m) : Fin n :=
  let f := rationalGreedyRanks cost owner
  have hi := rationalGreedyRanks_injective cost owner
  owner (finiteInverse f ⟨hi, Finite.surjective_of_injective hi⟩ x)

theorem rationalOriginalAllocation_safe {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) (i : Fin n) :
    (∑ x, if rationalOriginalAllocation cost owner x = i then cost i x else 0) ≤
      ∑ r, if owner r = i then rationalSortedCost cost i r else 0 := by
  let f := rationalGreedyRanks cost owner
  have hi := rationalGreedyRanks_injective cost owner
  let e : Equiv.Perm (Fin m) := Equiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩
  have hinv (r : Fin m) :
      rationalOriginalAllocation cost owner (e r) = owner r := by
    change owner (finiteInverse f _ (e r)) = owner r
    apply congrArg owner
    apply hi
    exact finiteInverse_spec f _ (e r)
  have hsum := Equiv.sum_comp e
    (fun x => if rationalOriginalAllocation cost owner x = i then cost i x else 0)
  rw [← hsum]
  apply Finset.sum_le_sum
  intro r hr
  rw [hinv]
  by_cases hri : owner r = i
  · simpa [hri, e, f] using rationalGreedyRanks_safe cost owner r
  · simp [hri]

/-- Executable most-expensive-first sorted rational row. -/
def rationalDescendingCost {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (i : Fin n) (r : Fin m) : ℚ := rationalSortedCost cost i r.rev

theorem rationalDescendingCost_antitone {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (i : Fin n) : Antitone (rationalDescendingCost cost i) := by
  intro r s hrs
  exact Tuple.monotone_sort (cost i) (Fin.rev_le_rev.mpr hrs)

/-- Original-item lift from the paper's most-expensive-first ranks. -/
def rationalDescendingAllocation {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) : Fin m → Fin n :=
  rationalOriginalAllocation cost (fun r => owner r.rev)

theorem rationalDescendingAllocation_safe {n m : ℕ} (cost : Fin n → Fin m → ℚ)
    (owner : Fin m → Fin n) (i : Fin n) :
    (∑ x, if rationalDescendingAllocation cost owner x = i then cost i x else 0) ≤
      ∑ r, if owner r = i then rationalDescendingCost cost i r else 0 := by
  have h := rationalOriginalAllocation_safe cost (fun r => owner r.rev) i
  have heq : (∑ r, if owner r.rev = i then rationalSortedCost cost i r else 0) =
      ∑ r, if owner r = i then rationalDescendingCost cost i r else 0 := by
    symm
    convert Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin m))
      (fun r => if owner r.rev = i then rationalSortedCost cost i r else 0) using 1
    simp [rationalDescendingCost, Fin.revPerm]
  simpa only [heq] using h

end ExactHillShares
