import ExactHillShares.ExactFormulaUpper
import ExactHillShares.SubsetSelection

namespace ExactHillShares

/-- A finite subset gap forces an item of at least half the target mass.
This corrects the prior paper's imprecise statement about elements outside
the chosen minimum subset: only its own elements need a lower bound. -/
theorem exists_large_of_subset_gap {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (v : ι → ℝ) {α δ : ℝ}
    (hα : 0 < α) (hδ : α / 3 < δ)
    (htotal : α ≤ ∑ x ∈ S, v x)
    (hgap : ∀ T ⊆ S, (∑ x ∈ T, v x) < α → (∑ x ∈ T, v x) ≤ α - δ) :
    ∃ x ∈ S, α / 2 ≤ v x := by
  classical
  by_contra! hsmall
  let candidates := S.powerset.filter (fun T => 2 * α / 3 ≤ ∑ x ∈ T, v x)
  have hc : candidates.Nonempty := by
    refine ⟨S, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, by linarith⟩
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image candidates Finset.card hc
  have hTS : T ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hTL : 2 * α / 3 ≤ ∑ x ∈ T, v x := (Finset.mem_filter.mp hT).2
  have hTa : α ≤ ∑ x ∈ T, v x := by
    by_contra! h
    have hh := hgap T hTS h
    linarith
  have hitem : ∀ x ∈ T, α / 3 < v x := by
    intro x hx
    have herase : (∑ y ∈ T.erase x, v y) < 2 * α / 3 := by
      by_contra! hn
      have hem : T.erase x ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨(Finset.erase_subset _ _).trans hTS, hn⟩
      have hm := hmin (T.erase x) hem
      have hlt := Finset.card_erase_lt_of_mem hx
      omega
    have hsum := Finset.sum_erase_add T v hx
    linarith
  have htcard : 1 < T.card := by
    by_contra! h
    have hsum : (∑ x ∈ T, v x) ≤ (T.card : ℝ) * (α / 2) := by
      calc
        _ ≤ ∑ _x ∈ T, α / 2 := Finset.sum_le_sum (fun x hx => le_of_lt (hsmall x (hTS hx)))
        _ = _ := by simp
    have hcR : (T.card : ℝ) ≤ 1 := by exact_mod_cast h
    nlinarith
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp htcard
  have hpair : ({x, y} : Finset ι) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hTS hx
    · exact hTS hy
  have hp_lt : (∑ z ∈ ({x, y} : Finset ι), v z) < α := by
    rw [Finset.sum_pair hxy]
    have hxv := hsmall x (hTS hx)
    have hyv := hsmall y (hTS hy)
    linarith
  have hp_gap := hgap {x, y} hpair hp_lt
  rw [Finset.sum_pair hxy] at hp_gap
  have hxv := hitem x hx
  have hyv := hitem y hy
  linarith

/-- The stable-allocation upper bound responsible for the exceptional middle range. -/
theorem mms_two_le_exceptional_max {m : ℕ} {v : Fin m → ℝ} {α : ℝ}
    (hα : 0 < α) (hα3 : α ≤ 1 / 3) (hv : IsNormalizedExact v α) :
    mms 2 v ≤ max (3 * (1 - α) / 4) (max ((2 + 3 * α) / 5) (2 * α)) := by
  classical
  obtain ⟨a, ha⟩ := exists_exchangeStable (n := 2) (by decide) v
  apply (mms_le_iff (by decide) v _).2
  refine ⟨a, ?_⟩
  intro i
  by_contra! hbound
  have hB1 : 3 * (1 - α) / 4 < load v a i := (le_max_left _ _).trans_lt hbound
  have hB2 : (2 + 3 * α) / 5 < load v a i :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hbound
  have hB3 : 2 * α < load v a i :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hbound
  obtain ⟨j, hij, hsum⟩ : ∃ j : Fin 2, i ≠ j ∧ load v a i + load v a j = 1 := by
    have hsum := sum_load v a
    rw [hv.2.1, Fin.sum_univ_two] at hsum
    fin_cases i
    · exact ⟨1, by decide, hsum⟩
    · exact ⟨0, by decide, by rw [add_comm]; exact hsum⟩
  let δ := load v a i - load v a j
  have hδ : α / 3 < δ := by
    dsimp [δ]
    by_cases hα4 : α ≤ 1 / 4 <;> linarith only [hsum, hB1, hB2, hα4]
  have hδ0 : 0 < δ := lt_trans (by linarith : (0 : ℝ) < α / 3) hδ
  have hmain : ∀ x, v x = α → a x = i := by
    intro x hxα
    by_cases hxi : a x = i
    · exact hxi
    exfalso
    have hxj : a x = j := by
      have hh : (a x).val = j.val := by omega
      exact Fin.ext hh
    let S := positiveFiber v a i
    have hSsum : (∑ y ∈ S, v y) = load v a i := by
      rw [← bundleCost_eq_sum]
      exact bundleCost_positiveFiber (fun y => (hv.1 y).1) a i
    have hSbounds : ∀ y ∈ S, 0 < v y ∧ v y ≤ α := by
      intro y hy
      exact ⟨((mem_positiveFiber v a i y).1 hy).2, (hv.1 y).2⟩
    obtain ⟨U, hUS, hUL, hUU⟩ := subset_selection_one S v α hα (by rwa [hSsum]) hSbounds
    rw [hSsum] at hUL hUU
    have hUfiber : U ⊆ fiber a i := hUS.trans (positiveFiber_subset v a i)
    have hxmem : x ∈ fiber a j := by simpa using hxj
    have hh := ha.swap_obstruction hij
      (fun y hy => (mem_fiber a i y).1 (hUfiber hy))
      (fun y hy => (mem_fiber a j y).1 (Finset.mem_of_mem_erase hy))
      (S := U) (T := (fiber a j).erase x) (by
        rw [bundleCost_erase v hxmem, bundleCost_fiber, hxα, bundleCost_eq_sum]
        linarith)
    rw [bundleCost_erase v hxmem, bundleCost_fiber, hxα, bundleCost_eq_sum] at hh
    linarith
  obtain ⟨x, hxα⟩ := hv.2.2
  have hxi := hmain x hxα
  have hMα : α < load v a i := by linarith
  have hother : α ≤ load v a j := by
    have hh := ha.subset_le_other hij (S := {x}) (by simpa)
      (by simpa [hxα] using hMα)
    simpa [hxα] using hh
  have hother_strict : ∀ y ∈ fiber a j, v y < α := by
    intro y hy
    apply lt_of_le_of_ne (hv.1 y).2
    intro hyα
    exact hij ((hmain y hyα).symm.trans ((mem_fiber a j y).1 hy))
  have hgap : ∀ T ⊆ fiber a j, (∑ y ∈ T, v y) < α → (∑ y ∈ T, v y) ≤ α - δ := by
    intro T hT hTα
    have hh := ha i j {x} T hij (by simpa)
      (fun y hy => (mem_fiber a j y).1 (hT hy)) (by
        simpa [hxα, bundleCost_eq_sum] using hTα)
    rw [bundleCost_singleton, hxα, bundleCost_eq_sum] at hh
    dsimp [δ]
    linarith
  obtain ⟨b, hb, hblow⟩ := exists_large_of_subset_gap (fiber a j) v hα hδ
    (by rwa [← bundleCost_eq_sum, bundleCost_fiber]) hgap
  have hbj := (mem_fiber a j b).1 hb
  have hbα := hother_strict b hb
  have hbup : v b ≤ α - δ := by
    have hh := hgap {b} (Finset.singleton_subset_iff.mpr hb) (by simpa using hbα)
    simpa using hh
  let R := (positiveFiber v a i).erase x
  have hxmem : x ∈ positiveFiber v a i := by simp [hxi, hxα, hα]
  have hRsum : (∑ y ∈ R, v y) = load v a i - α := by
    rw [← bundleCost_eq_sum]
    dsimp [R]
    rw [bundleCost_erase v hxmem, bundleCost_positiveFiber (fun y => (hv.1 y).1), hxα]
  have hRmem : ∀ y ∈ R, a y = i ∧ 0 < v y := by
    intro y hy
    exact (mem_positiveFiber v a i y).1 (Finset.mem_of_mem_erase hy)
  have hRlow : ∀ y ∈ R, δ ≤ v y := by
    intro y hy
    have hymem := hRmem y hy
    have hh := ha.item_gap hymem.2 (hymem.1.trans_ne hij)
    rwa [hymem.1] at hh
  have hRcard : 2 ≤ R.card := by
    apply Nat.le_of_not_lt
    intro hc
    have hcR : (R.card : ℝ) ≤ 1 := by exact_mod_cast (show R.card ≤ 1 by omega)
    have hs : (∑ y ∈ R, v y) ≤ (R.card : ℝ) * α := by
      calc
        _ ≤ ∑ _y ∈ R, α := Finset.sum_le_sum fun y _ => (hv.1 y).2
        _ = _ := by simp
    rw [hRsum] at hs
    nlinarith only [hs, hcR, hB3, hα]
  have hRup : ∀ y ∈ R, v y ≤ v b := by
    intro y hy
    apply le_of_not_gt
    intro hyb
    have hymem := hRmem y hy
    have hyy := ha i j {y} {b} hij (by simpa using hymem.1) (by simpa using hbj)
      (by simpa using hyb)
    simp only [bundleCost_singleton] at hyy
    obtain ⟨z, hz, hzy⟩ := Finset.exists_mem_ne (show 1 < R.card by omega) y
    have hpair : ({y, z} : Finset (Fin m)) ⊆ R := by simp [Finset.insert_subset_iff, hy, hz]
    have hsum_pair := Finset.sum_le_sum_of_subset_of_nonneg hpair
      (fun w _ _ => (hv.1 w).1)
    rw [Finset.sum_pair (Ne.symm hzy), hRsum] at hsum_pair
    have hzl := hRlow z hz
    dsimp [δ] at hzl
    linarith only [hyy, hsum_pair, hzl, hblow, hsum, hB1, hα3]
  have hRcard_le : R.card ≤ 2 := by
    apply Nat.le_of_not_lt
    intro hc
    have hcR : (3 : ℝ) ≤ R.card := by exact_mod_cast (show 3 ≤ R.card by omega)
    have hs : (R.card : ℝ) * δ ≤ load v a i - α := by
      calc
        _ = ∑ _y ∈ R, δ := by simp
        _ ≤ ∑ y ∈ R, v y := Finset.sum_le_sum hRlow
        _ = _ := hRsum
    have hprod := mul_le_mul_of_nonneg_right hcR hδ0.le
    dsimp [δ] at hs hprod
    by_cases hα4 : α ≤ 1 / 4 <;> linarith only [hs, hprod, hsum, hB1, hB2, hα4]
  have hRtwo : R.card = 2 := by omega
  have hs : load v a i - α ≤ 2 * v b := by
    rw [← hRsum]
    calc
      _ ≤ ∑ _y ∈ R, v b := Finset.sum_le_sum hRup
      _ = _ := by simp [hRtwo]
  dsimp [δ] at hbup
  linarith

/-- On the exceptional interval the three obstructions give exactly the displayed formula. -/
theorem twoFormula_eq_exceptional_max {α : ℝ} (hα5 : 1 / 5 ≤ α) (hα3 : α ≤ 1 / 3) :
    twoFormula α = max (3 * (1 - α) / 4) (max ((2 + 3 * α) / 5) (2 * α)) := by
  unfold twoFormula
  split_ifs with h3 h7 h27
  · have hαeq : α = 1 / 3 := le_antisymm hα3 h3
    subst α
    norm_num
  · rw [max_eq_right (by linarith : (2 + 3 * α) / 5 ≤ 2 * α)]
    rw [max_eq_right (by linarith : 3 * (1 - α) / 4 ≤ 2 * α)]
  · rw [max_eq_left (by linarith : 2 * α ≤ (2 + 3 * α) / 5)]
    rw [max_eq_right (by linarith : 3 * (1 - α) / 4 ≤ (2 + 3 * α) / 5)]
  · rw [max_eq_left (by linarith : 2 * α ≤ (2 + 3 * α) / 5)]
    rw [max_eq_left (by linarith : (2 + 3 * α) / 5 ≤ 3 * (1 - α) / 4)]

/-- Semantic finite-instance upper bound throughout the exceptional middle interval. -/
theorem mms_le_twoFormula_exceptional {m : ℕ} {v : Fin m → ℝ} {α : ℝ}
    (hα5 : 1 / 5 ≤ α) (hα3 : α ≤ 1 / 3) (hv : IsNormalizedExact v α) :
    mms 2 v ≤ twoFormula α := by
  rw [twoFormula_eq_exceptional_max hα5 hα3]
  exact mms_two_le_exceptional_max (by linarith) hα3 hv

end ExactHillShares
