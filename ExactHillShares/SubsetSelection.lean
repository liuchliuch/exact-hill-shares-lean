import Mathlib

namespace ExactHillShares

/-- The two cheapest elements cost at most twice the average cost. -/
theorem exists_pair_le_twice_average {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (v : ι → ℝ) (hcard : 2 ≤ S.card) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧
      (S.card : ℝ) * (v x + v y) ≤ 2 * ∑ z ∈ S, v z := by
  have hs : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx, hxmin⟩ := Finset.exists_min_image S v hs
  have hecard : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
  have he : (S.erase x).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y, hy, hymin⟩ := Finset.exists_min_image (S.erase x) v he
  have hyS := Finset.mem_of_mem_erase hy
  have hyx := (Finset.mem_erase.mp hy).1
  have hxy : v x ≤ v y := hxmin y hyS
  have hsum : ((S.erase x).card : ℝ) * v y ≤ ∑ z ∈ S.erase x, v z := by
    calc
      ((S.erase x).card : ℝ) * v y = ∑ z ∈ S.erase x, v y := by simp
      _ ≤ ∑ z ∈ S.erase x, v z := Finset.sum_le_sum (fun z hz => hymin z hz)
  have heR : ((S.erase x).card : ℝ) = (S.card : ℝ) - 1 := by
    rw [hecard, Nat.cast_sub (by omega)]
    norm_num
  rw [heR] at hsum
  have hdecomp := Finset.sum_erase_add S v hx
  have hcR : (2 : ℝ) ≤ S.card := by exact_mod_cast hcard
  have hprod : 0 ≤ ((S.card : ℝ) - 2) * (v y - v x) :=
    mul_nonneg (by linarith) (by linarith)
  refine ⟨x, hx, y, hyS, Ne.symm hyx, ?_⟩
  nlinarith

/-- A sum-minimal subset satisfying a threshold exists whenever the whole set does. -/
lemma exists_min_subset_sum {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (v : ι → ℝ) (q : ℝ)
    (hS : q < ∑ z ∈ S, v z) :
    ∃ t ⊆ S, q < ∑ z ∈ t, v z ∧
      ∀ u ⊆ S, q < ∑ z ∈ u, v z → (∑ z ∈ t, v z) ≤ ∑ z ∈ u, v z := by
  let T := S.powerset.filter (fun t => q < ∑ z ∈ t, v z)
  have hne : T.Nonempty := ⟨S, by simp [T, hS]⟩
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image T (fun t => ∑ z ∈ t, v z) hne
  have ht' := Finset.mem_filter.mp ht
  refine ⟨t, Finset.mem_powerset.mp ht'.1, ht'.2, ?_⟩
  intro u hu hqu
  exact hmin u (by simp [T, hu, hqu])

lemma subset_selection_large {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (v : ι → ℝ) (α : ℝ) (k : ℕ)
    (hα : 0 < α) (hk : 2 ≤ k)
    (hM : ((k : ℝ) + 1) * α < ∑ z ∈ S, v z)
    (hv : ∀ z ∈ S, 0 < v z ∧ v z ≤ α)
    (hlow : ∀ z ∈ S, α / ((k : ℝ) + 2) < v z) :
    ∃ U ⊆ S, (k : ℝ) * (∑ z ∈ S, v z) / ((k : ℝ) + 2) ≤ ∑ z ∈ U, v z ∧
      (∑ z ∈ U, v z) < (∑ z ∈ S, v z) - α := by
  let M : ℝ := ∑ z ∈ S, v z
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < (k : ℝ) + 2 := by positivity
  have hMα : α < M := by dsimp [M]; nlinarith
  obtain ⟨t, htS, htα, htmin⟩ := exists_min_subset_sum S v α hMα
  have htsmall : (∑ z ∈ t, v z) ≤ 2 * M / ((k : ℝ) + 2) := by
    by_contra! hbig
    have hbig' : 2 * M < (∑ z ∈ t, v z) * ((k : ℝ) + 2) := (div_lt_iff₀ hd).mp hbig
    have htlarge : 3 * α / 2 < ∑ z ∈ t, v z := by
      have haux : 0 ≤ ((k : ℝ) - 2) * α := mul_nonneg (by linarith) hα.le
      dsimp [M] at hbig'
      nlinarith
    have htitem : ∀ z ∈ t, α / 2 < v z := by
      intro z hz
      have hremove : (∑ e ∈ t.erase z, v e) ≤ α := by
        by_contra! habove
        have hmin := htmin (t.erase z) ((Finset.erase_subset z t).trans htS) habove
        have heq := Finset.sum_erase_add t v hz
        have hpos := (hv z (htS hz)).1
        linarith
      have heq := Finset.sum_erase_add t v hz
      linarith
    have htcard : 2 ≤ t.card := by
      by_contra! hc
      have hsumle : (∑ z ∈ t, v z) ≤ (t.card : ℝ) * α := by
        calc
          _ ≤ ∑ _z ∈ t, α := Finset.sum_le_sum (fun z hz => (hv z (htS hz)).2)
          _ = _ := by simp
      have hcR : (t.card : ℝ) ≤ 1 := by exact_mod_cast (show t.card ≤ 1 by omega)
      nlinarith
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < t.card by omega)
    have hpair_sub : ({x, y} : Finset ι) ⊆ S := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact htS hx
      · exact htS hy
    have hpair_gt : α < v x + v y := by have := htitem x hx; have := htitem y hy; linarith
    have hpair_min := htmin {x, y} hpair_sub (by simpa [hxy] using hpair_gt)
    have hpair_le : v x + v y ≤ ∑ z ∈ t, v z := by
      have hsub : ({x, y} : Finset ι) ⊆ t := by simp [Finset.insert_subset_iff, hx, hy]
      have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z hz _ => (hv z (htS hz)).1.le)
      simpa [hxy] using hh
    have hpair_eq : (∑ z ∈ t, v z) = v x + v y := by
      have hpm : (∑ z ∈ t, v z) ≤ v x + v y := by simpa [hxy] using hpair_min
      exact le_antisymm hpm hpair_le
    obtain ⟨l, hl, s, hs, hls, hvls, hteq⟩ :
        ∃ l ∈ t, ∃ s ∈ t, l ≠ s ∧ v s ≤ v l ∧ (∑ z ∈ t, v z) = v l + v s := by
      by_cases h : v y ≤ v x
      · exact ⟨x, hx, y, hy, hxy, h, hpair_eq⟩
      · exact ⟨y, hy, x, hx, Ne.symm hxy, le_of_lt (lt_of_not_ge h), by linarith⟩
    have hlbig : ((k : ℝ) + 1) * α < v l * ((k : ℝ) + 2) := by
      have hmul := mul_le_mul_of_nonneg_right hvls hd.le
      dsimp [M] at hbig'
      rw [hteq] at hbig'
      nlinarith
    have hglobmin : ∀ e ∈ S, v s ≤ v e := by
      intro e he
      by_cases hel : e = l
      · simpa [hel] using hvls
      have hle : l ≠ e := Ne.symm hel
      have he_low : α < v e * ((k : ℝ) + 2) := (div_lt_iff₀ hd).mp (hlow e he)
      have habove : α < v l + v e := by nlinarith
      have hsub : ({l, e} : Finset ι) ⊆ S := by simp [Finset.insert_subset_iff, htS hl, he]
      have hmin := htmin {l, e} hsub (by simpa [hle] using habove)
      simp only [Finset.sum_insert, Finset.mem_singleton, hle, not_false_eq_true,
        Finset.sum_singleton] at hmin
      rw [hteq] at hmin
      linarith
    have halllarge : ∀ e ∈ S, α / 2 < v e := by
      intro e he
      exact lt_of_lt_of_le (htitem s hs) (hglobmin e he)
    have hcard : k + 2 ≤ S.card := by
      have hsumle : M ≤ (S.card : ℝ) * α := by
        calc
          _ ≤ ∑ _z ∈ S, α := Finset.sum_le_sum (fun z hz => (hv z hz).2)
          _ = _ := by simp
      have hcR : (k : ℝ) + 1 < (S.card : ℝ) := by dsimp [M] at hsumle; nlinarith
      have hc : k + 1 < S.card := by exact_mod_cast hcR
      omega
    obtain ⟨a, ha, b, hb, hab, hpavg⟩ := exists_pair_le_twice_average S v (by omega)
    have hpabove : α < v a + v b := by have := halllarge a ha; have := halllarge b hb; linarith
    have hpsub : ({a, b} : Finset ι) ⊆ S := by simp [Finset.insert_subset_iff, ha, hb]
    have hpmin := htmin {a, b} hpsub (by simpa [hab] using hpabove)
    have hcR : (k : ℝ) + 2 ≤ (S.card : ℝ) := by exact_mod_cast hcard
    have hpnonneg : 0 ≤ v a + v b := by linarith
    have hpmul := mul_le_mul_of_nonneg_right hcR hpnonneg
    simp [hab] at hpmin
    dsimp [M] at hbig'
    nlinarith
  have heq : (∑ z ∈ S \ t, v z) + (∑ z ∈ t, v z) = M := by
    exact Finset.sum_sdiff htS
  refine ⟨S \ t, Finset.sdiff_subset, ?_, ?_⟩
  · have htsmall' := (le_div_iff₀ hd).mp htsmall
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · dsimp [M] at heq
    linarith

/-- The elementary one-third subset selection bound. -/
lemma subset_selection_one {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (v : ι → ℝ) (α : ℝ)
    (hα : 0 < α) (hM : 2 * α < ∑ z ∈ S, v z)
    (hv : ∀ z ∈ S, 0 < v z ∧ v z ≤ α) :
    ∃ U ⊆ S, (∑ z ∈ S, v z) / 3 ≤ ∑ z ∈ U, v z ∧
      (∑ z ∈ U, v z) < (∑ z ∈ S, v z) - α := by
  let M : ℝ := ∑ z ∈ S, v z
  have hMpos : 0 < M := by dsimp [M]; linarith
  by_cases hsingle : ∃ z ∈ S, M / 3 ≤ v z
  · obtain ⟨z, hz, hzbig⟩ := hsingle
    refine ⟨{z}, by simpa using hz, ?_, ?_⟩
    · simpa [M] using hzbig
    · simp only [Finset.sum_singleton]
      have := (hv z hz).2
      linarith
  have hsmall : ∀ z ∈ S, v z < M / 3 := by
    intro z hz
    by_contra! h
    exact hsingle ⟨z, hz, h⟩
  obtain ⟨t, htS, htq, htmin⟩ := exists_min_subset_sum S v (M / 3) (by dsimp [M] at *; linarith)
  have htne : t.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    simp [h] at htq
    linarith
  obtain ⟨z, hz⟩ := htne
  have hremove : (∑ e ∈ t.erase z, v e) ≤ M / 3 := by
    by_contra! habove
    have hmin := htmin (t.erase z) ((Finset.erase_subset z t).trans htS) habove
    have heq := Finset.sum_erase_add t v hz
    have hpos := (hv z (htS hz)).1
    linarith
  have hupper : (∑ e ∈ t, v e) < 2 * M / 3 := by
    have heq := Finset.sum_erase_add t v hz
    have := hsmall z (htS hz)
    linarith
  by_cases hhalf : (∑ e ∈ t, v e) ≤ M / 2
  · refine ⟨t, htS, htq.le, ?_⟩
    dsimp [M] at hhalf
    linarith
  · have heq : (∑ z ∈ S \ t, v z) + (∑ z ∈ t, v z) = M := Finset.sum_sdiff htS
    refine ⟨S \ t, Finset.sdiff_subset, ?_, ?_⟩
    · dsimp [M] at heq hupper
      linarith
    · dsimp [M] at heq hhalf
      linarith

/-- Claim 5 of Li--Moulin--Sun--Zhou: a medium-sized subset below the strict gap. -/
theorem subset_selection_claim5 {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (v : ι → ℝ) (α : ℝ) (k : ℕ)
    (hα : 0 < α) (hk : 1 ≤ k)
    (hM : ((k : ℝ) + 1) * α < ∑ z ∈ S, v z)
    (hv : ∀ z ∈ S, 0 < v z ∧ v z ≤ α)
    (hlow : 2 ≤ k → ∀ z ∈ S, α / ((k : ℝ) + 2) < v z) :
    ∃ U ⊆ S, (k : ℝ) * (∑ z ∈ S, v z) / ((k : ℝ) + 2) ≤ ∑ z ∈ U, v z ∧
      (∑ z ∈ U, v z) < (∑ z ∈ S, v z) - α := by
  by_cases hk1 : k = 1
  · subst k
    have hm : 2 * α < ∑ z ∈ S, v z := by norm_num at hM ⊢; exact hM
    simpa only [Nat.cast_one, one_mul, show (1 : ℝ) + 2 = 3 by norm_num] using subset_selection_one S v α hα hm hv
  · have hk2 : 2 ≤ k := by omega
    exact subset_selection_large S v α k hα hk2 hM hv (hlow hk2)

end ExactHillShares
