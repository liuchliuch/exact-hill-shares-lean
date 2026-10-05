import ExactHillShares.StableAllocation
import ExactHillShares.Formula

open scoped BigOperators
namespace ExactHillShares

noncomputable def fiber {m n : ℕ} (a : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun x => a x = i

@[simp] lemma mem_fiber {m n : ℕ} (a : Fin m → Fin n) (i : Fin n) (x : Fin m) :
    x ∈ fiber a i ↔ a x = i := by classical simp [fiber]

@[simp] lemma bundleCost_fiber {m n : ℕ} (v : Fin m → ℝ)
    (a : Fin m → Fin n) (i : Fin n) : bundleCost v (fiber a i) = load v a i := by
  classical
  simp only [bundleCost, mem_fiber, load]

@[simp] lemma bundleCost_singleton {m : ℕ} (v : Fin m → ℝ) (x : Fin m) :
    bundleCost v {x} = v x := by classical simp [bundleCost]

@[simp] lemma bundleCost_empty {m : ℕ} (v : Fin m → ℝ) : bundleCost v ∅ = 0 := by
  classical simp [bundleCost]

lemma bundleCost_erase {m : ℕ} (v : Fin m → ℝ) {S : Finset (Fin m)} {x : Fin m}
    (hx : x ∈ S) : bundleCost v (S.erase x) = bundleCost v S - v x := by
  classical
  rw [bundleCost_eq_sum, bundleCost_eq_sum, Finset.sum_erase_eq_sub hx]

lemma ExchangeStable.subset_le_other {m n : ℕ} {v : Fin m → ℝ}
    {a : Fin m → Fin n} (ha : ExchangeStable v a) {i j : Fin n}
    (hij : i ≠ j) {S : Finset (Fin m)} (hS : S ⊆ fiber a i)
    (hlt : bundleCost v S < load v a i) : bundleCost v S ≤ load v a j := by
  have h := ha.swap_obstruction hij
    (fun x hx => (mem_fiber a i x).1 (hS hx))
    (fun x hx => (mem_fiber a j x).1 hx)
    (S := S) (T := fiber a j)
  simpa using h (by simpa using hlt)

/-- The first crossing of a finite sum has overshoot smaller than one summand bound. -/
lemma exists_subset_sum_ge_lt {ι : Type*} [DecidableEq ι] (S : Finset ι) (v : ι → ℝ)
    {L p : ℝ} (hL : 0 < L) (hv : ∀ x ∈ S, v x < p) (hs : L ≤ ∑ x ∈ S, v x) :
    ∃ T ⊆ S, L ≤ ∑ x ∈ T, v x ∧ (∑ x ∈ T, v x) < L + p := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty] at hs; linarith
  | @insert x S hx ih =>
      by_cases hrest : L ≤ ∑ y ∈ S, v y
      · obtain ⟨T, hT, hTL, hTU⟩ := ih (fun y hy => hv y (Finset.mem_insert_of_mem hy)) hrest
        exact ⟨T, hT.trans (Finset.subset_insert x S), hTL, hTU⟩
      · refine ⟨insert x S, Finset.Subset.refl _, hs, ?_⟩
        rw [Finset.sum_insert hx]
        have hxv := hv x (Finset.mem_insert_self x S)
        linarith

/-- A largest item in one bin forces every other bin to lie within half its cost. -/
lemma ExchangeStable.gap_le_half_maximum {m n : ℕ} {v : Fin m → ℝ}
    {a : Fin m → Fin n} (ha : ExchangeStable v a) {i j : Fin n} {α : ℝ}
    (hij : i ≠ j) (hα : 0 < α) {x : Fin m} (hxi : a x = i) (hxα : v x = α)
    (hM : α < load v a i) (hstrict : ∀ y, a y = j → v y < α) :
    load v a i - load v a j ≤ α / 2 := by
  classical
  by_contra h
  have hgap : α / 2 < load v a i - load v a j := lt_of_not_ge h
  have hb : α ≤ load v a j := by
    have hh := ha.subset_le_other hij (S := {x}) (by simpa) (by simpa [hxα] using hM)
    simpa [hxα] using hh
  have hsub : ∀ T ⊆ fiber a j, bundleCost v T < α → bundleCost v T < α / 2 := by
    intro T hT hlt
    have hh := ha i j {x} T hij (by simpa) (fun y hy => (mem_fiber a j y).1 (hT hy))
      (by simpa [hxα] using hlt)
    simp only [bundleCost_singleton, hxα] at hh
    linarith
  have hsmall : ∀ y ∈ fiber a j, v y < α / 2 := by
    intro y hy
    have hh := hsub {y} (Finset.singleton_subset_iff.mpr hy)
      (by simpa using hstrict y ((mem_fiber a j y).1 hy))
    simpa using hh
  obtain ⟨T, hT, hTL, hTU⟩ := exists_subset_sum_ge_lt (fiber a j) v
    (L := α / 2) (p := α / 2) (by linarith) hsmall
    (by rw [← bundleCost_eq_sum, bundleCost_fiber]; linarith)
  have hh := hsub T hT (by rw [bundleCost_eq_sum]; linarith)
  rw [bundleCost_eq_sum] at hh
  linarith

lemma distinguished_load_bound {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n)
    (i : Fin n) (L : ℝ) (hL : ∀ j, j ≠ i → L ≤ load v a j) :
    load v a i + ((n : ℝ) - 1) * L ≤ ∑ x, v x := by
  classical
  have h : ∀ j, L + (if j = i then load v a i - L else 0) ≤ load v a j := by
    intro j
    by_cases hji : j = i
    · subst j; simp
    · simp only [if_neg hji, add_zero]; exact hL j hji
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
  rw [sum_load] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_pos] at hs
  linarith

lemma two_distinguished_load_bound {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n)
    (i j : Fin n) (hij : i ≠ j) (L J : ℝ) (hj : J ≤ load v a j)
    (hL : ∀ z, z ≠ i → z ≠ j → L ≤ load v a z) :
    load v a i + J + ((n : ℝ) - 2) * L ≤ ∑ x, v x := by
  classical
  have h : ∀ z, L + (if z = i then load v a i - L else 0) +
      (if z = j then J - L else 0) ≤ load v a z := by
    intro z
    by_cases hzi : z = i
    · subst z; simp [hij]
    · by_cases hzj : z = j
      · subst z; simpa [Ne.symm hij] using hj
      · simpa [hzi, hzj] using hL z hzi hzj
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun z _ => h z)
  rw [sum_load] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_pos] at hs
  linarith

noncomputable def positiveFiber {m n : ℕ} (v : Fin m → ℝ)
    (a : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  (fiber a i).filter fun x => 0 < v x

@[simp] lemma mem_positiveFiber {m n : ℕ} (v : Fin m → ℝ)
    (a : Fin m → Fin n) (i : Fin n) (x : Fin m) :
    x ∈ positiveFiber v a i ↔ a x = i ∧ 0 < v x := by
  classical simp [positiveFiber]

lemma positiveFiber_subset {m n : ℕ} (v : Fin m → ℝ)
    (a : Fin m → Fin n) (i : Fin n) : positiveFiber v a i ⊆ fiber a i := by
  exact Finset.filter_subset _ _

@[simp] lemma bundleCost_positiveFiber {m n : ℕ} {v : Fin m → ℝ}
    (hv : ∀ x, 0 ≤ v x) (a : Fin m → Fin n) (i : Fin n) :
    bundleCost v (positiveFiber v a i) = load v a i := by
  classical
  unfold bundleCost load
  apply Finset.sum_congr rfl
  intro x _
  simp only [mem_positiveFiber]
  by_cases hxi : a x = i
  · by_cases hxv : 0 < v x
    · simp [hxi, hxv]
    · have hx0 : v x = 0 := le_antisymm (le_of_not_gt hxv) (hv x)
      simp [hx0]
  · simp [hxi]

lemma ExchangeStable.complement_bound {m n : ℕ} {v : Fin m → ℝ}
    {a : Fin m → Fin n} (ha : ExchangeStable v a) {i j : Fin n} (hij : i ≠ j)
    {x : Fin m} (hxi : a x = i) (hx : 0 < v x) :
    load v a i - v x ≤ load v a j := by
  have hm : x ∈ fiber a i := (mem_fiber a i x).2 hxi
  have hh := ha.subset_le_other hij (S := (fiber a i).erase x)
    (Finset.erase_subset _ _) (by rw [bundleCost_erase v hm, bundleCost_fiber]; linarith)
  simpa only [bundleCost_erase v hm, bundleCost_fiber] using hh

lemma exists_item_le_fraction {m n k : ℕ} {v : Fin m → ℝ}
    (a : Fin m → Fin n) (i : Fin n) {α : ℝ} (hα : 0 < α)
    (hv : ∀ x, 0 ≤ v x ∧ v x ≤ α) (hM : ((k : ℝ) + 1) * α < load v a i) :
    ∃ x, a x = i ∧ 0 < v x ∧ ((k : ℝ) + 2) * v x ≤ load v a i := by
  classical
  let S := positiveFiber v a i
  have hsum : (∑ x ∈ S, v x) = load v a i := by
    rw [← bundleCost_eq_sum]; exact bundleCost_positiveFiber (fun x => (hv x).1) a i
  have hS : S.Nonempty := by
    by_contra hempty
    have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hz, Finset.sum_empty] at hsum
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image S v hS
  have hxmem := (mem_positiveFiber v a i x).1 hx
  have hcard : k + 2 ≤ S.card := by
    by_contra hc
    have hcn : S.card ≤ k + 1 := by omega
    have hcr : (S.card : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hcn
    have hsle : (∑ y ∈ S, v y) ≤ S.card * α := by
      calc
        _ ≤ ∑ _y ∈ S, α := Finset.sum_le_sum fun y _ => (hv y).2
        _ = _ := by simp
    rw [hsum] at hsle
    nlinarith
  have hminsum : (S.card : ℝ) * v x ≤ load v a i := by
    calc
      _ = ∑ _y ∈ S, v x := by simp
      _ ≤ ∑ y ∈ S, v y := Finset.sum_le_sum fun y hy => hmin y hy
      _ = _ := hsum
  refine ⟨x, hxmem.1, hxmem.2, ?_⟩
  have hcr : (k : ℝ) + 2 ≤ S.card := by exact_mod_cast hcard
  exact (mul_le_mul_of_nonneg_right hcr (le_of_lt hxmem.2)).trans hminsum

private lemma inside_maximum_arithmetic {q k α M : ℝ}
    (hq : 0 < q) (hk : 0 ≤ k) (hα : 0 < α) (hqk : k + 2 ≤ q * k)
    (hM : (k + 1) * α < M)
    (hD : (k + 2) * (1 - α) < M * (q * (k + 1)))
    (hs : M + (q - 1) * (M - α / 2) ≤ 1) : False := by
  have hscaled := mul_le_mul_of_nonneg_right hs (show 0 ≤ k + 2 by linarith)
  have hpositive := mul_lt_mul_of_pos_left hM hq
  have hcond := mul_nonneg (show 0 ≤ q * k - k - 2 by linarith) (le_of_lt hα)
  nlinarith

private lemma small_maximum_item_arithmetic {q k α M t : ℝ}
    (hq : 1 ≤ q) (hk : 0 ≤ k) (hα : 0 < α) (hqk : k + 1 ≤ q * k)
    (hM : (k + 1) * α < M)
    (hD : (k + 2) * (1 - α) < M * (q * (k + 1)))
    (hs : M + (q - 1) * (M - t) ≤ 1) : α / (k + 2) < t := by
  by_contra h
  have ht : (k + 2) * t ≤ α := by
    have ht' := (le_div_iff₀ (show 0 < k + 2 by linarith)).1 (le_of_not_gt h)
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hs (show 0 ≤ k + 2 by linarith)
  have htq := mul_le_mul_of_nonneg_left ht (show 0 ≤ q - 1 by linarith)
  have hpositive := mul_lt_mul_of_pos_left hM (show 0 < q by linarith)
  have hcond := mul_nonneg (show 0 ≤ q * k - k - 1 by linarith) (le_of_lt hα)
  nlinarith

/-- Generic packing step. The premise is the standalone finite subset-selection
lemma; it is not a premise identifying any formula with the Hill supremum. -/
theorem mms_le_envelope_of_selection {m n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    (hnk : k + 2 ≤ n * k) {v : Fin m → ℝ} {α : ℝ}
    (hα : 0 < α) (hv : IsNormalizedExact v α)
    (hselect : ∀ (S : Finset (Fin m)),
      (∀ x ∈ S, 0 < v x ∧ v x ≤ α) →
      ((k : ℝ) + 1) * α < (∑ x ∈ S, v x) →
      (∀ x ∈ S, α / ((k : ℝ) + 2) < v x) →
      ∃ U ⊆ S, (k : ℝ) * (∑ x ∈ S, v x) / ((k : ℝ) + 2) ≤ (∑ x ∈ U, v x) ∧
        (∑ x ∈ U, v x) < (∑ x ∈ S, v x) - α) :
    mms n v ≤ envelope n k 1 α := by
  classical
  obtain ⟨a, ha⟩ := exists_exchangeStable hn v
  apply (mms_le_iff hn v _).2
  refine ⟨a, ?_⟩
  intro i
  by_contra hbound
  have hM : ((k : ℝ) + 1) * α < load v a i :=
    (le_envelope_left n k 1 α).trans_lt (lt_of_not_ge hbound)
  have hD : ((k : ℝ) + 2) * (1 - α) < load v a i * ((n : ℝ) * ((k : ℝ) + 1)) := by
    have hh := (le_envelope_right n k 1 α).trans_lt (lt_of_not_ge hbound)
    rw [div_mul_eq_mul_div] at hh
    exact (div_lt_iff₀ (by positivity)).1 hh
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkr : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hnkR : (k : ℝ) + 2 ≤ (n : ℝ) * k := by exact_mod_cast hnk
  have hMα : α < load v a i := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  by_cases hout : ∃ x, a x ≠ i ∧ v x = α
  · obtain ⟨x, hxi, hxα⟩ := hout
    let j := a x
    have hij : i ≠ j := Ne.symm hxi
    let S := positiveFiber v a i
    have hSsum : (∑ y ∈ S, v y) = load v a i := by
      rw [← bundleCost_eq_sum]; exact bundleCost_positiveFiber (fun y => (hv.1 y).1) a i
    have hSbounds : ∀ y ∈ S, 0 < v y ∧ v y ≤ α := by
      intro y hy
      exact ⟨((mem_positiveFiber v a i y).1 hy).2, (hv.1 y).2⟩
    have hsmall : ∀ y ∈ S, α / ((k : ℝ) + 2) < v y := by
      intro y hy
      have hymem := (mem_positiveFiber v a i y).1 hy
      have hb := distinguished_load_bound v a i (load v a i - v y)
        (fun z hzi => ha.complement_bound (Ne.symm hzi) hymem.1 hymem.2)
      rw [hv.2.1] at hb
      exact small_maximum_item_arithmetic hn1 hkr hα (by linarith) hM hD hb
    obtain ⟨U, hU, hUL, hUU⟩ := hselect S hSbounds (by rwa [hSsum]) hsmall
    rw [hSsum] at hUL hUU
    have hUfiber : U ⊆ fiber a i := hU.trans (positiveFiber_subset v a i)
    have hremove : x ∈ fiber a j := by simp [j]
    have hJ : α + (k : ℝ) * load v a i / ((k : ℝ) + 2) ≤ load v a j := by
      have hh := ha.swap_obstruction hij
        (fun y hy => (mem_fiber a i y).1 (hUfiber hy))
        (fun y hy => (mem_fiber a j y).1 (Finset.mem_of_mem_erase hy))
        (S := U) (T := (fiber a j).erase x) ?_
      · rw [bundleCost_erase v hremove, bundleCost_fiber, hxα, bundleCost_eq_sum] at hh
        linarith
      · rw [bundleCost_erase v hremove, bundleCost_fiber, hxα, bundleCost_eq_sum]
        linarith
    obtain ⟨y, hyi, hyv, hymean⟩ := exists_item_le_fraction a i hα hv.1 hM
    have hL : ∀ z, z ≠ i → z ≠ j →
        (((k : ℝ) + 1) * load v a i / ((k : ℝ) + 2)) ≤ load v a z := by
      intro z hzi _
      have hb := ha.complement_bound (Ne.symm hzi) hyi hyv
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    have hsum := two_distinguished_load_bound v a i j hij
      (((k : ℝ) + 1) * load v a i / ((k : ℝ) + 2))
      (α + (k : ℝ) * load v a i / ((k : ℝ) + 2)) hJ hL
    rw [hv.2.1] at hsum
    have hden : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hscaled := (mul_le_mul_of_nonneg_right hsum (le_of_lt hden))
    have heq : (load v a i + (α + (k : ℝ) * load v a i / ((k : ℝ) + 2)) +
        ((n : ℝ) - 2) * (((k : ℝ) + 1) * load v a i / ((k : ℝ) + 2))) *
        ((k : ℝ) + 2) =
        load v a i * ((n : ℝ) * ((k : ℝ) + 1)) + ((k : ℝ) + 2) * α := by
      field_simp
      <;> ring
    rw [heq] at hscaled
    nlinarith
  · obtain ⟨x, hxα⟩ := hv.2.2
    have hxi : a x = i := by by_contra hxi; exact hout ⟨x, hxi, hxα⟩
    have hL : ∀ j, j ≠ i → load v a i - α / 2 ≤ load v a j := by
      intro j hji
      have hh := ha.gap_le_half_maximum (Ne.symm hji) hα hxi hxα hMα ?_
      · linarith
      · intro y hyj
        have hyi : a y ≠ i := by rw [hyj]; exact hji
        have hyne : v y ≠ α := by intro heq; exact hout ⟨y, hyi, heq⟩
        exact lt_of_le_of_ne (hv.1 y).2 hyne
    have hs := distinguished_load_bound v a i (load v a i - α / 2) hL
    rw [hv.2.1] at hs
    exact inside_maximum_arithmetic hnr hkr hα hnkR hM hD hs

/-- The zero-index envelope, including its small-maximum range. -/
theorem mms_le_envelope_zero {m n : ℕ} (hn : 2 ≤ n) {v : Fin m → ℝ} {α : ℝ}
    (hα : 0 < α) (hv : IsNormalizedExact v α) : mms n v ≤ envelope n 0 1 α := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hsmall : ((n : ℝ) + 1) * α ≤ 1
  · have hh := mms_le_balancing_bound hn0 (le_of_lt hα) hv.1
    rw [hv.2.1] at hh
    calc
      mms n v ≤ (1 + ((n : ℝ) - 1) * α) / n := hh
      _ ≤ 2 * (1 - α) / n := (div_le_div_iff_of_pos_right hnR).2 (by nlinarith)
      _ ≤ envelope n 0 1 α := by
        simpa [envelope, div_mul_eq_mul_div] using le_envelope_right n 0 1 α
  obtain ⟨a, ha⟩ := exists_exchangeStable hn0 v
  apply (mms_le_iff hn0 v _).2
  refine ⟨a, ?_⟩
  intro i
  by_contra hbound
  have hM : α < load v a i := by
    simpa using (le_envelope_left n 0 1 α).trans_lt (lt_of_not_ge hbound)
  have hD : 2 * (1 - α) < load v a i * n := by
    have hh := (le_envelope_right n 0 1 α).trans_lt (lt_of_not_ge hbound)
    simp only [Nat.cast_zero, zero_add, mul_one] at hh
    rw [div_mul_eq_mul_div] at hh
    exact (div_lt_iff₀ hnR).1 hh
  obtain ⟨x, hxα⟩ := hv.2.2
  by_cases hxi : a x = i
  · have hL : ∀ j, j ≠ i → α ≤ load v a j := by
      intro j hji
      have hh := ha.subset_le_other (Ne.symm hji) (S := {x}) (by simpa)
        (by simpa [hxα] using hM)
      simpa [hxα] using hh
    have hs := distinguished_load_bound v a i α hL
    rw [hv.2.1] at hs
    have hs' := mul_le_mul_of_nonneg_right hs (le_of_lt hnR)
    have hp := mul_nonneg (show 0 ≤ ((n : ℝ) + 1) * α - 1 by linarith)
      (show 0 ≤ (n : ℝ) - 2 by linarith)
    nlinarith
  · let j := a x
    have hij : i ≠ j := Ne.symm hxi
    have hJ : α ≤ load v a j := by
      rw [← hxα]
      exact item_le_load (fun y => (hv.1 y).1) a x
    obtain ⟨y, hyi, hyv, hymean⟩ := exists_item_le_fraction (k := 0) a i hα hv.1 (by simpa using hM)
    have hL : ∀ z, z ≠ i → z ≠ j → load v a i / 2 ≤ load v a z := by
      intro z hzi _
      have hb := ha.complement_bound (Ne.symm hzi) hyi hyv
      simp only [Nat.cast_zero, zero_add] at hymean
      linarith
    have hs := two_distinguished_load_bound v a i j hij (load v a i / 2) α hJ hL
    rw [hv.2.1] at hs
    nlinarith

end ExactHillShares
