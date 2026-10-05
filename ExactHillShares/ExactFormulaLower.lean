import ExactHillShares.Foundations
import ExactHillShares.Formula
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.FinCases

open scoped BigOperators

namespace ExactHillShares

/-- More than n*k items of cost at least b force some bin to contain k+1 of them. -/
theorem heavy_items_le_mms {m n k : ℕ} (hn : 0 < n) {v : Fin m → ℝ}
    (hv : ∀ j, 0 ≤ v j) {b : ℝ} (hb : 0 ≤ b) (S : Finset (Fin m))
    (hS : n * k < S.card) (hheavy : ∀ j ∈ S, b ≤ v j) :
    ((k : ℝ) + 1) * b ≤ mms n v := by
  classical
  apply (le_mms_iff hn v _).mpr
  intro a
  obtain ⟨i, _, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := Finset.univ) (f := a) (n := k)
    (fun _ _ => Finset.mem_univ _) (by simpa using hS)
  have hcard : (k : ℝ) + 1 ≤ (S.filter (fun j => a j = i)).card := by
    exact_mod_cast (show k + 1 ≤ (S.filter (fun j => a j = i)).card by omega)
  have hload : ((S.filter (fun j => a j = i)).card : ℝ) * b ≤ load v a i := by
    calc
      ((S.filter (fun j => a j = i)).card : ℝ) * b =
          ∑ j ∈ S.filter (fun j => a j = i), b := by simp
      _ ≤ ∑ j ∈ S.filter (fun j => a j = i), v j := Finset.sum_le_sum fun j hj =>
        hheavy j (Finset.mem_filter.mp hj).1
      _ = ∑ j ∈ S.filter (fun j => a j = i), if a j = i then v j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [(Finset.mem_filter.mp hj).2]
      _ ≤ ∑ j, if a j = i then v j else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (by intro j _ _; split_ifs; exact hv j; exact le_rfl)
      _ = load v a i := rfl
  exact le_trans (le_trans (mul_le_mul_of_nonneg_right hcard hb) hload)
    (load_le_allocationCost v a i)

/-- A normalized extremal instance for the increasing branch: n*k+1
maximum-size items and n small residual items. -/
theorem increasing_branch_le_hill {n k : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hlo : (k : ℝ) * ((n : ℝ) * α) ≤ 1 - α)
    (hhi : 1 - α ≤ ((k : ℝ) + 1) * ((n : ℝ) * α)) :
    ((k : ℝ) + 1) * α ≤ hill n α := by
  classical
  let N := n * k + 1
  let β : ℝ := (1 - (N : ℝ) * α) / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < N := by dsimp [N]; omega
  have hβ0 : 0 ≤ β := by
    apply div_nonneg _ (le_of_lt hnR)
    dsimp [N]
    push_cast
    nlinarith
  have hβα : β ≤ α := by
    apply (div_le_iff₀ hnR).mpr
    dsimp [N]
    push_cast
    nlinarith
  let v : Fin (N + n) → ℝ := Fin.addCases (fun _ => α) (fun _ => β)
  have hvbounds : ∀ j, 0 ≤ v j ∧ v j ≤ α := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa [v] using (And.intro (le_of_lt hα) (le_refl α))
    · intro i
      simpa [v] using (And.intro hβ0 hβα)
  have hv : IsNormalizedExact v α := by
    refine ⟨hvbounds, ?_, ?_⟩
    · rw [Fin.sum_univ_add]
      simp only [v, Fin.addCases_left, Fin.addCases_right, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [β]
      field_simp
      <;> ring
    · exact ⟨Fin.castAdd n ⟨0, hN⟩, by simp [v]⟩
  let S : Finset (Fin (N + n)) := Finset.univ.image (Fin.castAdd n)
  have hScard : S.card = N := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ (Fin.castAdd_injective _ _)]
    simp
  have hheavy : ∀ j ∈ S, α ≤ v j := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    simp [v]
  exact le_trans (heavy_items_le_mms hn (fun j => (hvbounds j).1) (le_of_lt hα)
    S (by rw [hScard]; dsimp [N]; omega) hheavy) (mms_le_hill hn hv)

/-- A normalized extremal instance for the decreasing branch: one maximum
item and n*(k+1) equal items.  All n*(k+1)+1 items are at least the latter size. -/
theorem decreasing_branch_le_hill {n k : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hhi : 1 - α ≤ ((k : ℝ) + 1) * ((n : ℝ) * α)) :
    (((k : ℝ) + 2) / ((n : ℝ) * ((k : ℝ) + 1))) * (1 - α) ≤ hill n α := by
  classical
  let N := n * (k + 1)
  let β : ℝ := (1 - α) / N
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < N := by dsimp [N]; positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ0 : 0 ≤ β := div_nonneg (sub_nonneg.mpr hα1) (le_of_lt hNR)
  have hβα : β ≤ α := by
    apply (div_le_iff₀ hNR).mpr
    dsimp [N]
    push_cast
    nlinarith
  let v : Fin (N + 1) → ℝ := Fin.cases α (fun _ => β)
  have hvbounds : ∀ j, 0 ≤ v j ∧ v j ≤ α := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact ⟨le_of_lt hα, le_rfl⟩
    · exact ⟨hβ0, hβα⟩
  have hv : IsNormalizedExact v α := by
    refine ⟨hvbounds, ?_, ⟨0, rfl⟩⟩
    simp only [v, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [β]
    field_simp
  have hheavy : ∀ j ∈ (Finset.univ : Finset (Fin (N + 1))), β ≤ v j := by
    intro j _
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hβα
    · exact le_rfl
  have hlower := heavy_items_le_mms (k := k + 1) hn
    (fun j => (hvbounds j).1) hβ0 Finset.univ
    (by simp only [Finset.card_univ, Fintype.card_fin]; dsimp [N]; omega) hheavy
  have heq : (((k + 1 : ℕ) : ℝ) + 1) * β =
      (((k : ℝ) + 2) / ((n : ℝ) * ((k : ℝ) + 1))) * (1 - α) := by
    dsimp [β, N]
    push_cast
    field_simp
    <;> ring
    <;> simp
  rw [heq] at hlower
  exact hlower.trans (mms_le_hill hn hv)

/-- The closed-form lower bound is witnessed by actual finite normalized
valuations, independently of the upper-bound packing theorem. -/
theorem multiFormula_le_hill {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) : multiFormula n 1 α ≤ hill n α := by
  obtain ⟨hlo, hhi⟩ := formulaIndex_bounds hn hα hα1
  unfold multiFormula envelope
  apply max_le
  · exact increasing_branch_le_hill hn hα hα1 hlo (le_of_lt hhi)
  · exact decreasing_branch_le_hill hn hα hα1 (le_of_lt hhi)

/-- The six-object exceptional two-agent construction, checked for every
allocation by its two possible load counts around the distinguished object. -/
theorem six_item_lower {α β : ℝ} (hβ : 0 ≤ β) (hαβ : α ≤ 2 * β) :
    α + 2 * β ≤ mms 2 (Fin.cases α (fun _ : Fin 5 => β)) := by
  classical
  let v : Fin 6 → ℝ := Fin.cases α (fun _ => β)
  change α + 2 * β ≤ mms 2 v
  apply (le_mms_iff (by norm_num) v _).mpr
  intro a
  let c : ℕ := (Finset.univ.filter (fun j : Fin 5 => a j.succ = a 0)).card
  have hload : load v a (a 0) = α + (c : ℝ) * β := by
    unfold load
    rw [Fin.sum_univ_succ]
    simp only [v, Fin.cases_zero, Fin.cases_succ, if_pos rfl]
    rw [← Finset.sum_filter]
    simp [c]
  by_cases hc : 2 ≤ c
  · have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
    exact le_trans (by nlinarith) (load_le_allocationCost v a (a 0))
  · have hcR : (c : ℝ) ≤ 1 := by exact_mod_cast (show c ≤ 1 by omega)
    have hsmall : load v a (a 0) ≤ α + β := by nlinarith
    have htotal : load v a 0 + load v a 1 = α + 5 * β := by
      simpa [Fin.sum_univ_two, v, Fin.sum_univ_succ] using sum_load v a
    have ha0 := load_le_allocationCost v a (0 : Fin 2)
    have ha1 := load_le_allocationCost v a (1 : Fin 2)
    generalize heq : a 0 = i at hsmall
    fin_cases i
    · change load v a 0 ≤ α + β at hsmall
      linarith
    · change load v a 1 ≤ α + β at hsmall
      linarith

/-- The special middle branch of the two-agent formula is realized by one
item of size α and five equal items of size (1−α)/5. -/
theorem exceptional_branch_le_hill {α : ℝ}
    (hlo : 7 / 27 ≤ α) (hhi : α ≤ 2 / 7) :
    (2 + 3 * α) / 5 ≤ hill 2 α := by
  let β : ℝ := (1 - α) / 5
  have hα : 0 < α := by linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hβα : β ≤ α := by dsimp [β]; linarith
  have hαβ : α ≤ 2 * β := by dsimp [β]; linarith
  let v : Fin 6 → ℝ := Fin.cases α (fun _ => β)
  have hv : IsNormalizedExact v α := by
    refine ⟨?_, ?_, ⟨0, rfl⟩⟩
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact ⟨le_of_lt hα, le_rfl⟩
      · exact ⟨hβ, hβα⟩
    · simp [v, Fin.sum_univ_succ, β]
      ring
  have hlow : α + 2 * β ≤ mms 2 v := six_item_lower hβ hαβ
  have heq : α + 2 * β = (2 + 3 * α) / 5 := by dsimp [β]; ring
  rw [heq] at hlow
  exact hlow.trans (mms_le_hill (by norm_num) hv)

/-- All five pieces of the exact two-agent formula are attained as lower
bounds by genuine normalized finite valuations. -/
theorem twoFormula_le_hill {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    twoFormula α ≤ hill 2 α := by
  unfold twoFormula
  split_ifs with h1 h2 h3 h4
  · apply max_le (maximum_le_hill (by norm_num) hα hα1)
    have hh := decreasing_branch_le_hill (n := 2) (k := 0) (by norm_num) hα hα1
      (by norm_num; linarith)
    norm_num at hh
    linarith
  · have hh := increasing_branch_le_hill (n := 2) (k := 1) (by norm_num) hα hα1
      (by norm_num; linarith) (by norm_num; linarith)
    norm_num at hh
    exact hh
  · exact exceptional_branch_le_hill h3 (le_of_lt (lt_of_not_ge h2))
  · have hh := decreasing_branch_le_hill (n := 2) (k := 1) (by norm_num) hα hα1
      (by norm_num; linarith)
    norm_num at hh
    convert hh using 1 <;> ring
  · exact multiFormula_le_hill (by norm_num) hα hα1

end ExactHillShares
