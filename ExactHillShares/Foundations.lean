import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Finite additive costs and the semantic exact-maximum Hill share

These definitions are independent of any closed-form formula. In particular `hill` is
an actual supremum over all finite, normalized, nonnegative valuations attaining the
specified largest item. Allocations are arbitrary maps from items to bins; empty bins
are permitted.
-/

open scoped BigOperators

namespace ExactHillShares

/-- The cost of one bin of an allocation. -/
noncomputable def load {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n) (i : Fin n) : ℝ :=
  ∑ j, if a j = i then v j else 0

/-- The largest bin cost. All substantive results below assume at least one bin. -/
noncomputable def allocationCost (n : ℕ) {m : ℕ} (v : Fin m → ℝ)
    (a : Fin m → Fin n) : ℝ := sSup (Set.range (load v a))

/-- The minimax share of a finite valuation, minimizing over every allocation. -/
noncomputable def mms (n : ℕ) {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  sInf (Set.range (allocationCost n v))

/-- Nonnegative, normalized costs with exact maximum `α`. -/
def IsNormalizedExact {m : ℕ} (v : Fin m → ℝ) (α : ℝ) : Prop :=
  (∀ j, 0 ≤ v j ∧ v j ≤ α) ∧ (∑ j, v j) = 1 ∧ ∃ j, v j = α

/-- The set of genuine minimax shares with the given exact maximum. -/
def hillValues (n : ℕ) (α : ℝ) : Set ℝ :=
  {d | ∃ (m : ℕ) (v : Fin m → ℝ), IsNormalizedExact v α ∧ mms n v = d}

/-- Exact-maximum Hill share: a supremum over finite normalized valuations. -/
noncomputable def hill (n : ℕ) (α : ℝ) : ℝ := sSup (hillValues n α)

/-- Homogeneous Hill bound used for residual instances of total mass `T`. -/
noncomputable def hillBound (n : ℕ) (T p : ℝ) : ℝ := T * hill n (p / T)

lemma load_nonneg {m n : ℕ} {v : Fin m → ℝ} (hv : ∀ j, 0 ≤ v j)
    (a : Fin m → Fin n) (i : Fin n) : 0 ≤ load v a i := by
  classical
  unfold load
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hv j
  · exact le_rfl

lemma sum_load {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n) :
    ∑ i, load v a i = ∑ j, v j := by
  classical
  unfold load
  rw [Finset.sum_comm]
  simp

lemma load_le_total {m n : ℕ} {v : Fin m → ℝ} (hv : ∀ j, 0 ≤ v j)
    (a : Fin m → Fin n) (i : Fin n) : load v a i ≤ ∑ j, v j := by
  classical
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> simp_all

lemma item_le_load {m n : ℕ} {v : Fin m → ℝ} (hv : ∀ j, 0 ≤ v j)
    (a : Fin m → Fin n) (j : Fin m) : v j ≤ load v a (a j) := by
  classical
  unfold load
  calc
    v j = (if a j = a j then v j else 0) := by simp
    _ ≤ ∑ k, if a k = a j then v k else 0 :=
      Finset.single_le_sum (f := fun k => if a k = a j then v k else 0)
        (fun k _ => by dsimp only; split_ifs; exact hv k; exact le_rfl) (Finset.mem_univ j)

lemma load_le_allocationCost {m n : ℕ} (v : Fin m → ℝ)
    (a : Fin m → Fin n) (i : Fin n) : load v a i ≤ allocationCost n v a := by
  exact le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩

lemma allocationCost_le_iff {m n : ℕ} (hn : 0 < n) (v : Fin m → ℝ)
    (a : Fin m → Fin n) (b : ℝ) :
    allocationCost n v a ≤ b ↔ ∀ i, load v a i ≤ b := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · intro h i
    exact (load_le_allocationCost v a i).trans h
  · intro h
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨i, rfl⟩; exact h i)

lemma allocationCost_attained {m n : ℕ} (hn : 0 < n) (v : Fin m → ℝ)
    (a : Fin m → Fin n) : ∃ i, load v a i = allocationCost n v a := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (Set.range_nonempty _).csSup_mem (Set.finite_range _)

lemma allocationCost_nonneg {m n : ℕ} (hn : 0 < n) {v : Fin m → ℝ}
    (hv : ∀ j, 0 ≤ v j) (a : Fin m → Fin n) : 0 ≤ allocationCost n v a :=
  (load_nonneg hv a ⟨0, hn⟩).trans (load_le_allocationCost v a ⟨0, hn⟩)

lemma allocationCost_le_total {m n : ℕ} (hn : 0 < n) {v : Fin m → ℝ}
    (hv : ∀ j, 0 ≤ v j) (a : Fin m → Fin n) : allocationCost n v a ≤ ∑ j, v j :=
  (allocationCost_le_iff hn v a _).2 (load_le_total hv a)

lemma mms_le_allocationCost {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n) :
    mms n v ≤ allocationCost n v a :=
  csInf_le (Set.finite_range _).bddBelow ⟨a, rfl⟩

lemma mms_attained {m n : ℕ} (hn : 0 < n) (v : Fin m → ℝ) :
    ∃ a : Fin m → Fin n, allocationCost n v a = mms n v := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (Set.range_nonempty _).csInf_mem (Set.finite_range _)

lemma mms_le_iff {m n : ℕ} (hn : 0 < n) (v : Fin m → ℝ) (b : ℝ) :
    mms n v ≤ b ↔ ∃ a : Fin m → Fin n, ∀ i, load v a i ≤ b := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := mms_attained hn v
    exact ⟨a, (allocationCost_le_iff hn v a b).1 (ha.trans_le h)⟩
  · rintro ⟨a, ha⟩
    exact (mms_le_allocationCost v a).trans ((allocationCost_le_iff hn v a b).2 ha)

lemma le_mms_iff {m n : ℕ} (hn : 0 < n) (v : Fin m → ℝ) (b : ℝ) :
    b ≤ mms n v ↔ ∀ a : Fin m → Fin n, b ≤ allocationCost n v a := by
  constructor
  · intro h a
    exact h.trans (mms_le_allocationCost v a)
  · intro h
    obtain ⟨a, ha⟩ := mms_attained hn v
    simpa only [ha] using h a

lemma mms_nonneg {m n : ℕ} (hn : 0 < n) {v : Fin m → ℝ}
    (hv : ∀ j, 0 ≤ v j) : 0 ≤ mms n v :=
  (le_mms_iff hn v 0).2 (allocationCost_nonneg hn hv)

lemma mms_le_total {m n : ℕ} (hn : 0 < n) {v : Fin m → ℝ}
    (hv : ∀ j, 0 ≤ v j) : mms n v ≤ ∑ j, v j := by
  let a : Fin m → Fin n := fun _ => ⟨0, hn⟩
  exact (mms_le_allocationCost v a).trans (allocationCost_le_total hn hv a)

lemma item_le_mms {m n : ℕ} (hn : 0 < n) {v : Fin m → ℝ}
    (hv : ∀ j, 0 ≤ v j) (j : Fin m) : v j ≤ mms n v := by
  apply (le_mms_iff hn v (v j)).2
  intro a
  exact (item_le_load hv a j).trans (load_le_allocationCost v a (a j))

lemma total_le_mul_mms {m n : ℕ} (hn : 0 < n) (v : Fin m → ℝ) :
    (∑ j, v j) ≤ n * mms n v := by
  obtain ⟨a, ha⟩ := mms_attained hn v
  calc
    (∑ j, v j) = ∑ i, load v a i := (sum_load v a).symm
    _ ≤ ∑ _i : Fin n, mms n v := Finset.sum_le_sum fun i _ => by
      simpa only [ha] using load_le_allocationCost v a i
    _ = n * mms n v := by simp

lemma load_smul {m n : ℕ} (c : ℝ) (v : Fin m → ℝ)
    (a : Fin m → Fin n) (i : Fin n) :
    load (fun j => c * v j) a i = c * load v a i := by
  classical
  simp only [load, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma allocationCost_smul {m n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 ≤ c)
    (v : Fin m → ℝ) (a : Fin m → Fin n) :
    allocationCost n (fun j => c * v j) a = c * allocationCost n v a := by
  apply le_antisymm
  · apply (allocationCost_le_iff hn _ _ _).2
    intro i
    rw [load_smul]
    exact mul_le_mul_of_nonneg_left (load_le_allocationCost v a i) hc
  · obtain ⟨i, hi⟩ := allocationCost_attained hn v a
    calc
      c * allocationCost n v a = c * load v a i := by rw [hi]
      _ = load (fun j => c * v j) a i := (load_smul c v a i).symm
      _ ≤ allocationCost n (fun j => c * v j) a := load_le_allocationCost _ _ _

lemma mms_smul {m n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 ≤ c)
    (v : Fin m → ℝ) : mms n (fun j => c * v j) = c * mms n v := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := mms_attained hn v
    calc
      mms n (fun j => c * v j) ≤ allocationCost n (fun j => c * v j) a :=
        mms_le_allocationCost _ _
      _ = c * mms n v := by rw [allocationCost_smul hn hc, ha]
  · apply (le_mms_iff hn _ _).2
    intro a
    rw [allocationCost_smul hn hc]
    exact mul_le_mul_of_nonneg_left (mms_le_allocationCost v a) hc

lemma hillValues_bddAbove {n : ℕ} (hn : 0 < n) (α : ℝ) :
    BddAbove (hillValues n α) := by
  refine ⟨1, ?_⟩
  rintro d ⟨m, v, hv, rfl⟩
  simpa only [hv.2.1] using mms_le_total hn (fun j => (hv.1 j).1)

lemma mms_le_hill {m n : ℕ} (hn : 0 < n) {v : Fin m → ℝ} {α : ℝ}
    (hv : IsNormalizedExact v α) : mms n v ≤ hill n α :=
  le_csSup (hillValues_bddAbove hn α) ⟨m, v, hv, rfl⟩

/-- There is a finite valuation with every prescribed exact maximum in `(0,1]`. -/
lemma exists_normalizedExact {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ (m : ℕ) (v : Fin m → ℝ), IsNormalizedExact v α := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / α)
  have hNr : (0 : ℝ) < N := lt_trans (one_div_pos.mpr hα) hN
  have hNz : (N : ℝ) ≠ 0 := ne_of_gt hNr
  have hmass : 1 ≤ (N : ℝ) * α := by
    exact le_of_lt ((div_lt_iff₀ hα).mp hN)
  let β : ℝ := (1 - α) / N
  have hβ0 : 0 ≤ β := div_nonneg (sub_nonneg.mpr hα1) (le_of_lt hNr)
  have hβα : β ≤ α := by
    apply (div_le_iff₀ hNr).2
    nlinarith
  let v : Fin (N + 1) → ℝ := Fin.cases α (fun _ => β)
  refine ⟨N + 1, v, ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact ⟨le_of_lt hα, le_rfl⟩
    · exact ⟨hβ0, hβα⟩
  · simp only [v, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [β]
    field_simp
    <;> ring
  · exact ⟨0, rfl⟩

lemma hillValues_nonempty (n : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (hillValues n α).Nonempty := by
  obtain ⟨m, v, hv⟩ := exists_normalizedExact hα hα1
  exact ⟨mms n v, m, v, hv, rfl⟩

lemma hill_le_iff {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (b : ℝ) :
    hill n α ≤ b ↔ ∀ (m : ℕ) (v : Fin m → ℝ), IsNormalizedExact v α → mms n v ≤ b := by
  constructor
  · intro h m v hv
    exact (mms_le_hill hn hv).trans h
  · intro h
    apply csSup_le (hillValues_nonempty n hα hα1)
    rintro d ⟨m, v, hv, rfl⟩
    exact h m v hv

lemma hill_le_one {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) : hill n α ≤ 1 := by
  apply (hill_le_iff hn hα hα1 1).2
  intro m v hv
  simpa only [hv.2.1] using mms_le_total hn (fun j => (hv.1 j).1)

lemma maximum_le_hill {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) : α ≤ hill n α := by
  obtain ⟨m, v, hv⟩ := exists_normalizedExact hα hα1
  obtain ⟨j, hj⟩ := hv.2.2
  calc
    α = v j := hj.symm
    _ ≤ mms n v := item_le_mms hn (fun j => (hv.1 j).1) j
    _ ≤ hill n α := mms_le_hill hn hv

lemma hill_pos {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) : 0 < hill n α :=
  hα.trans_le (maximum_le_hill hn hα hα1)

lemma one_le_mul_hill {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) : 1 ≤ n * hill n α := by
  obtain ⟨m, v, hv⟩ := exists_normalizedExact hα hα1
  calc
    1 = ∑ j, v j := hv.2.1.symm
    _ ≤ n * mms n v := total_le_mul_mms hn v
    _ ≤ n * hill n α := mul_le_mul_of_nonneg_left (mms_le_hill hn hv) (Nat.cast_nonneg n)

/-- Every concrete valuation has a partition below its exact-maximum Hill share. -/
lemma exists_hill_allocation {m n : ℕ} (hn : 0 < n) {v : Fin m → ℝ} {α : ℝ}
    (hv : IsNormalizedExact v α) :
    ∃ a : Fin m → Fin n, ∀ i, load v a i ≤ hill n α :=
  (mms_le_iff hn v _).1 (mms_le_hill hn hv)

/-- Normalizing total mass and the largest item preserves the exact constraint. -/
lemma normalizedExact_div_total {m : ℕ} {v : Fin m → ℝ} {T p : ℝ}
    (hT : 0 < T) (hv : ∀ j, 0 ≤ v j ∧ v j ≤ p)
    (hsum : (∑ j, v j) = T) (hp : ∃ j, v j = p) :
    IsNormalizedExact (fun j => T⁻¹ * v j) (p / T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    constructor
    · exact mul_nonneg (inv_nonneg.mpr (le_of_lt hT)) (hv j).1
    · simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_left (hv j).2 (inv_nonneg.mpr (le_of_lt hT))
  · rw [← Finset.mul_sum, hsum, inv_mul_cancel₀ (ne_of_gt hT)]
  · obtain ⟨j, hj⟩ := hp
    exact ⟨j, by change T⁻¹ * v j = p / T; rw [hj]; ring⟩

lemma mms_le_hillBound {m n : ℕ} (hn : 0 < n) {v : Fin m → ℝ} {T p : ℝ}
    (hT : 0 < T) (hv : ∀ j, 0 ≤ v j ∧ v j ≤ p)
    (hsum : (∑ j, v j) = T) (hp : ∃ j, v j = p) :
    mms n v ≤ hillBound n T p := by
  have h := mms_le_hill hn (normalizedExact_div_total hT hv hsum hp)
  rw [mms_smul hn (inv_nonneg.mpr (le_of_lt hT))] at h
  have hh := mul_le_mul_of_nonneg_left h (le_of_lt hT)
  simpa only [hillBound, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hT), one_mul] using hh

end ExactHillShares
