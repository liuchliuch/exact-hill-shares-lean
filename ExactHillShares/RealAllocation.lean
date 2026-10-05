import ExactHillShares.Algorithm
import ExactHillShares.ExactFormula
import ExactHillShares.OrderedTail
import ExactHillShares.OrderedReduction
import ExactHillShares.RealCutChoose

/-! # Simultaneous exact Hill allocations for arbitrary real-valued costs

This existence proof uses finite moving-knife recursion over the real numbers.
The two-agent base uses an attained exact minimax partition, followed by
cut-and-choose. No rationality or approximation hypothesis is imposed.
-/
namespace ExactHillShares.RealAllocation
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A total-mass-safe extension at degenerate inputs and one remaining agent. -/
def bound (q : ℕ) (T p : ℝ) : ℝ :=
  if T = 0 then 0 else if q ≤ 1 then T else numericalBound q T p

lemma bound_eq {q : ℕ} (hq : 2 ≤ q) {T p : ℝ} (hT : T ≠ 0) :
    bound q T p = numericalBound q T p := by
  simp [bound, hT, show ¬ q ≤ 1 by omega]

/-- Sum of exactly `k` successive entries beginning at `l`. -/
def mass (c : ℕ → ℝ) (l : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => c l + mass c (l + 1) k

@[simp] theorem mass_zero (c l) : mass c l 0 = 0 := rfl
@[simp] theorem mass_succ (c l k) : mass c l (k + 1) = c l + mass c (l + 1) k := rfl

lemma mass_eq_sum (c : ℕ → ℝ) (l k : ℕ) :
    mass c l k = ∑ j ∈ Finset.range k, c (l + j) := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [mass_succ, Finset.sum_range_succ', ih, add_comm]
    simp only [Nat.add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    omega

lemma mass_append (c : ℕ → ℝ) (l s k : ℕ) :
    mass c l (s + k) = mass c l s + mass c (l + s) k := by
  induction s generalizing l with
  | zero => simp
  | succ s ih =>
    rw [show s + 1 + k = (s + k) + 1 by omega, mass_succ, ih, mass_succ]
    simp only [show l + 1 + s = l + (s + 1) by omega]
    ring

lemma mass_nonneg (c : ℕ → ℝ) (l k : ℕ) (hn : ∀ j, 0 ≤ c j) :
    0 ≤ mass c l k := by
  rw [mass_eq_sum]
  exact Finset.sum_nonneg fun j hj => hn _

lemma mass_mono (c : ℕ → ℝ) (l : ℕ) (hn : ∀ j, 0 ≤ c j) :
    Monotone (mass c l) := by
  intro s k hsk
  rw [← Nat.add_sub_of_le hsk, mass_append]
  exact le_add_of_nonneg_right (mass_nonneg _ _ _ hn)

/-- First strict crossing, represented by the number of safe preceding items.
The implementation visits each item at most once, subtracting its cost from the
remaining threshold. Equality is safe, so the stopping comparison is strict. -/
def safePrefix (c : ℕ → ℝ) (l : ℕ) : ℕ → ℝ → ℕ
  | 0, _ => 0
  | k + 1, d => if c l ≤ d then 1 + safePrefix c (l + 1) k (d - c l) else 0

theorem safePrefix_le (c l k d) : safePrefix c l k d ≤ k := by
  induction k generalizing l d with
  | zero => simp [safePrefix]
  | succ k ih =>
    simp only [safePrefix]
    split
    · have := ih (l + 1) (d - c l); omega
    · omega

/-- Both defining properties of the first strict crossing are proved directly
from the scanning implementation. -/
theorem safePrefix_spec (c : ℕ → ℝ) (l k : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    mass c l (safePrefix c l k d) ≤ d ∧
    (safePrefix c l k d < k → d < mass c l (safePrefix c l k d + 1)) := by
  induction k generalizing l d with
  | zero => simp [safePrefix, hd]
  | succ k ih =>
    simp only [safePrefix]
    split_ifs with h
    · obtain ⟨hb, hc⟩ := ih (l + 1) (d - c l) (by linarith)
      rw [Nat.add_comm 1, mass_succ]
      constructor
      · linarith
      · intro hk
        have hk' : safePrefix c (l + 1) k (d - c l) < k := by omega
        have hh := hc hk'
        rw [mass_succ]
        linarith
    · simp only [mass_zero, zero_add, mass_succ]
      exact ⟨hd, fun _ => by linarith⟩

theorem safePrefix_lt (c : ℕ → ℝ) (l k : ℕ) (d : ℝ)
    (hd : 0 ≤ d) (hcross : d < mass c l k) : safePrefix c l k d < k := by
  have hs := safePrefix_le c l k d
  have hb := (safePrefix_spec c l k d hd).1
  by_contra h
  have he : safePrefix c l k d = k := by omega
  rw [he] at hb
  linarith

/-- The finite argmax is evaluated using exact integer lengths; ties are broken
by agent identifier. -/
def maxCandidates {n : ℕ} (A : Finset (Fin n)) (f : Fin n → ℕ) : Finset (Fin n) :=
  let top := A.sup f
  A.filter (fun i => f i = top)

def pickMax {n : ℕ} (A : Finset (Fin n)) (f : Fin n → ℕ) : Option (Fin n) :=
  let candidates := maxCandidates A f
  if h : candidates.Nonempty then some (candidates.min' h) else none

theorem pickMax_spec {n : ℕ} (A : Finset (Fin n)) (f : Fin n → ℕ)
    (hA : A.Nonempty) :
    ∃ a, pickMax A f = some a ∧ a ∈ A ∧ ∀ i ∈ A, f i ≤ f a := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup A hA f
  have hh : (maxCandidates A f).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩
  let a := (maxCandidates A f).min' hh
  have ha := Finset.mem_filter.mp (Finset.min'_mem (maxCandidates A f) hh)
  refine ⟨a, by simp [pickMax, hh, a], ha.1, ?_⟩
  intro i hi
  exact (Finset.le_sup hi).trans_eq ha.2.symm

/-- A total item-to-agent function is represented implicitly. `none` is used
only outside the input suffix; the validity theorem excludes it inside. -/
abbrev Allocation (n : ℕ) := ℕ → Option (Fin n)

def Valid {n : ℕ} (A : Finset (Fin n)) (l k : ℕ) (a : Allocation n) : Prop :=
  (∀ r, l ≤ r → r < l + k → ∃ i ∈ A, a r = some i) ∧
  (∀ r, r < l ∨ l + k ≤ r → a r = none)

def charge {n : ℕ} (c : Fin n → ℕ → ℝ) (l k : ℕ)
    (a : Allocation n) (i : Fin n) : ℝ :=
  mass (fun r => if a r = some i then c i r else 0) l k

def whole {n : ℕ} (a : Fin n) (l k : ℕ) : Allocation n :=
  fun r => if l ≤ r ∧ r < l + k then some a else none

def splice {n : ℕ} (a : Fin n) (l s : ℕ) (tail : Allocation n) : Allocation n :=
  fun r => if l ≤ r ∧ r < l + s then some a else tail r

lemma mass_congr {c d : ℕ → ℝ} {l k : ℕ}
    (h : ∀ r, l ≤ r → r < l + k → c r = d r) : mass c l k = mass d l k := by
  simp only [mass_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact h _ (by omega) (by have := Finset.mem_range.mp hj; omega)

@[simp] lemma mass_const_zero (l k : ℕ) : mass (fun _ => 0) l k = 0 := by
  simp [mass_eq_sum]

lemma whole_valid {n : ℕ} {A : Finset (Fin n)} {a : Fin n} (ha : a ∈ A) (l k : ℕ) :
    Valid A l k (whole a l k) := by
  constructor
  · intro r hl hr
    exact ⟨a, ha, by simp [whole, hl, hr]⟩
  · intro r h
    simp only [whole]
    split <;> simp_all <;> omega

lemma charge_whole {n : ℕ} (c : Fin n → ℕ → ℝ) (a i : Fin n) (l k : ℕ) :
    charge c l k (whole a l k) i = if a = i then mass (c i) l k else 0 := by
  unfold charge
  by_cases hai : a = i
  · rw [if_pos hai]
    apply mass_congr
    intro r hl hr
    simp [whole, hl, hr, hai]
  · rw [if_neg hai]
    rw [← mass_const_zero l k]
    apply mass_congr
    intro r hl hr
    simp [whole, hl, hr, hai]

lemma splice_valid {n : ℕ} {A : Finset (Fin n)} {a : Fin n} (ha : a ∈ A)
    {l s k : ℕ} (hsk : s ≤ k) {tail : Allocation n}
    (ht : Valid (A.erase a) (l + s) (k - s) tail) :
    Valid A l k (splice a l s tail) := by
  constructor
  · intro r hl hr
    by_cases hs : r < l + s
    · exact ⟨a, ha, by simp [splice, hl, hs]⟩
    · obtain ⟨i, hi, hei⟩ := ht.1 r (by omega) (by omega)
      exact ⟨i, Finset.mem_of_mem_erase hi, by simp [splice, hs, hei]⟩
  · intro r hr
    have hp : ¬ (l ≤ r ∧ r < l + s) := by omega
    have ht' : tail r = none := ht.2 r (by omega)
    simp [splice, hp, ht']

/-- No item is duplicated by concatenating the safe prefix and the recursive
suffix, and the exact charge decomposes into those two contributions. -/
lemma charge_splice {n : ℕ} (c : Fin n → ℕ → ℝ) (a i : Fin n)
    (l s k : ℕ) (hsk : s ≤ k) (tail : Allocation n) :
    charge c l k (splice a l s tail) i =
      (if a = i then mass (c i) l s else 0) + charge c (l + s) (k - s) tail i := by
  unfold charge
  rw [← Nat.add_sub_of_le hsk, mass_append]
  simp only [Nat.add_sub_cancel_left]
  congr 1
  · by_cases hai : a = i
    · rw [if_pos hai]
      apply mass_congr
      intro r hl hr
      simp [splice, hl, hr, hai]
    · rw [if_neg hai, ← mass_const_zero l s]
      apply mass_congr
      intro r hl hr
      simp [splice, hl, hr, hai]
  · apply mass_congr
    intro r hl hr
    simp [splice, show ¬ (l ≤ r ∧ r < l + s) by omega]

lemma charge_erased {n : ℕ} (c : Fin n → ℕ → ℝ)
    {A : Finset (Fin n)} {a : Fin n} {l k : ℕ} {tail : Allocation n}
    (ht : Valid (A.erase a) l k tail) : charge c l k tail a = 0 := by
  unfold charge
  rw [← mass_const_zero l k]
  apply mass_congr
  intro r hl hr
  obtain ⟨i, hi, he⟩ := ht.1 r hl hr
  have hne := (Finset.mem_erase.mp hi).1
  simp [he, hne]

lemma mass_le_head (c : ℕ → ℝ) (l k : ℕ) (ha : Antitone c) :
    mass c l k ≤ (k : ℝ) * c l := by
  rw [mass_eq_sum]
  calc
    (∑ j ∈ Finset.range k, c (l + j)) ≤ ∑ _j ∈ Finset.range k, c l :=
      Finset.sum_le_sum fun j hj => ha (by omega)
    _ = _ := by simp

lemma head_pos (c : ℕ → ℝ) (l k : ℕ) (ha : Antitone c)
    (hT : 0 < mass c l k) : 0 < c l := by
  have h := mass_le_head c l k ha
  by_contra hp
  have hh : (k : ℝ) * c l ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_gt hp)
  linarith

lemma head_le_mass (c : ℕ → ℝ) (l k : ℕ) (hn : ∀ j, 0 ≤ c j) (hk : 0 < k) :
    c l ≤ mass c l k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [mass_succ]
  exact le_add_of_nonneg_right (mass_nonneg _ _ _ hn)

lemma bound_one (T p : ℝ) : bound 1 T p = T := by
  by_cases hT : T = 0 <;> simp [bound, hT]

lemma bound_zero (q : ℕ) (p : ℝ) : bound q 0 p = 0 := by simp [bound]

lemma bound_single (q : ℕ) {T : ℝ} (hT : 0 ≤ T) : bound q T T = T := by
  by_cases hz : T = 0
  · simp [bound, hz]
  · unfold bound
    simp only [hz, if_false]
    split_ifs with hq
    · rfl
    · unfold numericalBound
      split_ifs with hq2
      · norm_num [twoFormula, div_self hz]
      · simp [multiFormula, formulaIndex, envelope, max_eq_left hT]

lemma head_le_bound (c : ℕ → ℝ) (l k q : ℕ) (hq : 1 ≤ q)
    (hn : ∀ j, 0 ≤ c j) (ha : Antitone c) (hk : 0 < k) :
    c l ≤ bound q (mass c l k) (c l) := by
  have hpT := head_le_mass c l k hn hk
  have hT0 := mass_nonneg c l k hn
  by_cases hz : mass c l k = 0
  · rw [hz, bound_zero]; linarith
  by_cases hq1 : q = 1
  · subst q; simpa [bound_one] using hpT
  have hq2 : 2 ≤ q := by omega
  have hT : 0 < mass c l k := lt_of_le_of_ne hT0 (Ne.symm hz)
  have hp : 0 < c l := head_pos c l k ha hT
  rw [bound_eq hq2 hz]
  unfold numericalBound
  split_ifs with hqeq
  · have hh := mul_le_mul_of_nonneg_left
      (le_twoFormula_max (div_pos hp hT) ((div_le_one hT).mpr hpT)) hT.le
    have he : mass c l k * (c l / mass c l k) = c l := by field_simp
    rwa [he] at hh
  · exact le_multiFormula_max hp.le

lemma bound_nonneg (c : ℕ → ℝ) (l k q : ℕ) (hq : 1 ≤ q)
    (hn : ∀ j, 0 ≤ c j) (ha : Antitone c) :
    0 ≤ bound q (mass c l k) (c l) := by
  by_cases hk : k = 0
  · simp [hk, bound_zero]
  · exact (hn l).trans (head_le_bound c l k q hq hn ha (by omega))

lemma bound_lt_mass (c : ℕ → ℝ) (l k q : ℕ) (hq : 3 ≤ q)
    (hn : ∀ j, 0 ≤ c j) (ha : Antitone c)
    (hT : mass c l k ≠ 0) (hpT : c l ≠ mass c l k) :
    bound q (mass c l k) (c l) < mass c l k := by
  have hT0 := mass_nonneg c l k hn
  have hTpos : 0 < mass c l k := lt_of_le_of_ne hT0 (Ne.symm hT)
  have hk : 0 < k := by
    by_cases hk : k = 0
    · simp [hk] at hT
    · omega
  have hp := head_pos c l k ha hTpos
  have hpless : c l < mass c l k := lt_of_le_of_ne (head_le_mass c l k hn hk) hpT
  rw [bound_eq (by omega) hT]
  simp only [numericalBound, show q ≠ 2 by omega, if_false]
  exact multiFormula_lt_total (by omega) hp hpless

lemma mass_eq_prefix (c : ℕ → ℝ) (l k : ℕ) :
    mass c l k = prefixCost (fun j => c (l + j)) k := by
  simp [mass_eq_sum, prefixCost]

/-- Actual ordered-tail theorem, with zero residual handled before normalization. -/
theorem bound_tail (c : ℕ → ℝ) (l k s q : ℕ) (hq : 2 ≤ q)
    (hn : ∀ j, 0 ≤ c j) (ha : Antitone c) (hsk : s < k)
    (hcross : bound (q + 1) (mass c l k) (c l) < mass c l (s + 1)) :
    bound q (mass c (l + s) (k - s)) (c (l + s)) ≤
      bound (q + 1) (mass c l k) (c l) := by
  have hT := mass_nonneg c l k hn
  have hres := mass_nonneg c (l + s) (k - s) hn
  have hd := bound_nonneg c l k (q + 1) (by omega) hn ha
  by_cases hz : mass c (l + s) (k - s) = 0
  · simpa [hz, bound_zero] using hd
  have hrespos : 0 < mass c (l + s) (k - s) := lt_of_le_of_ne hres (Ne.symm hz)
  have heq : mass c l k = mass c l s + mass c (l + s) (k - s) := by
    conv_lhs => rw [← Nat.add_sub_of_le (Nat.le_of_lt hsk), mass_append]
  have hTpos : 0 < mass c l k := by linarith [mass_nonneg c l s hn]
  have hTne : mass c l k ≠ 0 := ne_of_gt hTpos
  let a : ℕ → ℝ := fun j => c (l + j)
  have ha' : Antitone a := fun _ _ hij => ha (by omega)
  have hn' : ∀ j, 0 ≤ a j := fun j => hn _
  have heqR : prefixCost a k - prefixCost a s = mass c (l + s) (k - s) := by
    change prefixCost (fun j => c (l + j)) k - prefixCost (fun j => c (l + j)) s = _
    rw [← mass_eq_prefix, ← mass_eq_prefix]
    linarith
  have hcrossR : numericalBound (q + 1) (prefixCost a k) (a 0) < prefixCost a (s + 1) := by
    simpa [a, ← mass_eq_prefix, bound_eq (by omega : 2 ≤ q + 1) hTne] using hcross
  have ht := ordered_numerical_tail a k s q hq ha' hn' hsk (by rwa [heqR]) hcrossR
  rw [heqR] at ht
  rw [bound_eq hq hz, bound_eq (by omega) hTne]
  simpa [a, mass_eq_prefix] using ht

/-- Find the agent with the last first-crossing position. -/
def knife {n : ℕ} (c : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (l k : ℕ) :
    Option (Fin n × ℕ) :=
  let f := fun i => safePrefix (c i) l k (bound A.card (mass (c i) l k) (c i l))
  (pickMax A f).map (fun a => (a, f a))

/-- The selected prefix is safe for its recipient and preserves every
survivor's numerical bound. No abstract tail or mass-cap premise is assumed. -/
theorem knife_spec {n : ℕ} (c : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (l k : ℕ)
    (hA : 3 ≤ A.card) (hn : ∀ i ∈ A, ∀ j, 0 ≤ c i j)
    (ha : ∀ i ∈ A, Antitone (c i))
    (hT : ∀ i ∈ A, mass (c i) l k ≠ 0)
    (hpT : ∀ i ∈ A, c i l ≠ mass (c i) l k) :
    ∃ a s, knife c A l k = some (a, s) ∧ a ∈ A ∧ s < k ∧
      mass (c a) l s ≤ bound A.card (mass (c a) l k) (c a l) ∧
      ∀ i ∈ A.erase a,
        bound (A.erase a).card (mass (c i) (l + s) (k - s)) (c i (l + s)) ≤
        bound A.card (mass (c i) l k) (c i l) := by
  let f := fun i => safePrefix (c i) l k (bound A.card (mass (c i) l k) (c i l))
  obtain ⟨a, hchoose, hamem, hmax⟩ := pickMax_spec A f (Finset.card_pos.mp (by omega))
  have hnon (i) (hi : i ∈ A) := bound_nonneg (c i) l k A.card (by omega) (hn i hi) (ha i hi)
  have hlt (i) (hi : i ∈ A) := bound_lt_mass (c i) l k A.card hA (hn i hi) (ha i hi)
    (hT i hi) (hpT i hi)
  have hs : f a < k := safePrefix_lt (c a) l k _ (hnon a hamem) (hlt a hamem)
  refine ⟨a, f a, ?_, hamem, hs, (safePrefix_spec (c a) l k _ (hnon a hamem)).1, ?_⟩
  · simp [knife, f, hchoose]
  · intro i hi
    have hiA := Finset.mem_of_mem_erase hi
    have hfi : f i < k := safePrefix_lt (c i) l k _ (hnon i hiA) (hlt i hiA)
    have hc := (safePrefix_spec (c i) l k _ (hnon i hiA)).2 hfi
    change bound A.card (mass (c i) l k) (c i l) < mass (c i) l (f i + 1) at hc
    have hcross : bound A.card (mass (c i) l k) (c i l) < mass (c i) l (f a + 1) :=
      hc.trans_le (mass_mono (c i) l (hn i hiA) (by have := hmax i hiA; omega))
    have hcard := Finset.card_erase_add_one hamem
    have hh := bound_tail (c i) l k (f a) (A.erase a).card (by omega)
      (hn i hiA) (ha i hiA) hs (by simpa [hcard] using hcross)
    simpa [hcard] using hh

/-- Complete local invariant: exactly the remaining ranks are assigned, every
owner is active, and every active agent respects her current numerical share. -/
def Safe {n : ℕ} (c : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (l k : ℕ)
    (out : Allocation n) : Prop :=
  Valid A l k out ∧ ∀ i ∈ A,
    charge c l k out i ≤ bound A.card (mass (c i) l k) (c i l)

def earlyCandidates {n : ℕ} (c : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (l k : ℕ) :=
  A.filter (fun i => mass (c i) l k = 0 ∨ c i l = mass (c i) l k)

def early {n : ℕ} (c : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (l k : ℕ) :
    Option (Fin n) :=
  let candidates := earlyCandidates c A l k
  if h : candidates.Nonempty then some (candidates.min' h) else none

lemma early_some {n : ℕ} {c : Fin n → ℕ → ℝ} {A : Finset (Fin n)} {l k : ℕ}
    {a : Fin n} (h : early c A l k = some a) :
    a ∈ A ∧ (mass (c a) l k = 0 ∨ c a l = mass (c a) l k) := by
  unfold early at h
  dsimp only at h
  split at h
  · rename_i hnon
    have he : (earlyCandidates c A l k).min' hnon = a := Option.some.inj h
    have hm := Finset.min'_mem (earlyCandidates c A l k) hnon
    rw [he] at hm
    exact Finset.mem_filter.mp hm
  · simp at h

lemma early_none {n : ℕ} {c : Fin n → ℕ → ℝ} {A : Finset (Fin n)} {l k : ℕ}
    (h : early c A l k = none) :
    (∀ i ∈ A, mass (c i) l k ≠ 0) ∧ (∀ i ∈ A, c i l ≠ mass (c i) l k) := by
  have hn : ¬ (earlyCandidates c A l k).Nonempty := by
    unfold early at h
    dsimp only at h
    split at h
    · simp at h
    · assumption
  constructor
  · intro i hi he
    exact hn ⟨i, Finset.mem_filter.mpr ⟨hi, Or.inl he⟩⟩
  · intro i hi he
    exact hn ⟨i, Finset.mem_filter.mpr ⟨hi, Or.inr he⟩⟩

lemma empty_safe {n : ℕ} (c : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (l : ℕ) :
    Safe c A l 0 (fun _ => none) := by
  constructor
  · constructor
    · intro r hl hr; omega
    · intro r hr; rfl
  · intro i hi
    simp [charge, bound_zero]

lemma early_safe {n : ℕ} (c : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (l k : ℕ)
    (hn : ∀ i ∈ A, ∀ j, 0 ≤ c i j) (ha : ∀ i ∈ A, Antitone (c i))
    {a : Fin n} (he : early c A l k = some a) : Safe c A l k (whole a l k) := by
  obtain ⟨haA, hdeg⟩ := early_some he
  have hq : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, haA⟩
  refine ⟨whole_valid haA l k, ?_⟩
  intro i hi
  rw [charge_whole]
  split_ifs with hai
  · subst i
    rcases hdeg with hz | hs
    · simp [hz, bound_zero]
    · rw [hs, bound_single _ (mass_nonneg _ _ _ (hn a haA))]
  · exact bound_nonneg _ _ _ _ hq (hn i hi) (ha i hi)

lemma one_safe {n : ℕ} (c : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (l k : ℕ)
    (hA : A.Nonempty) (hq : A.card = 1) : Safe c A l k (whole (A.min' hA) l k) := by
  refine ⟨whole_valid (Finset.min'_mem A hA) l k, ?_⟩
  intro i hi
  have he : A.min' hA = i := (Finset.card_le_one.mp (by omega)) _
    (Finset.min'_mem A hA) i hi
  rw [charge_whole, if_pos he, hq, bound_one]

lemma mass_eq_sum_fin (c : ℕ → ℝ) (l k : ℕ) :
    mass c l k = ∑ j : Fin k, c (l + j) := by
  rw [mass_eq_sum, ← Fin.sum_univ_eq_sum_range]

/-- Convert a finite suffix allocation into the interval representation. -/
def ofFinite {n k : ℕ} (l : ℕ) (owner : Fin k → Fin n) : Allocation n :=
  fun r => if h : l ≤ r ∧ r < l + k then some (owner ⟨r - l, by omega⟩) else none

lemma ofFinite_at {n k : ℕ} (l : ℕ) (owner : Fin k → Fin n) (j : Fin k) :
    ofFinite l owner (l + j) = some (owner j) := by
  simp [ofFinite, j.isLt]

lemma ofFinite_valid {n k : ℕ} (l : ℕ) {A : Finset (Fin n)}
    (owner : Fin k → Fin n) (howner : ∀ j, owner j ∈ A) : Valid A l k (ofFinite l owner) := by
  constructor
  · intro r hl hr
    exact ⟨owner ⟨r-l, by omega⟩, howner _, by simp [ofFinite, hl, hr]⟩
  · intro r hr
    simp [ofFinite, show ¬ (l ≤ r ∧ r < l + k) by omega]

lemma charge_ofFinite {n k : ℕ} (c : Fin n → ℕ → ℝ) (l : ℕ)
    (owner : Fin k → Fin n) (i : Fin n) :
    charge c l k (ofFinite l owner) i = load (fun j : Fin k => c i (l + j)) owner i := by
  rw [charge, mass_eq_sum_fin]
  simp [load, ofFinite_at]

/-- Exact cut-and-choose terminal; unlike the rational running-time routine,
this existence argument may select an attained exact minimax partition. -/
theorem two_safe {n : ℕ} (c : Fin n → ℕ → ℝ) (A : Finset (Fin n)) (l k : ℕ)
    (hA : A.card = 2) (hk : 0 < k)
    (hn : ∀ i ∈ A, ∀ j, 0 ≤ c i j) (ha : ∀ i ∈ A, Antitone (c i))
    (hT : ∀ i ∈ A, mass (c i) l k ≠ 0) :
    ∃ out, Safe c A l k out := by
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hA
  have ham : a ∈ A := by simp [hset]
  have hbm : b ∈ A := by simp [hset]
  let v : Fin k → ℝ := fun j => c a (l + j)
  let w : Fin k → ℝ := fun j => c b (l + j)
  have pos (i) (hi : i ∈ A) : 0 < mass (c i) l k :=
    lt_of_le_of_ne (mass_nonneg _ _ _ (hn i hi)) (Ne.symm (hT i hi))
  have headpos (i) (hi : i ∈ A) : 0 < c i l := head_pos _ _ _ (ha i hi) (pos i hi)
  have headle (i) (hi : i ∈ A) : c i l ≤ mass (c i) l k := head_le_mass _ _ _ (hn i hi) hk
  have hav : mms 2 v ≤ bound A.card (mass (c a) l k) (c a l) := by
    rw [hA, bound_eq (by norm_num) (hT a ham)]
    apply mms_le_numericalBound (by norm_num) (pos a ham) (headpos a ham) (headle a ham)
    · intro j
      exact ⟨hn a ham _, ha a ham (by omega)⟩
    · exact (mass_eq_sum_fin _ _ _).symm
    · exact ⟨⟨0, hk⟩, by simp [v]⟩
  have hbw : (∑ j, w j) / 2 ≤ bound A.card (mass (c b) l k) (c b l) := by
    rw [hA, bound_eq (by norm_num) (hT b hbm)]
    have hh := mul_le_mul_of_nonneg_left
      (half_le_twoFormula (div_pos (headpos b hbm) (pos b hbm))
        ((div_le_one (pos b hbm)).mpr (headle b hbm))) (pos b hbm).le
    change (∑ j, w j) / 2 ≤ mass (c b) l k * twoFormula _
    rw [show (∑ j, w j) = mass (c b) l k from (mass_eq_sum_fin _ _ _).symm]
    linarith
  obtain ⟨t, hta, htb⟩ := real_cut_choose v w _ _ hav hbw
  let owner : Fin k → Fin n := fun j => if t j = 0 then a else b
  refine ⟨ofFinite l owner, ofFinite_valid l owner ?_, ?_⟩
  · intro j
    simp only [owner]
    split <;> assumption
  · intro i hi
    rw [charge_ofFinite]
    have hi' : i = a ∨ i = b := by simpa [hset] using hi
    rcases hi' with rfl | rfl
    · convert hta using 1
      unfold load
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hj0 : t j = 0 <;> simp [owner, hj0, hab, Ne.symm hab, v]
    · convert htb using 1
      unfold load
      apply Finset.sum_congr rfl
      intro j hj
      have hcases : t j = 0 ∨ t j = 1 := by omega
      rcases hcases with ht0 | ht1
      · simp [owner, ht0, hab, w]
      · simp [owner, ht1, hab, w]

/-- Finite induction proves simultaneous feasibility for every ordered real row. -/
theorem exists_safe {n : ℕ} (c : Fin n → ℕ → ℝ) (fuel : ℕ)
    (A : Finset (Fin n)) (l k : ℕ) (hfuel : A.card ≤ fuel) (hA : A.Nonempty)
    (hn : ∀ i ∈ A, ∀ j, 0 ≤ c i j) (ha : ∀ i ∈ A, Antitone (c i)) :
    ∃ out, Safe c A l k out := by
  induction fuel generalizing A l k with
  | zero => have := Finset.card_pos.mpr hA; omega
  | succ fuel ih =>
    by_cases hk : k = 0
    · subst k
      exact ⟨_, empty_safe c A l⟩
    by_cases hq1 : A.card = 1
    · exact ⟨_, one_safe c A l k hA hq1⟩
    cases he : early c A l k with
    | some a => exact ⟨_, early_safe c A l k hn ha he⟩
    | none =>
      obtain ⟨hT, hpT⟩ := early_none he
      by_cases hq2 : A.card = 2
      · exact two_safe c A l k hq2 (by omega) hn ha hT
      have hq3 : 3 ≤ A.card := by have := Finset.card_pos.mpr hA; omega
      obtain ⟨a, s, hknife, hamem, hsk, hpref, htail⟩ := knife_spec c A l k hq3 hn ha hT hpT
      have hcard := Finset.card_erase_add_one hamem
      have hA' : (A.erase a).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨tail, hvalid, hsafe⟩ := ih (A.erase a) (l + s) (k - s)
        (by omega) hA' (fun i hi => hn i (Finset.mem_of_mem_erase hi))
        (fun i hi => ha i (Finset.mem_of_mem_erase hi))
      refine ⟨splice a l s tail, splice_valid hamem (Nat.le_of_lt hsk) hvalid, ?_⟩
      intro i hi
      rw [charge_splice c a i l s k (Nat.le_of_lt hsk) tail]
      by_cases hai : a = i
      · subst i
        rw [if_pos rfl, charge_erased c hvalid, add_zero]
        exact hpref
      · have hi' : i ∈ A.erase a := Finset.mem_erase.mpr ⟨Ne.symm hai, hi⟩
        rw [if_neg hai, zero_add]
        exact (hsafe i hi').trans (htail i hi')

/-- Extend finite descending rows by zeros so every recursive suffix is legal. -/
def zeroExtend {m : ℕ} (v : Fin m → ℝ) : ℕ → ℝ :=
  fun j => if h : j < m then v ⟨j, h⟩ else 0

lemma zeroExtend_at {m : ℕ} (v : Fin m → ℝ) (j : Fin m) : zeroExtend v j = v j := by
  simp [zeroExtend, j.isLt]

lemma zeroExtend_nonneg {m : ℕ} (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) :
    ∀ j, 0 ≤ zeroExtend v j := by
  intro j
  unfold zeroExtend
  split_ifs <;> simp_all

lemma zeroExtend_antitone {m : ℕ} (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j)
    (ha : Antitone v) : Antitone (zeroExtend v) := by
  intro j k hjk
  unfold zeroExtend
  split_ifs with hk hj
  · exact ha hjk
  · omega
  · exact hv _
  · exact le_rfl

lemma mass_zeroExtend {m : ℕ} (v : Fin m → ℝ) : mass (zeroExtend v) 0 m = ∑ j, v j := by
  rw [mass_eq_sum_fin]
  simp [zeroExtend_at]

/-- The ordered finite-row conclusion, before the itemwise matching lift. -/
theorem ordered_exists {n m : ℕ} (hn : 2 ≤ n) (v : Fin n → Fin m → ℝ)
    (α : Fin n → ℝ) (hv : ∀ i, IsNormalizedExact (v i) (α i))
    (ha : ∀ i, Antitone (v i)) :
    ∃ owner : Fin m → Fin n, ∀ i, load (v i) owner i ≤ hill n (α i) := by
  have hm : 0 < m := by
    obtain ⟨j, hj⟩ := (hv ⟨0, by omega⟩).2.2
    exact lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  let c : Fin n → ℕ → ℝ := fun i => zeroExtend (v i)
  have hcn : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j, 0 ≤ c i j :=
    fun i _ => zeroExtend_nonneg _ (fun j => (hv i).1 j |>.1)
  have hca : ∀ i ∈ (Finset.univ : Finset (Fin n)), Antitone (c i) :=
    fun i _ => zeroExtend_antitone _ (fun j => (hv i).1 j |>.1) (ha i)
  obtain ⟨out, hvalid, hsafe⟩ := exists_safe c n Finset.univ 0 m (by simp)
    (by exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩) hcn hca
  have hown : ∀ j : Fin m, ∃ i, out j = some i := by
    intro j
    obtain ⟨i, hi, hout⟩ := hvalid.1 j (by omega) (by simpa using j.isLt)
    exact ⟨i, hout⟩
  let owner : Fin m → Fin n := fun j => Classical.choose (hown j)
  have howner (j : Fin m) : out j = some (owner j) := Classical.choose_spec (hown j)
  refine ⟨owner, fun i => ?_⟩
  have hcharge : load (v i) owner i = charge c 0 m out i := by
    rw [charge, mass_eq_sum_fin]
    simp only [load, Nat.zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    simp [howner, c, zeroExtend_at]
  rw [hcharge]
  have hs := hsafe i (Finset.mem_univ _)
  have hmass : mass (c i) 0 m = 1 := by simpa [c, mass_zeroExtend] using (hv i).2.1
  have hhead : c i 0 = α i := by
    obtain ⟨j, hj⟩ := (hv i).2.2
    have he : zeroExtend (v i) 0 = v i ⟨0, hm⟩ := by simp [zeroExtend, hm]
    change zeroExtend (v i) 0 = α i
    rw [he]
    exact le_antisymm ((hv i).1 _).2 (hj ▸ ha i (show (⟨0, hm⟩ : Fin m) ≤ j by change 0 ≤ j.val; omega))
  have hαpos : 0 < α i := by
    have hh := head_pos (c i) 0 m (hca i (Finset.mem_univ _)) (by rw [hmass]; norm_num)
    simpa [hhead] using hh
  have hαle : α i ≤ 1 := by
    have hh := head_le_mass (c i) 0 m (hcn i (Finset.mem_univ _)) hm
    simpa [hhead, hmass] using hh
  simpa [Finset.card_univ, hmass, hhead, bound_eq hn (by norm_num : (1 : ℝ) ≠ 0),
    ← hill_eq_numericalBound hn hαpos hαle] using hs

end
end ExactHillShares.RealAllocation

namespace ExactHillShares
open scoped BigOperators

/-- Main simultaneous exact-maximum Hill-share existence theorem.
Every row is an arbitrary real-valued finite normalized nonnegative valuation. -/
theorem simultaneous_hill_allocation {n m : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ)
    (hv : ∀ i, IsNormalizedExact (v i) (α i)) :
    ∃ a : Fin m → Fin n, ∀ i, load (v i) a i ≤ hill n (α i) := by
  classical
  let ranked := descendingRankCost v
  let hequiv (i : Fin n) : Equiv.Perm (Fin m) := Fin.revPerm.trans (Tuple.sort (v i))
  have heq (i : Fin n) (j : Fin m) : ranked i j = v i (hequiv i j) := by
    simp [ranked, descendingRankCost, sortedRankCost, hequiv, Fin.revPerm]
  have hnorm : ∀ i, IsNormalizedExact (ranked i) (α i) := by
    intro i
    refine ⟨fun j => by rw [heq]; exact (hv i).1 _, ?_, ?_⟩
    · simpa only [heq, Equiv.sum_comp] using (hv i).2.1
    · obtain ⟨j, hj⟩ := (hv i).2.2
      exact ⟨(hequiv i).symm j, by rw [heq]; simpa using hj⟩
  obtain ⟨owner, howner⟩ := RealAllocation.ordered_exists hn ranked α hnorm
    (descendingRankCost_antitone v)
  obtain ⟨original, horiginal⟩ := descending_allocation_lift v owner
  exact ⟨original, fun i => (horiginal i).trans (howner i)⟩

/-- The exact maximum is attained automatically for a normalized finite row. -/
theorem exists_exact_maximum {m : ℕ} (v : Fin m → ℝ)
    (hv : ∀ j, 0 ≤ v j) (hs : (∑ j, v j) = 1) :
    ∃ α, IsNormalizedExact v α := by
  classical
  have hm : 0 < m := by
    by_contra hh
    have he : m = 0 := by omega
    subst m
    simp at hs
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨j, hj⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  exact ⟨v j, (fun k => ⟨hv k, hj.2 k (Finset.mem_univ _)⟩), hs, ⟨j, rfl⟩⟩

/-- Equivalent public API needing only nonnegativity and unit total mass. -/
theorem simultaneous_hill_allocation_of_normalized {n m : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Fin m → ℝ) (hv : ∀ i j, 0 ≤ v i j) (hs : ∀ i, (∑ j, v i j) = 1) :
    ∃ (α : Fin n → ℝ) (a : Fin m → Fin n),
      (∀ i, IsNormalizedExact (v i) (α i)) ∧ ∀ i, load (v i) a i ≤ hill n (α i) := by
  classical
  choose α hα using fun i => exists_exact_maximum (v i) (hv i) (hs i)
  obtain ⟨a, ha⟩ := simultaneous_hill_allocation hn v α hα
  exact ⟨α, a, hα, ha⟩

end ExactHillShares
