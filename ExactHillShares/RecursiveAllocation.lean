import Mathlib.Data.Rat.BigOperators
import ExactHillShares.Algorithm
import ExactHillShares.OrderedTail

namespace ExactHillShares.Algorithm
open scoped BigOperators

lemma mass_le_head (c : ℕ → ℚ) (l k : ℕ) (ha : Antitone c) :
    mass c l k ≤ (k : ℚ) * c l := by
  rw [mass_eq_sum]
  calc
    (∑ j ∈ Finset.range k, c (l + j)) ≤ ∑ _j ∈ Finset.range k, c l :=
      Finset.sum_le_sum fun j hj => ha (by omega)
    _ = _ := by simp

lemma head_pos (c : ℕ → ℚ) (l k : ℕ) (ha : Antitone c)
    (hT : 0 < mass c l k) : 0 < c l := by
  have h := mass_le_head c l k ha
  by_contra hp
  have hh : (k : ℚ) * c l ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_gt hp)
  linarith

lemma head_le_mass (c : ℕ → ℚ) (l k : ℕ) (hn : ∀ j, 0 ≤ c j) (hk : 0 < k) :
    c l ≤ mass c l k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [mass_succ]
  exact le_add_of_nonneg_right (mass_nonneg _ _ _ hn)

lemma bound_one (T p : ℚ) : bound 1 T p = T := by
  by_cases hT : T = 0 <;> simp [bound, hT]

lemma bound_zero (q : ℕ) (p : ℚ) : bound q 0 p = 0 := by simp [bound]

lemma bound_single (q : ℕ) {T : ℚ} (hT : 0 ≤ T) : bound q T T = T := by
  by_cases hz : T = 0
  · simp [bound, hz]
  · unfold bound
    simp only [hz, if_false]
    split_ifs with hq hq2
    · rfl
    · norm_num [two, div_self hz]
    · simp [multi, index, envelope, max_eq_left hT]

lemma head_le_bound (c : ℕ → ℚ) (l k q : ℕ) (hq : 1 ≤ q)
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
  have hpR : (0 : ℝ) < (c l : ℚ) := by exact_mod_cast hp
  have hTR : (0 : ℝ) < (mass c l k : ℚ) := by exact_mod_cast hT
  have hpTR : ((c l : ℚ) : ℝ) ≤ (mass c l k : ℚ) := by exact_mod_cast hpT
  apply (Rat.cast_le (K := ℝ)).mp
  rw [cast_bound hq2 hz]
  unfold numericalBound
  split_ifs with hqeq
  · have hh := mul_le_mul_of_nonneg_left
      (le_twoFormula_max (div_pos hpR hTR) ((div_le_one hTR).mpr hpTR)) hTR.le
    have he : (mass c l k : ℝ) * ((c l : ℝ) / (mass c l k : ℝ)) = c l := by
      field_simp
    rwa [he] at hh
  · exact le_multiFormula_max hpR.le

lemma bound_nonneg (c : ℕ → ℚ) (l k q : ℕ) (hq : 1 ≤ q)
    (hn : ∀ j, 0 ≤ c j) (ha : Antitone c) :
    0 ≤ bound q (mass c l k) (c l) := by
  by_cases hk : k = 0
  · simp [hk, bound_zero]
  · exact (hn l).trans (head_le_bound c l k q hq hn ha (by omega))

lemma bound_lt_mass (c : ℕ → ℚ) (l k q : ℕ) (hq : 3 ≤ q)
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
  apply (Rat.cast_lt (K := ℝ)).mp
  rw [cast_bound (by omega) hT]
  simp only [numericalBound, show q ≠ 2 by omega, if_false]
  exact multiFormula_lt_total (by omega) (by exact_mod_cast hp) (by exact_mod_cast hpless)

lemma cast_mass (c : ℕ → ℚ) (l k : ℕ) :
    ((mass c l k : ℚ) : ℝ) = prefixCost (fun j => (c (l + j) : ℝ)) k := by
  simp [mass_eq_sum, prefixCost, Rat.cast_sum]

/-- Ordered tail domination transported to the executable rational inputs. -/
theorem bound_tail (c : ℕ → ℚ) (l k s q : ℕ) (hq : 2 ≤ q)
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
  have ha' : Antitone a := by
    intro i j hij
    change (c (l + j) : ℝ) ≤ (c (l + i) : ℝ)
    exact_mod_cast ha (show l + i ≤ l + j by omega)
  have hn' : ∀ j, 0 ≤ a j := by
    intro j
    change (0 : ℝ) ≤ (c (l + j) : ℝ)
    exact_mod_cast hn (l + j)
  have heqR : prefixCost a k - prefixCost a s = (mass c (l + s) (k - s) : ℚ) := by
    change prefixCost (fun j => (c (l + j) : ℝ)) k -
      prefixCost (fun j => (c (l + j) : ℝ)) s = _
    rw [← cast_mass, ← cast_mass]
    exact_mod_cast (show mass c l k - mass c l s = mass c (l + s) (k - s) by linarith)
  have hcrossR : numericalBound (q + 1) (prefixCost a k) (a 0) < prefixCost a (s + 1) := by
    change numericalBound (q + 1) (prefixCost (fun j => (c (l + j) : ℝ)) k)
      (c (l + 0) : ℚ) < prefixCost (fun j => (c (l + j) : ℝ)) (s + 1)
    rw [← cast_mass, ← cast_mass, Nat.add_zero, ← cast_bound (by omega) hTne]
    exact_mod_cast hcross
  have ht := ordered_numerical_tail a k s q hq ha' hn' hsk
    (by rw [heqR]; exact_mod_cast hrespos) hcrossR
  rw [heqR] at ht
  apply (Rat.cast_le (K := ℝ)).mp
  rw [cast_bound hq hz, cast_bound (by omega) hTne]
  simpa [a, cast_mass] using ht

/-- Find the agent with the last first-crossing position. -/
def knife {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ) :
    Option (Fin n × ℕ) :=
  let q := A.card
  let f := fun i => safePrefix (c i) l k (bound q (mass (c i) l k) (c i l))
  (pickMax A f).map (fun a => (a, f a))

/-- The selected prefix is safe for its recipient and preserves every
survivor's numerical bound. No abstract tail or mass-cap premise is assumed. -/
theorem knife_spec {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ)
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

end ExactHillShares.Algorithm

namespace ExactHillShares.Algorithm

/-- Complete local invariant: exactly the remaining ranks are assigned, every
owner is active, and every active agent respects her current numerical share. -/
def Safe {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ)
    (out : Allocation n) : Prop :=
  Valid A l k out ∧ ∀ i ∈ A,
    charge c l k out i ≤ bound A.card (mass (c i) l k) (c i l)

abbrev Terminal (n : ℕ) :=
  (Fin n → ℕ → ℚ) → Finset (Fin n) → ℕ → ℕ → Option (Allocation n)

/-- Contract used solely to compose the separately verified executable
terminal component. The concrete terminal is instantiated in the final module. -/
def TerminalCorrect {n : ℕ} (terminal : Terminal n) : Prop :=
  ∀ (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ),
    A.card = 2 → 0 < k →
    (∀ i ∈ A, ∀ j, 0 ≤ c i j) → (∀ i ∈ A, Antitone (c i)) →
    (∀ i ∈ A, mass (c i) l k ≠ 0) →
    (∀ i ∈ A, c i l ≠ mass (c i) l k) →
    ∃ out, terminal c A l k = some out ∧ Safe c A l k out

def earlyCandidates {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ) :=
  A.filter (fun i => mass (c i) l k = 0 ∨ c i l = mass (c i) l k)

def early {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ) :
    Option (Fin n) :=
  let candidates := earlyCandidates c A l k
  if h : candidates.Nonempty then some (candidates.min' h) else none

lemma early_some {n : ℕ} {c : Fin n → ℕ → ℚ} {A : Finset (Fin n)} {l k : ℕ}
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

lemma early_none {n : ℕ} {c : Fin n → ℕ → ℚ} {A : Finset (Fin n)} {l k : ℕ}
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

lemma empty_safe {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l : ℕ) :
    Safe c A l 0 (fun _ => none) := by
  constructor
  · constructor
    · intro r hl hr; omega
    · intro r hr; rfl
  · intro i hi
    simp [charge, bound_zero]

lemma early_safe {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ)
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

lemma one_safe {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ)
    (hA : A.Nonempty) (hq : A.card = 1) : Safe c A l k (whole (A.min' hA) l k) := by
  refine ⟨whole_valid (Finset.min'_mem A hA) l k, ?_⟩
  intro i hi
  have he : A.min' hA = i := (Finset.card_le_one.mp (by omega)) _
    (Finset.min'_mem A hA) i hi
  rw [charge_whole, if_pos he, hq, bound_one]

/-- Algorithm 3, with the corrected terminal component supplied explicitly.
Fuel is the initial active-agent count, not an unproved termination oracle.
The empty, zero-total, and single-positive cases are handled before division. -/
def runWith {n : ℕ} (terminal : Terminal n) (c : Fin n → ℕ → ℚ) :
    ℕ → Finset (Fin n) → ℕ → ℕ → Option (Allocation n)
  | 0, _, _, k => if k = 0 then some (fun _ => none) else none
  | fuel + 1, A, l, k =>
    if k = 0 then some (fun _ => none)
    else if hA : A.Nonempty then
      if A.card = 1 then some (whole (A.min' hA) l k)
      else match early c A l k with
        | some a => some (whole a l k)
        | none => if A.card = 2 then terminal c A l k
          else match knife c A l k with
            | none => none
            | some (a, s) =>
              (runWith terminal c fuel (A.erase a) (l + s) (k - s)).map (splice a l s)
    else none

/-- Constructive induction for the actual recursive program. Every moving
knife premise is discharged by `knife_spec`; the only component parameter is
the independently verified two-agent routine. -/
theorem runWith_correct {n : ℕ} (terminal : Terminal n) (ht : TerminalCorrect terminal)
    (c : Fin n → ℕ → ℚ) (fuel : ℕ) (A : Finset (Fin n)) (l k : ℕ)
    (hfuel : A.card ≤ fuel) (hA : A.Nonempty)
    (hn : ∀ i ∈ A, ∀ j, 0 ≤ c i j) (ha : ∀ i ∈ A, Antitone (c i)) :
    ∃ out, runWith terminal c fuel A l k = some out ∧ Safe c A l k out := by
  induction fuel generalizing A l k with
  | zero => have := Finset.card_pos.mpr hA; omega
  | succ fuel ih =>
    by_cases hk : k = 0
    · subst k
      exact ⟨_, by simp [runWith], empty_safe c A l⟩
    by_cases hq1 : A.card = 1
    · exact ⟨_, by simp [runWith, hk, hA, hq1], one_safe c A l k hA hq1⟩
    cases he : early c A l k with
    | some a =>
      exact ⟨_, by simp [runWith, hk, hA, hq1, he], early_safe c A l k hn ha he⟩
    | none =>
      obtain ⟨hT, hpT⟩ := early_none he
      by_cases hq2 : A.card = 2
      · obtain ⟨out, hout, hs⟩ := ht c A l k hq2 (by omega) hn ha hT hpT
        exact ⟨out, by simpa [runWith, hk, hA, hq1, he, hq2] using hout, hs⟩
      have hq3 : 3 ≤ A.card := by have := Finset.card_pos.mpr hA; omega
      obtain ⟨a, s, hknife, hamem, hsk, hpref, htail⟩ := knife_spec c A l k hq3 hn ha hT hpT
      have hcard := Finset.card_erase_add_one hamem
      have hA' : (A.erase a).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨tail, hrun, hvalid, hsafe⟩ := ih (A.erase a) (l + s) (k - s)
        (by omega) hA' (fun i hi => hn i (Finset.mem_of_mem_erase hi))
        (fun i hi => ha i (Finset.mem_of_mem_erase hi))
      refine ⟨splice a l s tail, ?_, splice_valid hamem (Nat.le_of_lt hsk) hvalid, ?_⟩
      · simp [runWith, hk, hA, hq1, he, hq2, hknife, hrun]
      · intro i hi
        rw [charge_splice c a i l s k (Nat.le_of_lt hsk) tail]
        by_cases hai : a = i
        · subst i
          rw [if_pos rfl, charge_erased c hvalid, add_zero]
          exact hpref
        · have hi' : i ∈ A.erase a := Finset.mem_erase.mpr ⟨Ne.symm hai, hi⟩
          rw [if_neg hai, zero_add]
          exact (hsafe i hi').trans (htail i hi')

end ExactHillShares.Algorithm
