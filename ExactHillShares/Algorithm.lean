import ExactHillShares.TrimmedSubsetSum
import ExactHillShares.NumericalBounds
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Executable rational ordered allocation primitives

All thresholds, strict crossings, and subset sums use exact rational arithmetic.
The moving knife uses a linear scan, rather than binary search. This still gives
an item-count cubic arithmetic bound after the singleton preprocessing.
-/
namespace ExactHillShares.Algorithm
open scoped BigOperators

def envelope (q h : ℕ) (T p : ℚ) : ℚ :=
  max (((h : ℚ) + 1) * p)
    ((((h : ℚ) + 2) / ((q : ℚ) * ((h : ℚ) + 1))) * (T - p))

def index (q : ℕ) (T p : ℚ) : ℕ := ⌊(T - p) / ((q : ℚ) * p)⌋₊

def multi (q : ℕ) (T p : ℚ) : ℚ := envelope q (index q T p) T p

def two (x : ℚ) : ℚ :=
  if 1 / 3 ≤ x then max x (1 - x)
  else if 2 / 7 ≤ x then 2 * x
  else if 7 / 27 ≤ x then (2 + 3 * x) / 5
  else if 1 / 5 ≤ x then 3 * (1 - x) / 4
  else multi 2 1 x

/-- The zero case is defined separately: normalization is never used there. -/
def bound (q : ℕ) (T p : ℚ) : ℚ :=
  if T = 0 then 0 else if q ≤ 1 then T else if q = 2 then T * two (p / T)
  else multi q T p

@[simp] theorem cast_envelope (q h : ℕ) (T p : ℚ) :
    ((envelope q h T p : ℚ) : ℝ) = ExactHillShares.envelope q h T p := by
  simp [envelope, ExactHillShares.envelope]

@[simp] theorem cast_index (q : ℕ) (T p : ℚ) :
    index q T p = formulaIndex q T p := by
  have hc : (((T - p) / ((q : ℚ) * p) : ℚ) : ℝ) =
      ((T : ℝ) - p) / ((q : ℝ) * p) := by push_cast; rfl
  unfold index formulaIndex
  rw [← hc, ← Int.floor_toNat, ← Int.floor_toNat, Rat.floor_cast]

@[simp] theorem cast_multi (q : ℕ) (T p : ℚ) :
    ((multi q T p : ℚ) : ℝ) = multiFormula q T p := by
  simp [multi, multiFormula]

@[simp] theorem cast_two (x : ℚ) : ((two x : ℚ) : ℝ) = twoFormula x := by
  have h1 : (1 / 3 : ℝ) ≤ (x : ℝ) ↔ (1 / 3 : ℚ) ≤ x := by
    simpa using (Rat.cast_le (K := ℝ) (p := (1/3 : ℚ)) (q := x))
  have h2 : (2 / 7 : ℝ) ≤ (x : ℝ) ↔ (2 / 7 : ℚ) ≤ x := by
    simpa using (Rat.cast_le (K := ℝ) (p := (2/7 : ℚ)) (q := x))
  have h3 : (7 / 27 : ℝ) ≤ (x : ℝ) ↔ (7 / 27 : ℚ) ≤ x := by
    simpa using (Rat.cast_le (K := ℝ) (p := (7/27 : ℚ)) (q := x))
  have h4 : (1 / 5 : ℝ) ≤ (x : ℝ) ↔ (1 / 5 : ℚ) ≤ x := by
    simpa using (Rat.cast_le (K := ℝ) (p := (1/5 : ℚ)) (q := x))
  unfold two twoFormula
  simp only [h1, h2, h3, h4]
  split_ifs <;> push_cast <;> simp

@[simp] theorem cast_bound {q : ℕ} (hq : 2 ≤ q) {T p : ℚ} (hT : T ≠ 0) :
    ((bound q T p : ℚ) : ℝ) = numericalBound q T p := by
  simp [bound, hT, show ¬ q ≤ 1 by omega, numericalBound]
  split_ifs <;> simp

/-- Sum of exactly `k` successive entries beginning at `l`. -/
def mass (c : ℕ → ℚ) (l : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => c l + mass c (l + 1) k

@[simp] theorem mass_zero (c l) : mass c l 0 = 0 := rfl
@[simp] theorem mass_succ (c l k) : mass c l (k + 1) = c l + mass c (l + 1) k := rfl

lemma mass_eq_sum (c : ℕ → ℚ) (l k : ℕ) :
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

lemma mass_append (c : ℕ → ℚ) (l s k : ℕ) :
    mass c l (s + k) = mass c l s + mass c (l + s) k := by
  induction s generalizing l with
  | zero => simp
  | succ s ih =>
    rw [show s + 1 + k = (s + k) + 1 by omega, mass_succ, ih, mass_succ]
    simp only [show l + 1 + s = l + (s + 1) by omega]
    ring

lemma mass_nonneg (c : ℕ → ℚ) (l k : ℕ) (hn : ∀ j, 0 ≤ c j) :
    0 ≤ mass c l k := by
  rw [mass_eq_sum]
  exact Finset.sum_nonneg fun j hj => hn _

lemma mass_mono (c : ℕ → ℚ) (l : ℕ) (hn : ∀ j, 0 ≤ c j) :
    Monotone (mass c l) := by
  intro s k hsk
  rw [← Nat.add_sub_of_le hsk, mass_append]
  exact le_add_of_nonneg_right (mass_nonneg _ _ _ hn)

/-- First strict crossing, represented by the number of safe preceding items.
The implementation visits each item at most once, subtracting its cost from the
remaining threshold. Equality is safe, so the stopping comparison is strict. -/
def safePrefix (c : ℕ → ℚ) (l : ℕ) : ℕ → ℚ → ℕ
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
theorem safePrefix_spec (c : ℕ → ℚ) (l k : ℕ) (d : ℚ) (hd : 0 ≤ d) :
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

theorem safePrefix_lt (c : ℕ → ℚ) (l k : ℕ) (d : ℚ)
    (hd : 0 ≤ d) (hcross : d < mass c l k) : safePrefix c l k d < k := by
  have hs := safePrefix_le c l k d
  have hb := (safePrefix_spec c l k d hd).1
  by_contra h
  have he : safePrefix c l k d = k := by omega
  rw [he] at hb
  linarith

/-- Exact count of visited comparison/subtraction positions. -/
def scanVisits (c : ℕ → ℚ) (l : ℕ) : ℕ → ℚ → ℕ
  | 0, _ => 0
  | k + 1, d => if c l ≤ d then 1 + scanVisits c (l + 1) k (d - c l) else 1

theorem scanVisits_le (c l k d) : scanVisits c l k d ≤ k := by
  induction k generalizing l d with
  | zero => simp [scanVisits]
  | succ k ih =>
    simp only [scanVisits]
    split
    · have := ih (l + 1) (d - c l); omega
    · omega

end ExactHillShares.Algorithm

namespace ExactHillShares.Algorithm

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

def charge {n : ℕ} (c : Fin n → ℕ → ℚ) (l k : ℕ)
    (a : Allocation n) (i : Fin n) : ℚ :=
  mass (fun r => if a r = some i then c i r else 0) l k

def whole {n : ℕ} (a : Fin n) (l k : ℕ) : Allocation n :=
  fun r => if l ≤ r ∧ r < l + k then some a else none

def splice {n : ℕ} (a : Fin n) (l s : ℕ) (tail : Allocation n) : Allocation n :=
  fun r => if l ≤ r ∧ r < l + s then some a else tail r

lemma mass_congr {c d : ℕ → ℚ} {l k : ℕ}
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

lemma charge_whole {n : ℕ} (c : Fin n → ℕ → ℚ) (a i : Fin n) (l k : ℕ) :
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
lemma charge_splice {n : ℕ} (c : Fin n → ℕ → ℚ) (a i : Fin n)
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

lemma charge_erased {n : ℕ} (c : Fin n → ℕ → ℚ)
    {A : Finset (Fin n)} {a : Fin n} {l k : ℕ} {tail : Allocation n}
    (ht : Valid (A.erase a) l k tail) : charge c l k tail a = 0 := by
  unfold charge
  rw [← mass_const_zero l k]
  apply mass_congr
  intro r hl hr
  obtain ⟨i, hi, he⟩ := ht.1 r hl hr
  have hne := (Finset.mem_erase.mp hi).1
  simp [he, hne]

end ExactHillShares.Algorithm

namespace ExactHillShares.Algorithm

lemma pickMax_some {n : ℕ} {A : Finset (Fin n)} {f : Fin n → ℕ} {a : Fin n}
    (h : pickMax A f = some a) : a ∈ A := by
  unfold pickMax at h
  dsimp only at h
  split at h
  · rename_i hh
    have he := Option.some.inj h
    have hm := Finset.min'_mem (maxCandidates A f) hh
    rw [he] at hm
    exact (Finset.mem_filter.mp hm).1
  · simp at h

end ExactHillShares.Algorithm
