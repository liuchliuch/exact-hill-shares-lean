import ExactHillShares.RecursiveAllocation
import ExactHillShares.RationalFeasibility
import ExactHillShares.ExactFormula

/-! Corrected two-agent terminal routine. The large-item singleton shortcut is
performed before invoking the positive-width trimmed subset-sum routine. -/
namespace ExactHillShares.Algorithm
open scoped BigOperators

/-- A finite mask's exact selected charge. -/
def maskSum {k : ℕ} (c : Fin k → ℚ) (b : Fin k → Bool) : ℚ :=
  ∑ j, if b j then c j else 0

lemma maskSum_complement {k : ℕ} (c : Fin k → ℚ) (b : Fin k → Bool) :
    maskSum c b + maskSum c (fun j => !(b j)) = ∑ j, c j := by
  rw [maskSum, maskSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  cases b j <;> simp

lemma mass_eq_fin_sum (c : ℕ → ℚ) (l k : ℕ) :
    mass c l k = ∑ j : Fin k, c (l + j) := by
  rw [mass_eq_sum]
  exact (Fin.sum_univ_eq_sum_range (fun j => c (l + j)) k).symm

/-- Missing bits are false; correctness establishes that no bit is missing. -/
def bitsMask (k : ℕ) (bs : List Bool) : Fin k → Bool := fun j => bs.getD j false

lemma ofFn_bitsMask {k : ℕ} {bs : List Bool} (h : bs.length = k) :
    List.ofFn (bitsMask k bs) = bs := by
  apply List.ext_getElem (by simpa using h.symm)
  intro i hi hib
  simp [bitsMask, List.getD, List.getElem?_eq_getElem hib]

lemma maskSum_bitsMask {k : ℕ} (c : Fin k → ℚ) {bs : List Bool}
    (h : bs.length = k) :
    maskSum c (bitsMask k bs) = Trimmed.selectedSum (List.ofFn c) bs := by
  conv_rhs => rw [← ofFn_bitsMask h, Trimmed.selectedSum_ofFn]
  rfl

lemma half_le_bound_two (c : ℕ → ℚ) (l k : ℕ)
    (hn : ∀ j, 0 ≤ c j) (ha : Antitone c) :
    mass c l k / 2 ≤ bound 2 (mass c l k) (c l) := by
  by_cases hz : mass c l k = 0
  · simp [hz, bound_zero]
  have hT := lt_of_le_of_ne (mass_nonneg c l k hn) (Ne.symm hz)
  have hp := head_pos c l k ha hT
  have hk : 0 < k := by
    by_contra h
    have he : k = 0 := by omega
    simp [he] at hz
  have hpT := head_le_mass c l k hn hk
  apply (Rat.cast_le (K := ℝ)).mp
  rw [cast_bound (by norm_num) hz]
  push_cast
  simp only [numericalBound, if_pos rfl]
  have hTR : (0 : ℝ) < (mass c l k : ℚ) := by exact_mod_cast hT
  have hx : (0 : ℝ) < (c l : ℚ) / (mass c l k : ℚ) := by exact_mod_cast div_pos hp hT
  have hx1 : (c l : ℝ) / (mass c l k : ℚ) ≤ 1 := by
    exact_mod_cast (div_le_one hT).2 hpT
  have H := mul_le_mul_of_nonneg_left (half_le_twoFormula hx hx1) hTR.le
  simpa [div_eq_mul_inv] using H

lemma bound_two_large {T p : ℚ} (hT : 0 < T) (hlarge : T ≤ 3 * p) :
    bound 2 T p = max p (T - p) := by
  have hh : (1 / 3 : ℚ) ≤ p / T := (le_div_iff₀ hT).2 (by linarith)
  simp only [bound, ne_of_gt hT, if_false, show ¬ (2 : ℕ) ≤ 1 by omega, if_pos rfl]
  rw [two, if_pos hh, mul_max_of_nonneg _ _ hT.le]
  have he : T * (p / T) = p := by field_simp
  rw [he, mul_sub, mul_one, he]
  simp

lemma bound_two_width (c : ℕ → ℚ) (l k : ℕ)
    (hn : ∀ j, 0 ≤ c j) (ha : Antitone c)
    (hT : 0 < mass c l k) (hsmall : 3 * c l < mass c l k) :
    0 < 2 * bound 2 (mass c l k) (c l) - mass c l k ∧
    3 * mass c l k ≤ 7 * (k : ℚ) *
      (2 * bound 2 (mass c l k) (c l) - mass c l k) := by
  have hp := head_pos c l k ha hT
  have hTR : (0 : ℝ) < (mass c l k : ℚ) := by exact_mod_cast hT
  have hpR : (0 : ℝ) < (c l : ℚ) := by exact_mod_cast hp
  have hx : (c l : ℝ) / (mass c l k : ℚ) ≤ 1 / 3 := by
    apply (div_le_iff₀ hTR).2
    have hs : (3 : ℝ) * (c l : ℚ) < (mass c l k : ℚ) := by exact_mod_cast hsmall
    linarith
  have hw := twoFormula_scaled_width hTR hpR hx
  have hd : ((bound 2 (mass c l k) (c l) : ℚ) : ℝ) =
      (mass c l k : ℚ) * twoFormula ((c l : ℚ) / (mass c l k : ℚ)) := by
    rw [cast_bound (by norm_num) (ne_of_gt hT)]
    simp [numericalBound]
  rw [← hd] at hw
  have hwQ : (3 / 7 : ℚ) * c l ≤ 2 * bound 2 (mass c l k) (c l) - mass c l k := by
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    norm_num at hw ⊢
    exact hw
  have hm := mass_le_head c l k ha
  have hkmul := mul_le_mul_of_nonneg_left hwQ (Nat.cast_nonneg k : (0 : ℚ) ≤ k)
  constructor <;> nlinarith

/-- The divider first uses the singleton/remainder partition when p/T≥1/3.
Only the remaining positive-width case calls the two trimmed DP directions. -/
def divide (c : ℕ → ℚ) (l k : ℕ) : Option (Fin k → Bool) :=
  let T := mass c l k
  let D := bound 2 T (c l)
  if T = 0 then some (fun _ => false)
  else if T ≤ 3 * c l then some (fun j => decide (j.val = 0))
  else (Trimmed.solve (List.ofFn fun j : Fin k => c (l + j)) (T - D) D).map
    (fun y => bitsMask k y.bits)

/-- Numerical feasibility is a proof input only, never an executable search. -/
def TwoFeasible (c : ℕ → ℚ) (l k : ℕ) : Prop :=
  ∃ b : Fin k → Bool,
    mass c l k - bound 2 (mass c l k) (c l) ≤ maskSum (fun j => c (l + j)) b ∧
    maskSum (fun j => c (l + j)) b ≤ bound 2 (mass c l k) (c l)

lemma maskSum_singleton (c : ℕ → ℚ) (l k : ℕ) (hk : 0 < k) :
    maskSum (fun j : Fin k => c (l + j)) (fun j => decide (j.val = 0)) = c l := by
  unfold maskSum
  have he : (fun j : Fin k => if decide (j.val = 0) then c (l + j) else 0) =
      (fun j : Fin k => if j = ⟨0, hk⟩ then c l else 0) := by
    funext j
    by_cases hj : j.val = 0
    · have he : j = ⟨0, hk⟩ := Fin.ext hj
      simp [he]
    · have he : j ≠ ⟨0, hk⟩ := fun he => hj (congrArg Fin.val he)
      simp [hj, he]
  rw [he]
  simp

theorem divide_spec (c : ℕ → ℚ) (l k : ℕ) (hk : 0 < k)
    (hn : ∀ j, 0 ≤ c j) (ha : Antitone c) (hf : TwoFeasible c l k) :
    ∃ b, divide c l k = some b ∧
      maskSum (fun j => c (l + j)) b ≤ bound 2 (mass c l k) (c l) ∧
      maskSum (fun j => c (l + j)) (fun j => !(b j)) ≤ bound 2 (mass c l k) (c l) := by
  have hcomp (b : Fin k → Bool) := maskSum_complement (fun j => c (l + j)) b
  rw [← mass_eq_fin_sum] at hcomp
  by_cases hz : mass c l k = 0
  · refine ⟨fun _ => false, by simp [divide, hz], ?_, ?_⟩
    · simp [maskSum, hz, bound_zero]
    · simp [maskSum, hz, bound_zero, ← mass_eq_fin_sum]
  have hT : 0 < mass c l k := lt_of_le_of_ne (mass_nonneg c l k hn) (Ne.symm hz)
  by_cases hh : mass c l k ≤ 3 * c l
  · refine ⟨fun j => decide (j.val = 0), by simp [divide, hz, hh], ?_, ?_⟩
    · rw [maskSum_singleton c l k hk, bound_two_large hT hh]
      exact le_max_left _ _
    · have hc := hcomp (fun j => decide (j.val = 0))
      rw [maskSum_singleton c l k hk] at hc
      rw [bound_two_large hT hh]
      have H := le_max_right (c l) (mass c l k - c l)
      linarith
  have hw := bound_two_width c l k hn ha hT (lt_of_not_ge hh)
  obtain ⟨y, hy, hyw, hlo, hhi⟩ := Trimmed.finite_solve_correct hk
    (by linarith : mass c l k - bound 2 (mass c l k) (c l) < bound 2 (mass c l k) (c l))
    (fun j : Fin k => hn (l + j)) hf
  obtain ⟨hlen, hval⟩ := Trimmed.witness_decodes hyw
  have hlen' : y.bits.length = k := by simpa using hlen
  refine ⟨bitsMask k y.bits, by simp [divide, hz, hh, hy], ?_, ?_⟩
  · rw [maskSum_bitsMask _ hlen']
    linarith
  · have hc := hcomp (bitsMask k y.bits)
    rw [maskSum_bitsMask _ hlen'] at hc
    linarith

end ExactHillShares.Algorithm

namespace ExactHillShares.Algorithm
open scoped BigOperators

/-- Evaluate the mask in the contiguous input suffix. -/
def maskAllocation {n k : ℕ} (a b : Fin n) (l : ℕ) (mask : Fin k → Bool) :
    Allocation n := fun r =>
  if h : l ≤ r ∧ r < l + k then
    if mask ⟨r - l, by omega⟩ then some a else some b
  else none

lemma maskAllocation_valid {n k : ℕ} {A : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ A) (hb : b ∈ A) (l : ℕ) (mask : Fin k → Bool) :
    Valid A l k (maskAllocation a b l mask) := by
  constructor
  · intro r hl hr
    have hh : l ≤ r ∧ r < l + k := ⟨hl, hr⟩
    by_cases hm : mask ⟨r - l, by omega⟩ = true
    · exact ⟨a, ha, by simp [maskAllocation, hh, hm]⟩
    · exact ⟨b, hb, by simp [maskAllocation, hh, hm]⟩
  · intro r hr
    exact dif_neg (by omega)

lemma charge_maskAllocation_left {n k : ℕ} (c : Fin n → ℕ → ℚ)
    (a b : Fin n) (hab : a ≠ b) (l : ℕ) (mask : Fin k → Bool) :
    charge c l k (maskAllocation a b l mask) a = maskSum (fun j => c a (l + j)) mask := by
  rw [charge, mass_eq_fin_sum, maskSum]
  apply Finset.sum_congr rfl
  intro j hj
  have hh : l ≤ l + j.val ∧ l + j.val < l + k := ⟨by omega, by omega⟩
  simp only [maskAllocation, dif_pos hh, Nat.add_sub_cancel_left]
  cases mask j <;> simp [hab, Ne.symm hab]

lemma charge_maskAllocation_right {n k : ℕ} (c : Fin n → ℕ → ℚ)
    (a b : Fin n) (hab : a ≠ b) (l : ℕ) (mask : Fin k → Bool) :
    charge c l k (maskAllocation a b l mask) b =
      maskSum (fun j => c b (l + j)) (fun j => !(mask j)) := by
  rw [charge, mass_eq_fin_sum, maskSum]
  apply Finset.sum_congr rfl
  intro j hj
  have hh : l ≤ l + j.val ∧ l + j.val < l + k := ⟨by omega, by omega⟩
  simp only [maskAllocation, dif_pos hh, Nat.add_sub_cancel_left]
  cases mask j <;> simp [hab, Ne.symm hab]

/-- Algorithm 2's second agent chooses the cheaper of the two bundles.
Ties favor the selected mask; the comparison uses exactly half her total. -/
def choose {n k : ℕ} (c : Fin n → ℕ → ℚ) (a b : Fin n) (l : ℕ)
    (mask : Fin k → Bool) : Allocation n :=
  if maskSum (fun j => c b (l + j)) mask ≤ mass (c b) l k / 2
  then maskAllocation b a l mask else maskAllocation a b l mask

/-- The actual executable choice gives the chooser at most half her total,
independently of any Hill-bound, nonnegativity, or ordering assumptions. -/
theorem choose_chooser_le_half {n k : ℕ} (c : Fin n → ℕ → ℚ)
    (a b : Fin n) (hab : a ≠ b) (l : ℕ) (mask : Fin k → Bool) :
    charge c l k (choose c a b l mask) b ≤ mass (c b) l k / 2 := by
  have hsum := maskSum_complement (fun j : Fin k => c b (l + j)) mask
  rw [← mass_eq_fin_sum] at hsum
  unfold choose
  split_ifs with hchoose
  · rw [charge_maskAllocation_left c b a (Ne.symm hab)]
    exact hchoose
  · rw [charge_maskAllocation_right c a b hab]
    linarith

lemma choose_safe {n k : ℕ} (c : Fin n → ℕ → ℚ)
    {A : Finset (Fin n)} {a b : Fin n} (hab : a ≠ b) (hA : A = {a, b})
    (l : ℕ) (mask : Fin k → Bool)
    (hna : ∀ j, 0 ≤ c a j) (haa : Antitone (c a))
    (hnb : ∀ j, 0 ≤ c b j) (habr : Antitone (c b))
    (hs : maskSum (fun j => c a (l + j)) mask ≤ bound 2 (mass (c a) l k) (c a l))
    (hc : maskSum (fun j => c a (l + j)) (fun j => !(mask j)) ≤
      bound 2 (mass (c a) l k) (c a l)) :
    Safe c A l k (choose c a b l mask) := by
  have haA : a ∈ A := by simp [hA]
  have hbA : b ∈ A := by simp [hA]
  have hcard : A.card = 2 := by simp [hA, hab]
  have hhalf := half_le_bound_two (c b) l k hnb habr
  have hsum := maskSum_complement (fun j : Fin k => c b (l + j)) mask
  rw [← mass_eq_fin_sum] at hsum
  unfold choose
  split_ifs with hchoose
  · refine ⟨maskAllocation_valid hbA haA l mask, ?_⟩
    intro i hi
    have hcases : i = a ∨ i = b := by simpa [hA] using hi
    rcases hcases with he | he
    · rw [he, hcard, charge_maskAllocation_right c b a (Ne.symm hab)]
      exact hc
    · rw [he, hcard, charge_maskAllocation_left c b a (Ne.symm hab)]
      exact hchoose.trans hhalf
  · refine ⟨maskAllocation_valid haA hbA l mask, ?_⟩
    intro i hi
    have hcases : i = a ∨ i = b := by simpa [hA] using hi
    rcases hcases with he | he
    · rw [he, hcard, charge_maskAllocation_left c a b hab]
      exact hs
    · rw [he, hcard, charge_maskAllocation_right c a b hab]
      linarith

/-- Executable divider/chooser terminal. No real arithmetic, minimax oracle,
or exponential subset enumeration occurs in this definition. -/
def terminal {n : ℕ} : Terminal n := fun c A l k => do
  let a ← pickMax A (fun _ => 0)
  let b ← pickMax (A.erase a) (fun _ => 0)
  let mask ← divide (c a) l k
  pure (choose c a b l mask)

lemma pick_two {n : ℕ} (A : Finset (Fin n)) (hA : A.card = 2) :
    ∃ a b, pickMax A (fun _ => 0) = some a ∧
      pickMax (A.erase a) (fun _ => 0) = some b ∧ a ≠ b ∧ A = {a, b} := by
  obtain ⟨a, ha, ham, _⟩ := pickMax_spec A (fun _ => 0)
    (Finset.card_pos.mp (by omega))
  have hcard : (A.erase a).card = 1 := by rw [Finset.card_erase_of_mem ham, hA]
  obtain ⟨b, hb, hbm, _⟩ := pickMax_spec (A.erase a) (fun _ => 0)
    (Finset.card_pos.mp (by omega))
  have hsingle' : A.erase a = {b} := by
    obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hcard
    have hbd : b = d := by simpa [hd] using hbm
    simpa [hbd] using hd
  refine ⟨a, b, ha, hb, Ne.symm (Finset.mem_erase.mp hbm).1, ?_⟩
  rw [← Finset.insert_erase ham, hsingle']

/-- Concrete terminal correctness given the independently established semantic
feasibility theorem. This premise is removed by the exact formula bridge. -/
theorem terminal_correct_of_feasible {n : ℕ}
    (hf : ∀ (c : ℕ → ℚ) (l k : ℕ), 0 < k →
      (∀ j, 0 ≤ c j) → Antitone c → mass c l k ≠ 0 → TwoFeasible c l k) :
    TerminalCorrect (@terminal n) := by
  intro c A l k hA hk hn ha hT hpT
  obtain ⟨a, b, hpa, hpb, hab, hpair⟩ := pick_two A hA
  have haA : a ∈ A := by simp [hpair]
  have hbA : b ∈ A := by simp [hpair]
  obtain ⟨mask, hm, hs, hc⟩ := divide_spec (c a) l k hk (hn a haA) (ha a haA)
    (hf (c a) l k hk (hn a haA) (ha a haA) (hT a haA))
  refine ⟨choose c a b l mask, ?_, ?_⟩
  · simp [terminal, hpa, hpb, hm]
  · exact choose_safe c hab hpair l mask (hn a haA) (ha a haA) (hn b hbA) (ha b hbA) hs hc

end ExactHillShares.Algorithm

namespace ExactHillShares.Algorithm

/-- The actual supremum definition, its exact closed form, and finite minimax
attainment supply the DP's feasible subset premise. -/
theorem two_feasible (c : ℕ → ℚ) (l k : ℕ) (hk : 0 < k)
    (hn : ∀ j, 0 ≤ c j) (ha : Antitone c) (hz : mass c l k ≠ 0) :
    TwoFeasible c l k := by
  have hT : 0 < mass c l k := lt_of_le_of_ne (mass_nonneg c l k hn) (Ne.symm hz)
  have hp := head_pos c l k ha hT
  have hpT := head_le_mass c l k hn hk
  unfold TwoFeasible maskSum
  apply rational_feasible_of_hillBound (fun j : Fin k => c (l + j))
    (T := mass c l k) (p := c l) (D := bound 2 (mass c l k) (c l)) hT
  · intro j
    exact ⟨hn _, ha (by omega)⟩
  · exact (mass_eq_fin_sum c l k).symm
  · exact ⟨⟨0, hk⟩, by simp⟩
  · rw [hillBound_eq_numericalBound (by norm_num) (by exact_mod_cast hT)
      (by exact_mod_cast hp) (by exact_mod_cast hpT), cast_bound (by norm_num) hz]

/-- Verified corrected Algorithm 2: semantic Hill feasibility, the singleton
shortcut, both DP directions, reconstruction, and the other agent's choice. -/
theorem terminal_correct {n : ℕ} : TerminalCorrect (@terminal n) :=
  terminal_correct_of_feasible two_feasible

end ExactHillShares.Algorithm

namespace ExactHillShares.Algorithm
open scoped BigOperators

/-- Explicit charged rational+floor model for the divider. Rational arithmetic,
comparison, and floor each cost one unit; the polynomial does not bound bit
complexity. The DP contribution is its actual two-run array counter. The linear
term covers the finite-row construction, total, threshold, and branch tests.
This is a model counter, not a theorem about Lean VM instruction counts. -/
def divideOps (c : ℕ → ℚ) (l k : ℕ) : ℕ :=
  let T := mass c l k
  let D := bound 2 T (c l)
  40 * (k + 1) +
    if T = 0 ∨ T ≤ 3 * c l then 0
    else Trimmed.solveOps (List.ofFn fun j : Fin k => c (l + j)) (T - D) D

/-- The denominator-independent cubic bound includes the singleton shortcut. -/
theorem divideOps_cubic (c : ℕ → ℚ) (l k : ℕ) (hk : 0 < k)
    (hn : ∀ j, 0 ≤ c j) (ha : Antitone c) :
    divideOps c l k ≤ 2080 * k^3 := by
  have hk1 : 1 ≤ k := hk
  have hkk : k ≤ k^3 := by nlinarith [sq_nonneg (k : ℤ)]
  have hk3 : 1 ≤ k^3 := by nlinarith
  unfold divideOps
  dsimp only
  split_ifs with h
  · nlinarith
  · have hz : mass c l k ≠ 0 := fun hz => h (Or.inl hz)
    have hsmall : 3 * c l < mass c l k := lt_of_not_ge (fun hh => h (Or.inr hh))
    have hT : 0 < mass c l k := lt_of_le_of_ne (mass_nonneg c l k hn) (Ne.symm hz)
    have hw := bound_two_width c l k hn ha hT hsmall
    have hsum : (List.ofFn fun j : Fin k => c (l + j)).sum = mass c l k := by
      rw [List.sum_ofFn, ← mass_eq_fin_sum]
    have H := Trimmed.solveOps_cubic
      (cs := List.ofFn fun j : Fin k => c (l + j))
      (L := mass c l k - bound 2 (mass c l k) (c l))
      (U := bound 2 (mass c l k) (c l))
      (by simpa using hk)
      (by intro x hx; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx; exact hn _)
      (by linarith)
      (by
        simp only [List.length_ofFn, hsum]
        convert hw.2 using 1 <;> ring)
    simp only [List.length_ofFn] at H
    nlinarith

/-- Charged terminal work on the actual selected divider. Selection scans the
active agents; the quadratic allowance covers reading the linked Boolean mask
for the chooser and materializing all k output assignments. An array of witness
bits makes these latter phases linear, but is not needed for the cubic bound. -/
def terminalOps {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ) : ℕ :=
  100 * (A.card + 1) + 100 * (k + 1)^2 +
  match pickMax A (fun _ => 0) with
  | none => 0
  | some a => divideOps (c a) l k

theorem terminalOps_cubic {n : ℕ} (c : Fin n → ℕ → ℚ)
    (A : Finset (Fin n)) (l k : ℕ) (hA : A.card = 2) (hk : 0 < k)
    (hn : ∀ i ∈ A, ∀ j, 0 ≤ c i j) (ha : ∀ i ∈ A, Antitone (c i)) :
    terminalOps c A l k ≤ 3000 * k^3 := by
  obtain ⟨a, hp, ham, _⟩ := pickMax_spec A (fun _ => 0)
    (Finset.card_pos.mp (by omega))
  have hd := divideOps_cubic (c a) l k hk (hn a ham) (ha a ham)
  have hk1 : 1 ≤ k := hk
  have hk2 : k^2 ≤ k^3 := by nlinarith [sq_nonneg (k : ℤ)]
  have hkk : k ≤ k^3 := by nlinarith [sq_nonneg (k : ℤ)]
  have hk3 : 1 ≤ k^3 := by nlinarith
  simp only [terminalOps, hA, hp]
  nlinarith

end ExactHillShares.Algorithm
