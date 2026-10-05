import ExactHillShares.RecursiveAllocation
import ExactHillShares.Terminal

/-!
# Charged arithmetic runtime of the implemented moving knife

The cost model charges rational addition, multiplication, division, comparison,
exact floor, array access and fixed-size allocation at unit cost. It is NOT a
bit-complexity bound. Access to a row entry is an array lookup. Finite active
sets are traversed linearly; no constant-time finite-set operation is assumed.

The implementation uses linear prefix scans. It consequently has a verified
`O(n²m + m³)` recursion bound, rather than asserting binary-search costs for a
linear program. The sorting/lifting costs are separate. An implicit assignment
is returned; materializing its `m` owners costs an additional `O(nm)`.
-/
namespace ExactHillShares.Algorithm
open scoped BigOperators

/-- One evaluation of the moving-knife score: sum the row, evaluate the fixed
piecewise rational formula, and perform the actual strict-crossing scan. -/
def rowScanOps (c : ℕ → ℚ) (l k q : ℕ) : ℕ :=
  2 * k + 32 + 4 * scanVisits c l k (bound q (mass c l k) (c l))

lemma rowScanOps_le (c l k q) : rowScanOps c l k q ≤ 32 * (k + 1) := by
  unfold rowScanOps
  have := scanVisits_le c l k (bound q (mass c l k) (c l))
  omega

/-- Two score passes (maximum and argmax filter), a tie-breaking scan, and one
last score evaluation for the returned agent. `maxCandidates` explicitly binds
the maximum once, so it is not recomputed inside the filter. -/
def knifeOps {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ) : ℕ :=
  2 * (∑ i ∈ A, rowScanOps (c i) l k A.card) + 8 * A.card + 10 +
    match pickMax A (fun i => safePrefix (c i) l k (bound A.card (mass (c i) l k) (c i l))) with
    | none => 0
    | some a => rowScanOps (c a) l k A.card

lemma knifeOps_le {n : ℕ} (c : Fin n → ℕ → ℚ) (A : Finset (Fin n)) (l k : ℕ) :
    knifeOps c A l k ≤ 110 * (A.card + 1) * (k + 1) := by
  have hs : (∑ i ∈ A, rowScanOps (c i) l k A.card) ≤ A.card * (32 * (k + 1)) := by
    calc
      _ ≤ ∑ _i ∈ A, 32 * (k + 1) := Finset.sum_le_sum fun i hi => rowScanOps_le _ _ _ _
      _ = _ := by simp
  unfold knifeOps
  split
  · nlinarith
  · have hh := rowScanOps_le (c ‹Fin n›) l k A.card
    nlinarith

/-- The early-rule pass evaluates each row total at most twice and scans the
candidate active set to choose its least identifier. -/
def earlyOps {n : ℕ} (A : Finset (Fin n)) (k : ℕ) : ℕ :=
  A.card * (4 * k + 8) + 2 * A.card + 4

lemma earlyOps_le {n : ℕ} (A : Finset (Fin n)) (k : ℕ) :
    earlyOps A k ≤ 14 * (A.card + 1) * (k + 1) := by unfold earlyOps; nlinarith

/-- The operation counter follows the exact branch and recursion structure of
`runWith`. `terminalOps` is the separately charged two-bin implementation. -/
def runOpsWith {n : ℕ} (terminalOps : (Fin n → ℕ → ℚ) →
    Finset (Fin n) → ℕ → ℕ → ℕ) (terminal : Terminal n) (c : Fin n → ℕ → ℚ) :
    ℕ → Finset (Fin n) → ℕ → ℕ → ℕ
  | 0, _, _, _ => 1
  | fuel + 1, A, l, k =>
    if k = 0 then 1
    else if A.Nonempty then
      if A.card = 1 then 5 + 4 * A.card
      else
        let pre := 20 + 4 * A.card + earlyOps A k
        match early c A l k with
        | some _ => pre + 5
        | none => if A.card = 2 then pre + terminalOps c A l k
          else match knife c A l k with
            | none => pre + knifeOps c A l k
            | some (a, s) => pre + knifeOps c A l k + 5 +
                runOpsWith terminalOps terminal c fuel (A.erase a) (l + s) (k - s)
    else 5

lemma knife_some {n : ℕ} {c : Fin n → ℕ → ℚ} {A : Finset (Fin n)} {l k : ℕ}
    {a : Fin n} {s : ℕ} (h : knife c A l k = some (a, s)) : a ∈ A := by
  unfold knife at h
  dsimp only at h
  cases he : pickMax A (fun i => safePrefix (c i) l k (bound A.card (mass (c i) l k) (c i l))) with
  | none => simp [he] at h
  | some b =>
    simp [he] at h
    rcases h with ⟨rfl, hs⟩
    exact pickMax_some he

/-- One chain of moving-knife calls plus at most one terminal invocation.
This bound explicitly retains both active-agent and item dependence. -/
theorem runOpsWith_bound {n : ℕ}
    (terminalOps : (Fin n → ℕ → ℚ) → Finset (Fin n) → ℕ → ℕ → ℕ)
    (terminal : Terminal n)
    (ht : ∀ c A l k, A.card = 2 → 0 < k →
      (∀ i ∈ A, ∀ j, 0 ≤ c i j) → (∀ i ∈ A, Antitone (c i)) →
      terminalOps c A l k ≤ 3000 * (k + 1)^3)
    (c : Fin n → ℕ → ℚ) (fuel : ℕ) (A : Finset (Fin n)) (l k : ℕ)
    (hf : A.card ≤ fuel)
    (hn : ∀ i ∈ A, ∀ j, 0 ≤ c i j) (ha : ∀ i ∈ A, Antitone (c i)) :
    runOpsWith terminalOps terminal c fuel A l k ≤
      1000 * fuel^2 * (k + 1) + 3000 * (k + 1)^3 := by
  induction fuel generalizing A l k with
  | zero =>
    have hpos : 0 < (k + 1)^3 := pow_pos (by omega) _
    simp only [runOpsWith, zero_pow (by decide : 2 ≠ 0), Nat.mul_zero, Nat.zero_mul, zero_add]
    omega
  | succ fuel ih =>
    have hearly := earlyOps_le A k
    have hknife := knifeOps_le c A l k
    have hpoly : 20 + 4 * A.card + earlyOps A k + knifeOps c A l k + 5 ≤
        160 * (A.card + 1) * (k + 1) := by nlinarith
    have hlevel : 20 + 4 * A.card + earlyOps A k + knifeOps c A l k + 5 +
        1000 * fuel^2 * (k + 1) ≤ 1000 * (fuel + 1)^2 * (k + 1) := by
      have hmul : (A.card + 1) * (k + 1) ≤ (fuel + 2) * (k + 1) := by nlinarith
      nlinarith
    have hcubepos : 0 < (k + 1)^3 := pow_pos (by omega) _
    have hpos : 5 ≤ 1000 * (k + 1)^3 := by omega
    by_cases hk : k = 0
    · simp only [runOpsWith, if_pos hk]
      omega
    by_cases hA : A.Nonempty
    · simp only [runOpsWith, if_neg hk, if_pos hA]
      by_cases hq : A.card = 1
      · rw [if_pos hq, hq]
        nlinarith
      rw [if_neg hq]
      cases he : early c A l k with
      | some a => simp only; nlinarith
      | none =>
        simp only
        by_cases hq2 : A.card = 2
        · rw [if_pos hq2]
          have hh := ht c A l k hq2 (by omega) hn ha
          nlinarith
        rw [if_neg hq2]
        cases hki : knife c A l k with
        | none => simp only; nlinarith
        | some pair =>
          rcases pair with ⟨a, s⟩
          simp only
          have hmem := knife_some hki
          have hcard := Finset.card_erase_add_one hmem
          have hrec := ih (A.erase a) (l + s) (k - s) (by omega)
            (fun i hi => hn i (Finset.mem_of_mem_erase hi))
            (fun i hi => ha i (Finset.mem_of_mem_erase hi))
          have hm : k - s + 1 ≤ k + 1 := by omega
          have hp : (k - s + 1)^3 ≤ (k + 1)^3 := Nat.pow_le_pow_left hm 3
          have hm' : fuel^2 * (k - s + 1) ≤ fuel^2 * (k + 1) := Nat.mul_le_mul_left _ hm
          nlinarith
    · simp only [runOpsWith, if_neg hk, if_neg hA]
      omega

/-- The singleton preprocessing makes the number of processed rows at most
`m`. In the nontrivial branch `n<m`, the recursion is cubic in the item count. -/
theorem runOpsWith_item_cubic {n : ℕ}
    (terminalOps : (Fin n → ℕ → ℚ) → Finset (Fin n) → ℕ → ℕ → ℕ)
    (terminal : Terminal n)
    (ht : ∀ c A l k, A.card = 2 → 0 < k →
      (∀ i ∈ A, ∀ j, 0 ≤ c i j) → (∀ i ∈ A, Antitone (c i)) →
      terminalOps c A l k ≤ 3000 * (k + 1)^3)
    (c : Fin n → ℕ → ℚ) (m : ℕ) (hnm : n ≤ m)
    (hn : ∀ i j, 0 ≤ c i j) (ha : ∀ i, Antitone (c i)) :
    runOpsWith terminalOps terminal c n Finset.univ 0 m ≤ 4000 * (m + 1)^3 := by
  have h := runOpsWith_bound terminalOps terminal ht c n Finset.univ 0 m (by simp)
    (fun i hi => hn i) (fun i hi => ha i)
  have hn2 : n^2 ≤ (m + 1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hh : n^2 * (m + 1) ≤ (m + 1)^3 := by
    calc
      n^2 * (m + 1) ≤ (m + 1)^2 * (m + 1) := Nat.mul_le_mul_right _ hn2
      _ = _ := by ring
  nlinarith

end ExactHillShares.Algorithm

namespace ExactHillShares.Algorithm

/-- The concrete verified terminal discharges the cost contract; no generic
runtime component remains in this theorem. -/
theorem recursive_arithmetic_bound {n : ℕ} (c : Fin n → ℕ → ℚ)
    (A : Finset (Fin n)) (l k : ℕ)
    (hn : ∀ i ∈ A, ∀ j, 0 ≤ c i j) (ha : ∀ i ∈ A, Antitone (c i)) :
    runOpsWith terminalOps terminal c A.card A l k ≤
      1000 * A.card^2 * (k + 1) + 3000 * (k + 1)^3 := by
  apply runOpsWith_bound terminalOps terminal _ c A.card A l k le_rfl hn ha
  intro c A l k hA hk hn ha
  exact (terminalOps_cubic c A l k hA hk hn ha).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))

/-- Cubic arithmetic bound for the nontrivial ordered branch after `m≤n`
instances have been answered by the implicit singleton assignment. -/
theorem recursive_item_cubic {n : ℕ} (c : Fin n → ℕ → ℚ) (m : ℕ)
    (hnm : n ≤ m) (hn : ∀ i j, 0 ≤ c i j) (ha : ∀ i, Antitone (c i)) :
    runOpsWith terminalOps terminal c n Finset.univ 0 m ≤ 4000 * (m + 1)^3 := by
  apply runOpsWith_item_cubic terminalOps terminal _ c m hnm hn ha
  intro c A l k hA hk hn ha
  exact (terminalOps_cubic c A l k hA hk hn ha).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))

/-- Materializing every implicit recursive owner traverses at most one closure
per eliminated agent. The quadratic terminal-mask allowance is already included
in `terminalOps`; this term accounts for the outer prefix closures. -/
def materializationOps (n m : ℕ) : ℕ := 4 * (n + 1) * m

/-- A concrete, conservative arithmetic bound including owner materialization.
It displays the n,m dependence before the singleton preprocessing is applied. -/
theorem recursion_with_output_bound {n : ℕ} (c : Fin n → ℕ → ℚ) (m : ℕ)
    (hn : ∀ i j, 0 ≤ c i j) (ha : ∀ i, Antitone (c i)) :
    runOpsWith terminalOps terminal c n Finset.univ 0 m + materializationOps n m ≤
      1000 * n^2 * (m + 1) + 3000 * (m + 1)^3 + 4 * (n + 1) * m := by
  have h := recursive_arithmetic_bound c Finset.univ 0 m
    (fun i hi => hn i) (fun i hi => ha i)
  simpa [materializationOps] using Nat.add_le_add_right h (materializationOps n m)

end ExactHillShares.Algorithm
