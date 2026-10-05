import Mathlib

/-!
# Paper-first mathematical contracts

The initial core model, formula and existence contracts were formulated from
arXiv:2609.35801v1 before inspecting implementation theorem statements. The
rational interface was then refined to expose failure, and the ordered-tail
and interval-width contracts were added during source correspondence review.
All definitions express the paper's mathematics without implementation aliases.
No implementation module is imported here.
-/

namespace PaperContract

noncomputable section
open scoped BigOperators

/-- An owner function gives every item exactly one owner, allowing empty bundles. -/
def bundle {n m : ℕ} (c : Fin m → ℝ) (owner : Fin m → Fin n) (i : Fin n) : ℝ :=
  ∑ j : Fin m, if owner j = i then c j else 0

/-- The maximum load of a partition, expressed independently as a supremum. -/
def peak {n m : ℕ} (c : Fin m → ℝ) (owner : Fin m → Fin n) : ℝ :=
  sSup (Set.range (bundle c owner))

/-- The minimax share is the infimum over all owner functions. -/
def minimax (n m : ℕ) (c : Fin m → ℝ) : ℝ :=
  sInf (Set.range (fun owner : Fin m → Fin n => peak c owner))

/-- Normalization and an *attained*, exact largest-item value. -/
def exactMaximum (m : ℕ) (c : Fin m → ℝ) (a : ℝ) : Prop :=
  (∀ j, 0 ≤ c j) ∧ (∑ j : Fin m, c j) = 1 ∧
  (∀ j, c j ≤ a) ∧ ∃ j, c j = a

/-- Section 1: all finite instances are quantified over, without fixing item count. -/
def exactShare (n : ℕ) (a : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ m : ℕ, ∃ c : Fin m → ℝ,
    exactMaximum m c a ∧ z = minimax n m c}

/-- Proposition 4.1, after normalizing total cost to one. -/
def ordinaryFormula (n : ℕ) (a : ℝ) : ℝ :=
  let k : ℕ := ⌊(1 - a) / ((n : ℝ) * a)⌋₊
  max (((k : ℝ) + 1) * a)
    ((((k : ℝ) + 2) * (1 - a)) / ((n : ℝ) * ((k : ℝ) + 1)))

/-- Proposition 4.2, including the exceptional two-agent ranges. -/
def twoFormula (a : ℝ) : ℝ :=
  if 1 / 3 ≤ a then max a (1 - a)
  else if 2 / 7 ≤ a then 2 * a
  else if 7 / 27 ≤ a then (2 + 3 * a) / 5
  else if 1 / 5 ≤ a then 3 * (1 - a) / 4
  else ordinaryFormula 2 a

/-- Exact formula target, restricted below to n ≥ 2 and 0 < a ≤ 1. -/
def formula (n : ℕ) (a : ℝ) : ℝ :=
  if n = 2 then twoFormula a else ordinaryFormula n a

/-- Proposition 4.1/4.2 mean equality with the supremum, not merely a safe bound. -/
def SupremumFormula : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ, 0 < a → a ≤ 1 →
    exactShare n a = formula n a

/-- Theorem 1.1's real-valued existence claim; no computability assumption. -/
def RealExistence : Prop :=
  ∀ n m : ℕ, 2 ≤ n → ∀ c : Fin n → Fin m → ℝ, ∀ a : Fin n → ℝ,
    (∀ i, exactMaximum m (c i) (a i)) →
    ∃ owner : Fin m → Fin n, ∀ i,
      bundle (c i) owner i ≤ exactShare n (a i)

/-- Cost of the first `s` entries of an ordered row. Entries after the finite
item count are irrelevant; a finite row can be extended by zeros. -/
def prefixMass (c : ℕ → ℝ) (s : ℕ) : ℝ := ∑ j ∈ Finset.range s, c j

/-- Lemmas 4.3 and 4.4 together: a strict crossing protects the genuine share
of the remaining tail. No hypothesis assumes its desired conclusion. -/
def OrderedTailDomination : Prop :=
  ∀ n m s : ℕ, 3 ≤ n → s < m →
    ∀ c : ℕ → ℝ, Antitone c → (∀ j, 0 ≤ c j) → prefixMass c m = 1 →
      exactShare n (c 0) < prefixMass c (s + 1) → 0 < 1 - prefixMass c s →
      (1 - prefixMass c s) * exactShare (n - 1) (c s / (1 - prefixMass c s)) ≤
        exactShare n (c 0)

/-- Lemma 5.1: quantitative slack for the low-maximum terminal routine. -/
def FeasibleIntervalWidth : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ 1 / 3 → (3 / 7) * a ≤ 2 * exactShare 2 a - 1

/-- An interface, independent of how an executable allocator is implemented.
`none` represents failure, which the correctness contract must rule out. -/
def RationalAllocator :=
  (n m : ℕ) → (Fin n → Fin m → ℚ) → Option (Fin m → Fin n)

/-- The paper's exact-rational executable scope on normalized rows, n ≥ 2.
Success and the bound are both required. This is mathematical output correctness;
it intentionally does not assert the literal pseudocode or O(m³) machine time. -/
def RationalCorrectness (allocate : RationalAllocator) : Prop :=
  ∀ n m : ℕ, 2 ≤ n →
    ∀ c : Fin n → Fin m → ℚ, ∀ a : Fin n → ℝ,
      (∀ i, exactMaximum m (fun j => (c i j : ℝ)) (a i)) →
      ∃ owner : Fin m → Fin n,
        allocate n m c = some owner ∧
        ∀ i, bundle (fun j => (c i j : ℝ)) owner i ≤ exactShare n (a i)

end
end PaperContract
