import ExactHillShares.BinaryCrossing

namespace ExactHillShares.Algorithm

/-- Eagerly computed boundaries and the arithmetic/query charge that produced
them. Each row's binary computation occurs once, before maximum selection. -/
structure BoundaryBatch (α : Type*) where
  values : List (α × ℕ)
  queries : ℕ
  operations : ℕ

/-- Linear list traversal is used only for the active-agent set, never for
random access to a cost row or a prefix sum. -/
def computeBoundaryBatch {α : Type*} (compute : α → BinaryResult) :
    List α → BoundaryBatch α
  | [] => ⟨[], 0, 1⟩
  | a :: as =>
    let row := compute a
    let rest := computeBoundaryBatch compute as
    ⟨(a, row.boundary) :: rest.values, row.queries + rest.queries,
      row.operations + rest.operations + 4⟩

@[simp] theorem computeBoundaryBatch_values {α : Type*} (compute : α → BinaryResult)
    (as : List α) :
    (computeBoundaryBatch compute as).values = as.map (fun a => (a, (compute a).boundary)) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [computeBoundaryBatch, ih]

@[simp] theorem computeBoundaryBatch_length {α : Type*} (compute : α → BinaryResult)
    (as : List α) : (computeBoundaryBatch compute as).values.length = as.length := by simp

theorem computeBoundaryBatch_counts {α : Type*} (compute : α → BinaryResult)
    (as : List α) (Q W : ℕ)
    (hq : ∀ a ∈ as, (compute a).queries ≤ Q)
    (hw : ∀ a ∈ as, (compute a).operations ≤ W) :
    (computeBoundaryBatch compute as).queries ≤ as.length * Q ∧
    (computeBoundaryBatch compute as).operations ≤ as.length * (W + 4) + 1 := by
  induction as with
  | nil => simp [computeBoundaryBatch]
  | cons a as ih =>
    have hh := ih (fun b hb => hq b (by simp [hb])) (fun b hb => hw b (by simp [hb]))
    have hqa := hq a (by simp)
    have hwa := hw a (by simp)
    simp only [computeBoundaryBatch, List.length_cons]
    constructor <;> nlinarith [hh.1, hh.2]

/-- Counted linear argmax over stored natural-number boundaries. -/
structure BoundaryChoice (α : Type*) where
  value : Option (α × ℕ)
  operations : ℕ

def bestBoundary {α : Type*} : List (α × ℕ) → BoundaryChoice α
  | [] => ⟨none, 1⟩
  | a :: as =>
    let tail := bestBoundary as
    match tail.value with
    | none => ⟨some a, tail.operations + 3⟩
    | some b => ⟨some (if a.2 ≤ b.2 then b else a), tail.operations + 5⟩

theorem bestBoundary_operations {α : Type*} (as : List (α × ℕ)) :
    (bestBoundary as).operations ≤ 5 * as.length + 1 := by
  induction as with
  | nil => simp [bestBoundary]
  | cons a as ih =>
    simp only [bestBoundary, List.length_cons]
    split <;> dsimp only <;> omega

/-- The selected pair is a member and its boundary dominates every stored
boundary. No tie convention or evaluation-strategy assumption is needed. -/
theorem bestBoundary_spec {α : Type*} (as : List (α × ℕ)) :
    match (bestBoundary as).value with
    | none => as = []
    | some b => b ∈ as ∧ ∀ a ∈ as, a.2 ≤ b.2 := by
  induction as with
  | nil => simp [bestBoundary]
  | cons a as ih =>
    cases ht : (bestBoundary as).value with
    | none =>
      have he : as = [] := by simpa [ht] using ih
      subst as
      simp [bestBoundary]
    | some b =>
      have hh : b ∈ as ∧ ∀ d ∈ as, d.2 ≤ b.2 := by simpa [ht] using ih
      simp only [bestBoundary, ht]
      split_ifs with h
      · refine ⟨List.mem_cons_of_mem a hh.1, ?_⟩
        intro d hd
        rcases List.mem_cons.mp hd with hd | hd
        · simpa [hd] using h
        · exact hh.2 d hd
      · refine ⟨List.mem_cons_self, ?_⟩
        intro d hd
        rcases List.mem_cons.mp hd with hd | hd
        · simp [hd]
        · exact (hh.2 d hd).trans (by omega)

theorem bestBoundary_exists {α : Type*} (as : List (α × ℕ)) (hne : as ≠ []) :
    ∃ b, (bestBoundary as).value = some b ∧ b ∈ as ∧ ∀ a ∈ as, a.2 ≤ b.2 := by
  have hh := bestBoundary_spec as
  cases he : (bestBoundary as).value with
  | none => simp [he] at hh; exact False.elim (hne hh)
  | some b => exact ⟨b, rfl, by simpa [he] using hh⟩

/-- Combined counted stage: score each row once, then scan stored scores once. -/
def batchBest {α : Type*} (compute : α → BinaryResult) (as : List α) :
    BoundaryChoice α × ℕ :=
  let batch := computeBoundaryBatch compute as
  let chosen := bestBoundary batch.values
  (⟨chosen.value, batch.operations + chosen.operations⟩, batch.queries)

theorem batchBest_operations {α : Type*} (compute : α → BinaryResult)
    (as : List α) (Q W : ℕ)
    (hq : ∀ a ∈ as, (compute a).queries ≤ Q)
    (hw : ∀ a ∈ as, (compute a).operations ≤ W) :
    (batchBest compute as).1.operations ≤ as.length * (W + 9) + 2 ∧
    (batchBest compute as).2 ≤ as.length * Q := by
  have hb := computeBoundaryBatch_counts compute as Q W hq hw
  have hm := bestBoundary_operations (computeBoundaryBatch compute as).values
  rw [computeBoundaryBatch_length] at hm
  dsimp only [batchBest]
  constructor <;> nlinarith [hb.1, hb.2]

theorem batchBest_spec {α : Type*} (compute : α → BinaryResult)
    (as : List α) (hne : as ≠ []) :
    ∃ a ∈ as,
      (batchBest compute as).1.value = some (a, (compute a).boundary) ∧
      ∀ b ∈ as, (compute b).boundary ≤ (compute a).boundary := by
  have hne' : (computeBoundaryBatch compute as).values ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [computeBoundaryBatch_length, List.length_nil] at hl
    exact hne (List.length_eq_zero_iff.mp hl)
  obtain ⟨b, hb, hmem, hmax⟩ := bestBoundary_exists (computeBoundaryBatch compute as).values hne'
  rw [computeBoundaryBatch_values] at hmem
  obtain ⟨a, ha, hab⟩ := List.mem_map.mp hmem
  subst b
  refine ⟨a, ha, hb, ?_⟩
  intro d hd
  exact hmax (d, (compute d).boundary) (by simp [hd])

end ExactHillShares.Algorithm
