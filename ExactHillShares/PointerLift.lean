import ExactHillShares.OrderedReduction
import Mathlib.Data.Fintype.BigOperators

/-!
# Array-and-pointer implementation of the ordered-instance lift

Ranks are processed cheapest first. Each agent owns one cursor into its array
of sorted original indices. A single global Boolean array records used items.
Only the current owner's cursor advances. Finsets below occur exclusively in
proofs; executable membership tests are Boolean array reads.

The operation model is unit-cost indexed array read/write and bounded integer
control, not bit complexity or Lean VM running time. Native `Vector` is backed
by `Array`; no function-update history is traversed by the implementation.
-/
namespace ExactHillShares.PointerLift
open scoped BigOperators

abbrev read {α : Type*} {m : ℕ} (a : Vector α m) (i : Fin m) : α := a[i.val]
abbrev write {α : Type*} {m : ℕ} (a : Vector α m) (i : Fin m) (x : α) : Vector α m :=
  a.set i.val x

@[simp] theorem read_write {α : Type*} {m : ℕ} (a : Vector α m)
    (i j : Fin m) (x : α) : read (write a i x) j = if i = j then x else read a j := by
  simp only [read, write, Vector.getElem_set]
  congr 1
  exact propext Fin.ext_iff.symm

@[simp] theorem read_ofFn {α : Type*} {m : ℕ} (f : Fin m → α) (i : Fin m) :
    read (Vector.ofFn f) i = f i := by simp [read]

def usedSet {m : ℕ} (flags : Vector Bool m) : Finset (Fin m) :=
  Finset.univ.filter (fun x => read flags x = true)

@[simp] theorem mem_usedSet {m : ℕ} (flags : Vector Bool m) (x : Fin m) :
    x ∈ usedSet flags ↔ read flags x = true := by simp [usedSet]

lemma usedSet_write {m : ℕ} (flags : Vector Bool m) (x : Fin m) :
    usedSet (write flags x true) = insert x (usedSet flags) := by
  ext y
  simp only [mem_usedSet, read_write, Finset.mem_insert]
  by_cases h : x = y
  · subst y; simp
  · simp only [h, Ne.symm h, if_false, false_or]

/-- The actual first-unused scan returns its executed number of array probes. -/
structure Found {m : ℕ} (row : Vector (Fin m) m) (flags : Vector Bool m) (p : ℕ) where
  position : Fin m
  visits : ℕ
  lower : p ≤ position.val
  unused : read flags (read row position) = false
  skipped : ∀ j : Fin m, j.val < position.val → read flags (read row j) = true
  visits_eq : visits + p = position.val + 1

/-- Each recursive call advances exactly one position. Proof arguments erase. -/
def seek {m : ℕ} (row : Vector (Fin m) m) (flags : Vector Bool m) (p : ℕ)
    (hp : ∀ j : Fin m, j.val < p → read flags (read row j) = true)
    (hex : ∃ j : Fin m, p ≤ j.val ∧ read flags (read row j) = false) :
    Found row flags p := by
  have hpm : p < m := by obtain ⟨j, hj, _⟩ := hex; omega
  let j : Fin m := ⟨p, hpm⟩
  by_cases hu : read flags (read row j) = true
  · have hp' : ∀ k : Fin m, k.val < p + 1 → read flags (read row k) = true := by
      intro k hk
      by_cases hkp : k.val < p
      · exact hp k hkp
      · have he : k = j := Fin.ext (by dsimp [j]; omega)
        simpa [he] using hu
    have hex' : ∃ k : Fin m, p + 1 ≤ k.val ∧ read flags (read row k) = false := by
      obtain ⟨k, hk, hku⟩ := hex
      refine ⟨k, ?_, hku⟩
      have hne : k.val ≠ p := by
        intro he
        have hjk : k = j := Fin.ext he
        simp [hjk, hu] at hku
      omega
    let out := seek row flags (p + 1) hp' hex'
    exact ⟨out.position, out.visits + 1, by have := out.lower; omega,
      out.unused, out.skipped, by have := out.visits_eq; omega⟩
  · exact ⟨j, 1, le_rfl, by cases h : read flags (read row j) <;> simp_all,
      hp, by dsimp [j]; omega⟩
termination_by m - p

/-- Injectivity of a row implies that an all-used prefix has at most as many
positions as the whole used array. This is a ghost cardinality argument. -/
lemma prefix_le_card {m : ℕ} (row : Vector (Fin m) m)
    (hi : Function.Injective (read row)) (flags : Vector Bool m) (p : ℕ) (hpm : p ≤ m)
    (hp : ∀ j : Fin m, j.val < p → read flags (read row j) = true) :
    p ≤ (usedSet flags).card := by
  let f : Fin p → Fin m := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hpm⟩
  have hf : Function.Injective f := by
    intro a b h
    have he := congrArg (fun z : Fin m => z.val) h
    exact Fin.ext he
  have hsub : Finset.univ.image (fun j : Fin p => read row (f j)) ⊆ usedSet flags := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_usedSet _ _).mpr (hp (f j) j.isLt)
  have hc := Finset.card_le_card hsub
  have hif : Function.Injective (fun j : Fin p => read row (f j)) := hi.comp hf
  rw [Finset.card_image_of_injective _ hif] at hc
  simpa using hc

lemma unused_exists {m : ℕ} (row : Vector (Fin m) m)
    (hi : Function.Injective (read row)) (flags : Vector Bool m) (k : ℕ)
    (hc : (usedSet flags).card = k) (hk : k < m) (p : ℕ)
    (hp : ∀ j : Fin m, j.val < p → read flags (read row j) = true) :
    ∃ j : Fin m, p ≤ j.val ∧ read flags (read row j) = false := by
  by_contra h
  have hall : ∀ j : Fin m, read flags (read row j) = true := by
    intro j
    by_cases hj : j.val < p
    · exact hp j hj
    · have hnot : read flags (read row j) ≠ false := by
        intro hf
        exact h ⟨j, by omega, hf⟩
      cases he : read flags (read row j) <;> simp_all
  have hh := prefix_le_card row hi flags m le_rfl (fun j _ => hall j)
  omega

/-- Certified execution state after exactly `k` distinct rank assignments. All
five mutable tables are native fixed-size arrays. -/
structure State {n m : ℕ} (rows : Vector (Vector (Fin m) m) n)
    (cost : Fin n → Fin m → ℝ) (owner : Fin m → Fin n) (k : ℕ) where
  flags : Vector Bool m
  pointers : Vector ℕ n
  ranks : Vector (Option (Fin m)) m
  originals : Vector (Option (Fin n)) m
  visits : ℕ
  used_card : (usedSet flags).card = k
  pointer_bound : ∀ i, read pointers i ≤ m
  pointer_prefix : ∀ i j, j.val < read pointers i → read flags (read (read rows i) j) = true
  visit_potential : visits = ∑ i, read pointers i
  assigned : ∀ r : Fin m, r.val < k → ∃ x : Fin m,
    read ranks r = some x ∧ read flags x = true ∧ read originals x = some (owner r) ∧
      cost (owner r) x ≤ cost (owner r) (read (read rows (owner r)) r)
  injective : ∀ r s : Fin m, r.val < k → s.val < k →
    read ranks r = read ranks s → r = s

/-- Constant initialization, one cell per agent or item. -/
def initial {n m : ℕ} (rows : Vector (Vector (Fin m) m) n)
    (cost : Fin n → Fin m → ℝ) (owner : Fin m → Fin n) : State rows cost owner 0 where
  flags := Vector.ofFn (fun _ => false)
  pointers := Vector.ofFn (fun _ => 0)
  ranks := Vector.ofFn (fun _ => none)
  originals := Vector.ofFn (fun _ => none)
  visits := 0
  used_card := by simp [usedSet]
  pointer_bound := by simp
  pointer_prefix := by simp
  visit_potential := by simp
  assigned := by simp
  injective := by simp

lemma sum_write {n : ℕ} (p : Vector ℕ n) (i : Fin n) (v : ℕ) :
    (∑ j, read (write p i v) j) + read p i = (∑ j, read p j) + v := by
  classical
  have hold := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) (fun j => read p j)
    (Finset.mem_univ i)
  have hnew := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun j => read (write p i v) j) (Finset.mem_univ i)
  have he : (∑ j ∈ Finset.univ.erase i, read (write p i v) j) =
      ∑ j ∈ Finset.univ.erase i, read p j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.ne_of_mem_erase hj, Ne.symm (Finset.ne_of_mem_erase hj)]
  rw [he] at hnew
  dsimp only at hold hnew
  rw [show read (write p i v) i = v by simp] at hnew
  omega

/-- One rank step: scan only its owner's row, mark the chosen item, and write
both output directions. No inverse search or repeated membership traversal. -/
def step {n m : ℕ} (rows : Vector (Vector (Fin m) m) n)
    (cost : Fin n → Fin m → ℝ) (owner : Fin m → Fin n)
    (hinj : ∀ i, Function.Injective (read (read rows i)))
    (hsorted : ∀ i, Monotone (fun r => cost i (read (read rows i) r)))
    {k : ℕ} (s : State rows cost owner k) (hk : k < m) : State rows cost owner (k + 1) := by
  let r : Fin m := ⟨k, hk⟩
  let i := owner r
  let found := seek (read rows i) s.flags (read s.pointers i) (s.pointer_prefix i)
    (unused_exists (read rows i) (hinj i) s.flags k s.used_card hk
      (read s.pointers i) (s.pointer_prefix i))
  let q := found.position
  let x := read (read rows i) q
  have hx : read s.flags x = false := found.unused
  have hqk : q.val ≤ k := by
    have h := prefix_le_card (read rows i) (hinj i) s.flags q.val
      (Nat.le_of_lt q.isLt) found.skipped
    rw [s.used_card] at h
    exact h
  have hsafe : cost i x ≤ cost i (read (read rows i) r) := hsorted i hqk
  refine {
    flags := write s.flags x true
    pointers := write s.pointers i (q.val + 1)
    ranks := write s.ranks r (some x)
    originals := write s.originals x (some i)
    visits := s.visits + found.visits
    used_card := ?_
    pointer_bound := ?_
    pointer_prefix := ?_
    visit_potential := ?_
    assigned := ?_
    injective := ?_ }
  · rw [usedSet_write, Finset.card_insert_of_not_mem, s.used_card]
    simpa using hx
  · intro a
    simp only [read_write]
    split_ifs with h
    · exact q.isLt
    · exact s.pointer_bound a
  · intro a j hj
    simp only [read_write] at hj ⊢
    by_cases hai : i = a
    · subst a
      simp only [if_true] at hj
      by_cases hjq : j.val < q.val
      · have ht := found.skipped j hjq
        split_ifs <;> first | rfl | assumption
      · have he : j = q := Fin.ext (by omega)
        simp [he, x]
    · rw [if_neg hai] at hj
      have ht := s.pointer_prefix a j hj
      split_ifs <;> first | rfl | assumption
  · have hsum := sum_write s.pointers i (q.val + 1)
    have hv := found.visits_eq
    have hp := s.visit_potential
    omega
  · intro a ha
    by_cases har : a = r
    · subst a
      exact ⟨x, by simp, by simp, by simp [i], hsafe⟩
    · have hak : a.val < k := by
        have hn : a.val ≠ k := fun h => har (Fin.ext h)
        omega
      obtain ⟨y, hy, hyused, hyown, hysafe⟩ := s.assigned a hak
      have hxy : x ≠ y := by intro h; subst y; simp [hx] at hyused
      refine ⟨y, ?_, ?_, ?_, hysafe⟩
      · simpa [Ne.symm har] using hy
      · simpa [hxy] using hyused
      · simpa [hxy] using hyown
  · intro a b ha hb he
    by_cases har : a = r
    · subst a
      by_cases hbr : b = r
      · exact hbr.symm
      · have hbk : b.val < k := by
          have hn : b.val ≠ k := fun h => hbr (Fin.ext h)
          omega
        obtain ⟨y, hy, hyused, _, _⟩ := s.assigned b hbk
        have hxy : x ≠ y := by intro h; subst y; simp [hx] at hyused
        simp [Ne.symm hbr, hy, hxy] at he
    · by_cases hbr : b = r
      · subst b
        have hak : a.val < k := by
          have hn : a.val ≠ k := fun h => har (Fin.ext h)
          omega
        obtain ⟨y, hy, hyused, _, _⟩ := s.assigned a hak
        have hxy : x ≠ y := by intro h; subst y; simp [hx] at hyused
        simp [Ne.symm har, hy, hxy, Ne.symm hxy] at he
      · have hak : a.val < k := by
          have hn : a.val ≠ k := fun h => har (Fin.ext h)
          omega
        have hbk : b.val < k := by
          have hn : b.val ≠ k := fun h => hbr (Fin.ext h)
          omega
        apply s.injective a b hak hbk
        simpa [Ne.symm har, Ne.symm hbr] using he

/-- Tail-recursive traversal of ranks 0 through m-1. -/
def run {n m : ℕ} (rows : Vector (Vector (Fin m) m) n)
    (cost : Fin n → Fin m → ℝ) (owner : Fin m → Fin n)
    (hinj : ∀ i, Function.Injective (read (read rows i)))
    (hsorted : ∀ i, Monotone (fun r => cost i (read (read rows i) r)))
    (k : ℕ) (hk : k ≤ m) (s : State rows cost owner k) : State rows cost owner m :=
  if h : k < m then run rows cost owner hinj hsorted (k + 1) h
    (step rows cost owner hinj hsorted s h)
  else hk.antisymm (by omega) ▸ s
termination_by m - k

/-- The counted array implementation from precomputed sorted original indices. -/
def execute {n m : ℕ} (rows : Vector (Vector (Fin m) m) n)
    (cost : Fin n → Fin m → ℝ) (owner : Fin m → Fin n)
    (hinj : ∀ i, Function.Injective (read (read rows i)))
    (hsorted : ∀ i, Monotone (fun r => cost i (read (read rows i) r))) :
    State rows cost owner m :=
  run rows cost owner hinj hsorted 0 (Nat.zero_le _) (initial rows cost owner)

/-- Every agent's pointer advances at most m times in the complete run. -/
theorem pointer_advances_le {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) (i : Fin n) : read s.pointers i ≤ m := s.pointer_bound i

/-- Every probe advances the active owner's cursor by one, including the
successful probe. Hence the total actual probes are at most n*m. -/
theorem visits_le {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) : s.visits ≤ n * m := by
  rw [s.visit_potential]
  calc
    _ ≤ ∑ _i : Fin n, m := Finset.sum_le_sum (fun i _ => s.pointer_bound i)
    _ = n * m := by simp

/-- Reads the already-written rank output; the witness proof performs no search. -/
def ranksOf {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) (r : Fin m) : Fin m :=
  (read s.ranks r).get (by obtain ⟨x, hx, _⟩ := s.assigned r r.isLt; simp [hx])

lemma ranksOf_spec {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) (r : Fin m) :
    read s.ranks r = some (ranksOf s r) := by
  obtain ⟨x, hx, _⟩ := s.assigned r r.isLt
  simp [ranksOf, hx]

theorem ranksOf_injective {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) : Function.Injective (ranksOf s) := by
  intro a b h
  apply s.injective a b a.isLt b.isLt
  rw [ranksOf_spec, ranksOf_spec, h]

/-- Computed rank-to-original correspondence is a permutation: exact coverage
and pairwise disjointness do not depend on a feasibility assumption. -/
noncomputable def permutation {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (ranksOf s) ⟨ranksOf_injective s,
    Finite.surjective_of_injective (ranksOf_injective s)⟩

lemma originals_some {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) (x : Fin m) : (read s.originals x).isSome := by
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective (ranksOf_injective s) x
  obtain ⟨y, hy, _, hyown, _⟩ := s.assigned r r.isLt
  have he : y = x := by rw [ranksOf_spec] at hy; simpa [hr] using hy.symm
  simp [← he, hyown]

/-- The returned allocation is itself eagerly materialized in O(m) cells.
It reads the original-owner array directly; no finite inverse is computed. -/
def allocation {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) : Vector (Fin n) m :=
  Vector.ofFn (fun x => (read s.originals x).get (originals_some s x))

lemma allocation_ranksOf {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) (r : Fin m) :
    read (allocation s) (ranksOf s r) = owner r := by
  obtain ⟨x, hx, _, hxown, _⟩ := s.assigned r r.isLt
  have he : ranksOf s r = x := by rw [ranksOf_spec] at hx; exact Option.some.inj hx
  simp [allocation, he, hxown]

theorem itemwise {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) (r : Fin m) :
    cost (owner r) (ranksOf s r) ≤ cost (owner r) (read (read rows (owner r)) r) := by
  obtain ⟨x, hx, _, _, hs⟩ := s.assigned r r.isLt
  have he : ranksOf s r = x := by rw [ranksOf_spec] at hx; exact Option.some.inj hx
  simpa [he] using hs

theorem allocation_safe {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) (i : Fin n) :
    (∑ x, if read (allocation s) x = i then cost i x else 0) ≤
      ∑ r, if owner r = i then cost i (read (read rows i) r) else 0 := by
  classical
  have he := Equiv.sum_comp (permutation s)
    (fun x => if read (allocation s) x = i then cost i x else 0)
  rw [← he]
  apply Finset.sum_le_sum
  intro r _
  change (if read (allocation s) (ranksOf s r) = i then cost i (ranksOf s r) else 0) ≤ _
  rw [allocation_ranksOf]
  by_cases h : owner r = i
  · simpa [h] using itemwise s r
  · simp [h]

/-- Array-RAM charge: initialize n pointer cells and 3m item cells, 16 fixed
operations for each of m rank steps, 6 operations per actual seek probe, and
2m operations to materialize the output owners. A probe reads a sorted index
and a used flag, tests it, and increments local control/cursor counters. -/
def operations {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) : ℕ := n + 21 * m + 6 * s.visits + 1

theorem operations_le {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) : operations s ≤ n + 21 * m + 6 * n * m + 1 := by
  have h := visits_le s
  unfold operations
  simp only [Nat.mul_assoc] at *
  omega

/-- Thus the after-sorting lift is O(nm) when there is at least one agent and
one item; the explicit preceding bound also handles either empty dimension. -/
theorem operations_linear {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) (hn : 0 < n) (hm : 0 < m) :
    operations s ≤ 29 * (n * m) := by
  have h := operations_le s
  have hn' : n ≤ n * m := Nat.le_mul_of_pos_right n hm
  have hm' : m ≤ n * m := Nat.le_mul_of_pos_left m hn
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  simp only [Nat.mul_assoc] at *
  omega

/-- Materialize the sorted original-index permutations once, before the lift. -/
def rowsOfOrder {n m : ℕ} (order : Fin n → Equiv.Perm (Fin m)) :
    Vector (Vector (Fin m) m) n := Vector.ofFn (fun i => let row := order i; Vector.ofFn (fun j => row j))

@[simp] theorem rowsOfOrder_read {n m : ℕ} (order : Fin n → Equiv.Perm (Fin m))
    (i : Fin n) (r : Fin m) : read (read (rowsOfOrder order) i) r = order i r := by
  simp [rowsOfOrder]

/-- Generic sorted-permutation interface, suitable for the separately verified
counted merge-sort. Sorting is not repeated inside the rank loop. -/
def lift {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    (order : Fin n → Equiv.Perm (Fin m))
    (hsorted : ∀ i, Monotone (fun r => cost i (order i r)))
    (owner : Fin m → Fin n) : Vector (Fin n) m :=
  let rows := rowsOfOrder order
  allocation (execute rows cost owner
    (by
      intro i a b h
      apply (order i).injective
      simpa [rows] using h)
    (by intro i; simpa [rows] using hsorted i))

theorem lift_safe {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    (order : Fin n → Equiv.Perm (Fin m))
    (hsorted : ∀ i, Monotone (fun r => cost i (order i r)))
    (owner : Fin m → Fin n) (i : Fin n) :
    (∑ x, if read (lift cost order hsorted owner) x = i then cost i x else 0) ≤
      ∑ r, if owner r = i then cost i (order i r) else 0 := by
  exact (allocation_safe _ i).trans_eq (by simp)

/-- The selected position is cheapest among every globally unused original.
Its row is a permutation, so this quantifies over all original indices. -/
theorem found_cheapest {m : ℕ} (row : Vector (Fin m) m) (flags : Vector Bool m)
    (cost : Fin m → ℝ) (hinj : Function.Injective (read row))
    (hsorted : Monotone (fun r => cost (read row r))) {p : ℕ}
    (f : Found row flags p) (x : Fin m) (hx : read flags x = false) :
    cost (read row f.position) ≤ cost x := by
  obtain ⟨j, hj⟩ := Finite.surjective_of_injective hinj x
  have hle : f.position ≤ j := by
    by_contra h
    have hp := f.skipped j (by simpa only [not_le] using h)
    rw [hj, hx] at hp
    contradiction
  simpa [hj] using hsorted hle

/-- On a rank step, every other agent's cursor is unchanged. -/
theorem step_pointer_other {n m : ℕ} (rows : Vector (Vector (Fin m) m) n)
    (cost : Fin n → Fin m → ℝ) (owner : Fin m → Fin n)
    (hinj : ∀ i, Function.Injective (read (read rows i)))
    (hsorted : ∀ i, Monotone (fun r => cost i (read (read rows i) r)))
    {k : ℕ} (s : State rows cost owner k) (hk : k < m)
    (j : Fin n) (hj : owner ⟨k, hk⟩ ≠ j) :
    read (step rows cost owner hinj hsorted s hk).pointers j = read s.pointers j := by
  simp only [step, read_write, if_neg hj]

/-- A rank step never moves any pointer backwards. -/
theorem step_pointer_monotone {n m : ℕ} (rows : Vector (Vector (Fin m) m) n)
    (cost : Fin n → Fin m → ℝ) (owner : Fin m → Fin n)
    (hinj : ∀ i, Function.Injective (read (read rows i)))
    (hsorted : ∀ i, Monotone (fun r => cost i (read (read rows i) r)))
    {k : ℕ} (s : State rows cost owner k) (hk : k < m) (j : Fin n) :
    read s.pointers j ≤ read (step rows cost owner hinj hsorted s hk).pointers j := by
  simp only [step, read_write]
  split_ifs with h
  · subst j
    have h := (seek (read rows (owner ⟨k, hk⟩)) s.flags
      (read s.pointers (owner ⟨k, hk⟩)) (s.pointer_prefix (owner ⟨k, hk⟩))
      (unused_exists _ (hinj _) _ k s.used_card hk _ (s.pointer_prefix _))).lower
    omega
  · exact le_rfl

/-- The actual probes added by a rank step are exactly the movement of the
active agent's pointer. This is the per-agent amortization identity. -/
theorem step_visit_charge {n m : ℕ} (rows : Vector (Vector (Fin m) m) n)
    (cost : Fin n → Fin m → ℝ) (owner : Fin m → Fin n)
    (hinj : ∀ i, Function.Injective (read (read rows i)))
    (hsorted : ∀ i, Monotone (fun r => cost i (read (read rows i) r)))
    {k : ℕ} (s : State rows cost owner k) (hk : k < m) :
    (step rows cost owner hinj hsorted s hk).visits + read s.pointers (owner ⟨k, hk⟩) =
      s.visits + read (step rows cost owner hinj hsorted s hk).pointers (owner ⟨k, hk⟩) := by
  have h := (seek (read rows (owner ⟨k, hk⟩)) s.flags
    (read s.pointers (owner ⟨k, hk⟩)) (s.pointer_prefix (owner ⟨k, hk⟩))
    (unused_exists _ (hinj _) _ k s.used_card hk _ (s.pointer_prefix _))).visits_eq
  simp only [step, read_write, if_true]
  omega

/-- Exact disjointness of the computed original bundles. -/
theorem bundles_disjoint {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) (i j : Fin n) (hij : i ≠ j) :
    Disjoint (Finset.univ.filter (fun x => read (allocation s) x = i))
      (Finset.univ.filter (fun x => read (allocation s) x = j)) := by
  rw [Finset.disjoint_left]
  intro x hi hj
  exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

/-- Every original belongs to exactly one computed agent bundle. -/
theorem bundles_cover {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) :
    (Finset.univ.biUnion (fun i : Fin n =>
      Finset.univ.filter (fun x => read (allocation s) x = i))) = Finset.univ := by
  ext x
  simp

/-- Including the optional materialization of n sorted-index rows costs n*m
additional cell reads/writes, and still has the same asymptotic bound. -/
theorem with_row_materialization_linear {n m : ℕ} {rows : Vector (Vector (Fin m) m) n}
    {cost : Fin n → Fin m → ℝ} {owner : Fin m → Fin n}
    (s : State rows cost owner m) (hn : 0 < n) (hm : 0 < m) :
    2 * (n * m) + operations s ≤ 31 * (n * m) := by
  have h := operations_linear s hn hm
  omega

end ExactHillShares.PointerLift
