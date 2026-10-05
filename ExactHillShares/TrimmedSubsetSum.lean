import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# One-sided, witness-carrying trimmed subset sum

The implementation uses exact rational numbers and deterministic bucket arrays.
Each witness is a linked list of include/exclude bits; consing a bit shares its
predecessor. The complexity statements use unit-cost rational arithmetic,
comparison and floor, and unit-cost array reads/writes. They are not bit-cost
bounds. The routine deliberately requires a positive trimming width: the
large-maximum shortcut must precede it in the two-agent allocation routine.
-/

namespace ExactHillShares.Trimmed

structure State where
  value : ℚ
  bits : List Bool
  deriving DecidableEq, Repr

def zero : State := ⟨0, []⟩
def skip (x : State) : State := ⟨x.value, false :: x.bits⟩
def take (c : ℚ) (x : State) : State := ⟨x.value + c, true :: x.bits⟩

/-- An exact subset witness, including a decision for every item. -/
inductive Witness : List ℚ → State → Prop
  | nil : Witness [] zero
  | skip {cs x} : Witness cs x → Witness (c :: cs) (skip x)
  | take {cs x} : Witness cs x → Witness (c :: cs) (take c x)

def selectedSum : List ℚ → List Bool → ℚ
  | c :: cs, b :: bs => (if b then c else 0) + selectedSum cs bs
  | _, _ => 0

theorem witness_decodes {cs x} (h : Witness cs x) :
    x.bits.length = cs.length ∧ selectedSum cs x.bits = x.value := by
  induction h with
  | nil => simp [zero, selectedSum]
  | skip h ih => simpa [skip, selectedSum] using ih
  | take h ih => simp [take, selectedSum, ih, add_comm]

theorem witness_bounds {cs x} (hn : ∀ c ∈ cs, 0 ≤ c) (h : Witness cs x) :
    0 ≤ x.value ∧ x.value ≤ cs.sum := by
  induction h with
  | nil => simp [zero]
  | @skip c cs x h ih =>
    have hc := hn c (by simp)
    have hx := ih (fun a ha => hn a (by simp [ha]))
    simp only [skip, List.sum_cons]
    constructor <;> linarith [hx.1, hx.2]
  | @take c cs x h ih =>
    have hc := hn c (by simp)
    have hx := ih (fun a ha => hn a (by simp [ha]))
    simp only [take, List.sum_cons]
    constructor <;> linarith [hx.1, hx.2]

/-- `true` means MAX; `false` means MIN. -/
def Before (up : Bool) (a b : ℚ) : Prop := if up then a ≤ b else b ≤ a
instance (up : Bool) (a b : ℚ) : Decidable (Before up a b) :=
  inferInstanceAs (Decidable (if up then a ≤ b else b ≤ a))

theorem before_refl (up) (a) : Before up a a := by cases up <;> simp [Before]
theorem before_trans {up a b c} (h : Before up a b) (h' : Before up b c) :
    Before up a c := by cases up <;> simp_all [Before] <;> linarith

def better (up : Bool) (x y : State) : State :=
  if Before up x.value y.value then y else x

theorem better_mem (up x y) : better up x y = x ∨ better up x y = y := by
  unfold better; split <;> simp_all

theorem before_better_left (up x y) : Before up x.value (better up x y).value := by
  unfold better; split <;> simp_all [before_refl]

theorem before_better_right (up x y) : Before up y.value (better up x y).value := by
  cases up <;> simp [better, Before] <;> split <;> simp_all <;> linarith

def bucket (η z : ℚ) : ℕ := ⌊z / η⌋₊
def buckets (η T : ℚ) : ℕ := bucket η T + 1

theorem bucket_lt {η x T : ℚ} (hη : 0 < η) (hx : x ≤ T) :
    bucket η x < buckets η T := by
  exact Nat.lt_succ_of_le (Nat.floor_mono ((div_le_div_iff_of_pos_right hη).2 hx))

theorem same_bucket_close {η x y : ℚ} (hη : 0 < η) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hb : bucket η x = bucket η y) :
    x < y + η ∧ y < x + η := by
  have hxl := Nat.floor_le (div_nonneg hx hη.le)
  have hyl := Nat.floor_le (div_nonneg hy hη.le)
  have hxu := Nat.lt_floor_add_one (x / η)
  have hyu := Nat.lt_floor_add_one (y / η)
  change (⌊x / η⌋₊ : ℕ) = ⌊y / η⌋₊ at hb
  rw [hb] at hxl hxu
  have h1 : x / η < y / η + 1 := by linarith
  have h2 : y / η < x / η + 1 := by linarith
  constructor
  · have := (div_lt_iff₀ hη).1 h1
    simpa [add_mul, hη.ne'] using this
  · have := (div_lt_iff₀ hη).1 h2
    simpa [add_mul, hη.ne'] using this

abbrev Table := Array (Option State)
def lookup (a : Table) (i : ℕ) : Option State := (a[i]?).join
def entries (a : Table) : List State := a.toList.filterMap id

theorem mem_entries {a : Table} {x : State} :
    x ∈ entries a ↔ ∃ i, lookup a i = some x := by
  simp only [entries, List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, hx⟩
    have hsome : o = some x := hx
    subst o
    have hm : some x ∈ a := by simpa using ho
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 hm
    exact ⟨i, by simp [lookup, hi]⟩
  · rintro ⟨i, hi⟩
    have hg : a[i]? = some (some x) := by
      unfold lookup at hi
      cases he : a[i]? with
      | none => simp [he] at hi
      | some o => cases o <;> simp_all
    refine ⟨some x, ?_, rfl⟩
    simpa using (Array.mem_of_getElem? hg)

theorem lookup_lt {a : Table} {i x} (h : lookup a i = some x) : i < a.size := by
  by_contra hn
  have := Array.getElem?_eq_none (xs := a) (Nat.le_of_not_gt hn)
  simp [lookup, this] at h

/-- Constant-time insertion into the array bucket, keeping the preferred exact witness. -/
def insert (up : Bool) (η : ℚ) (a : Table) (x : State) : Table :=
  let i := bucket η x.value
  match lookup a i with
  | none => a.setIfInBounds i (some x)
  | some y => a.setIfInBounds i (some (better up x y))

@[simp] theorem size_insert (up η a x) : (insert up η a x).size = a.size := by
  unfold insert; dsimp only; split <;> simp

theorem lookup_set (a : Table) (i j : ℕ) (x : State) :
    lookup (a.setIfInBounds i (some x)) j =
      if i = j then if i < a.size then some x else none else lookup a j := by
  simp only [lookup, Array.getElem?_setIfInBounds]
  split <;> simp_all
  split <;> simp_all

theorem insert_origin {up η a x i y} (h : lookup (insert up η a x) i = some y) :
    y = x ∨ lookup a i = some y := by
  unfold insert at h
  dsimp only at h
  split at h <;> rw [lookup_set] at h
  · split at h
    · split at h <;> simp_all
    · exact Or.inr h
  · rename_i old hold
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        rcases better_mem up x old with he | he
        · left; rw [he] at h; exact h.symm
        · right; rw [he] at h; subst y; simp_all
      · simp_all
    · exact Or.inr h

/-- Every old representative is replaced only by an at-least-as-good one. -/
theorem insert_dominates {up η a x i y} (h : lookup a i = some y) :
    ∃ z, lookup (insert up η a x) i = some z ∧ Before up y.value z.value := by
  by_cases hb : bucket η x.value = i
  · have hi := lookup_lt h
    refine ⟨better up x y, ?_, before_better_right up x y⟩
    simp [insert, hb, h, lookup_set, hi]
  · refine ⟨y, ?_, before_refl up y.value⟩
    unfold insert
    dsimp only
    split <;> simp [lookup_set, hb, h]

theorem insert_contains {up η a x} (hi : bucket η x.value < a.size) :
    ∃ z, lookup (insert up η a x) (bucket η x.value) = some z ∧
      Before up x.value z.value := by
  unfold insert
  dsimp only
  split
  · exact ⟨x, by simp [lookup_set, hi], before_refl up x.value⟩
  · rename_i y hy
    exact ⟨better up x y, by simp [lookup_set, hi], before_better_left up x y⟩

/-- Fold over the actual candidates, with one array update per candidate. -/
def fill (up : Bool) (η : ℚ) : Table → List State → Table
  | a, [] => a
  | a, x :: xs => fill up η (insert up η a x) xs

@[simp] theorem size_fill (up η a xs) : (fill up η a xs).size = a.size := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [fill, ih]

theorem fill_origin {up η a xs i y} (h : lookup (fill up η a xs) i = some y) :
    y ∈ xs ∨ ∃ j, lookup a j = some y := by
  induction xs generalizing a with
  | nil => exact Or.inr ⟨i, h⟩
  | cons x xs ih =>
    rcases ih h with hy | ⟨j, hj⟩
    · exact Or.inl (by simp [hy])
    · rcases insert_origin hj with he | he
      · exact Or.inl (by simp [he])
      · exact Or.inr ⟨j, he⟩

theorem fill_dominates {up η a xs i y} (h : lookup a i = some y) :
    ∃ z, lookup (fill up η a xs) i = some z ∧ Before up y.value z.value := by
  induction xs generalizing a y with
  | nil => exact ⟨y, h, before_refl up y.value⟩
  | cons x xs ih =>
    obtain ⟨z, hz, hyz⟩ := insert_dominates (x := x) (up := up) (η := η) h
    obtain ⟨w, hw, hzw⟩ := ih hz
    exact ⟨w, hw, before_trans hyz hzw⟩

theorem fill_contains {up η a xs x} (hx : x ∈ xs)
    (hi : bucket η x.value < a.size) :
    ∃ z, lookup (fill up η a xs) (bucket η x.value) = some z ∧
      Before up x.value z.value := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨z, hz, hxz⟩ := insert_contains (up := up) (η := η) hi
      obtain ⟨w, hw, hzw⟩ := fill_dominates (xs := ys) hz
      exact ⟨w, hw, before_trans hxz hzw⟩
    · exact ih hx (by simpa using hi)

def trim (up : Bool) (η T : ℚ) (xs : List State) : Table :=
  fill up η (Array.replicate (buckets η T) none) xs

@[simp] theorem size_trim (up η T xs) : (trim up η T xs).size = buckets η T := by
  simp [trim]

theorem trim_origin {up η T xs i y} (h : lookup (trim up η T xs) i = some y) :
    y ∈ xs := by
  rcases fill_origin h with h | ⟨j, hj⟩
  · exact h
  · simp only [lookup, Array.getElem?_replicate] at hj
    split at hj <;> simp_all

def Bucketed (η : ℚ) (a : Table) : Prop :=
  ∀ i x, lookup a i = some x → bucket η x.value = i

theorem insert_bucketed {up η a x} (ha : Bucketed η a) :
    Bucketed η (insert up η a x) := by
  intro i y hy
  unfold insert at hy
  dsimp only at hy
  split at hy <;> rw [lookup_set] at hy
  · split at hy
    · split at hy <;> simp_all
    · exact ha i y hy
  · rename_i z hz
    split at hy
    · rename_i hi
      split at hy
      · simp only [Option.some.injEq] at hy
        rcases better_mem up x z with he | he
        · rw [he] at hy; subst y; exact hi
        · rw [he] at hy; subst y; exact (ha _ _ hz).trans hi
      · simp_all
    · exact ha i y hy

theorem fill_bucketed {up η a xs} (ha : Bucketed η a) :
    Bucketed η (fill up η a xs) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih => exact ih (insert_bucketed ha)

theorem trim_bucketed (up η T xs) : Bucketed η (trim up η T xs) := by
  apply fill_bucketed
  intro i x hx
  simp only [lookup, Array.getElem?_replicate] at hx
  split at hx <;> simp_all

/-- One-step trimming error, with a real candidate witness retained. -/
theorem trim_approximates {up η T xs x} (hη : 0 < η)
    (hn : ∀ y ∈ xs, 0 ≤ y.value) (hx : x ∈ xs) (hT : x.value ≤ T) :
    ∃ y, y ∈ entries (trim up η T xs) ∧ y ∈ xs ∧
      Before up x.value y.value ∧ x.value - η ≤ y.value ∧ y.value ≤ x.value + η := by
  obtain ⟨y, hy, hp⟩ := fill_contains (up := up) (η := η)
    (a := Array.replicate (buckets η T) none) hx (by simpa using bucket_lt hη hT)
  have hyo := trim_origin (show lookup (trim up η T xs) _ = some y from hy)
  have hb := trim_bucketed up η T xs _ _ hy
  have hclose := same_bucket_close hη (hn x hx) (hn y hyo) hb.symm
  exact ⟨y, mem_entries.2 ⟨_, hy⟩, hyo, hp, by linarith [hclose.1], hclose.2.le⟩

def candidates (c : ℚ) (a : Table) : List State :=
  (entries a).flatMap (fun x => [skip x, take c x])

@[simp] theorem mem_candidates {c a y} :
    y ∈ candidates c a ↔ ∃ x ∈ entries a, y = skip x ∨ y = take c x := by
  simp [candidates, eq_comm]

/-- The processed sequence is read right-to-left; decision bits stay in input order.
All tables have the same global bucket-array length. -/
def run (up : Bool) (η T : ℚ) : List ℚ → Table
  | [] => trim up η T [zero]
  | c :: cs => trim up η T (candidates c (run up η T cs))

@[simp] theorem size_run (up η T cs) : (run up η T cs).size = buckets η T := by
  cases cs <;> simp [run]

/-- No rounded or fictitious sum is ever stored. -/
theorem run_sound {up η T cs y} (hy : y ∈ entries (run up η T cs)) :
    Witness cs y := by
  induction cs generalizing y with
  | nil =>
    obtain ⟨i, hi⟩ := mem_entries.1 hy
    have := trim_origin hi
    simp only [List.mem_singleton] at this
    subst y
    exact Witness.nil
  | cons c cs ih =>
    obtain ⟨i, hi⟩ := mem_entries.1 hy
    have hcan := trim_origin hi
    obtain ⟨x, hx, he | he⟩ := mem_candidates.1 hcan
    · subst y; exact Witness.skip (ih hx)
    · subst y; exact Witness.take (ih hx)

theorem zero_mem_run_nil (up η T) : zero ∈ entries (run up η T []) := by
  have hi : bucket η zero.value < (Array.replicate (buckets η T) none : Table).size := by
    simp [zero, bucket, buckets]
  obtain ⟨y, hy, _⟩ := fill_contains (up := up) (η := η)
    (a := Array.replicate (buckets η T) none) (xs := [zero]) (by simp) hi
  have he := trim_origin (show lookup (trim up η T [zero]) _ = some y from hy)
  simp only [List.mem_singleton] at he
  subst y
  exact mem_entries.2 ⟨_, hy⟩

/-- Lemma 5.2, simultaneously covering both directions and every layer. -/
theorem run_approximates {up η T cs x} (hη : 0 < η)
    (hn : ∀ c ∈ cs, 0 ≤ c) (hT : cs.sum ≤ T) (hx : Witness cs x) :
    ∃ y, y ∈ entries (run up η T cs) ∧ Before up x.value y.value ∧
      x.value - (cs.length : ℚ) * η ≤ y.value ∧
      y.value ≤ x.value + (cs.length : ℚ) * η := by
  induction hx with
  | nil => exact ⟨zero, zero_mem_run_nil up η T, before_refl up 0, by simp [zero]⟩
  | @skip c cs x hx ih =>
    have hc := hn c (by simp)
    have hcs : ∀ d ∈ cs, 0 ≤ d := fun d hd => hn d (by simp [hd])
    have hcsT : cs.sum ≤ T := by simp only [List.sum_cons] at hT; linarith
    obtain ⟨y, hy, hxy, hlo, hhi⟩ := ih hcs hcsT
    have hw : Witness (c :: cs) (skip y) := Witness.skip (run_sound hy)
    have hm : skip y ∈ candidates c (run up η T cs) :=
      mem_candidates.2 ⟨y, hy, Or.inl rfl⟩
    have hnon : ∀ z ∈ candidates c (run up η T cs), 0 ≤ z.value := by
      intro z hz
      obtain ⟨v, hv, rfl | rfl⟩ := mem_candidates.1 hz
      · exact (witness_bounds hn (Witness.skip (run_sound hv))).1
      · exact (witness_bounds hn (Witness.take (run_sound hv))).1
    obtain ⟨z, hz, _, hyz, hzl, hzu⟩ := trim_approximates hη hnon hm
      ((witness_bounds hn hw).2.trans hT)
    refine ⟨z, hz, ?_, ?_, ?_⟩
    · exact before_trans hxy hyz
    · simp only [skip, List.length_cons, Nat.cast_add, Nat.cast_one] at *; nlinarith
    · simp only [skip, List.length_cons, Nat.cast_add, Nat.cast_one] at *; nlinarith
  | @take c cs x hx ih =>
    have hc := hn c (by simp)
    have hcs : ∀ d ∈ cs, 0 ≤ d := fun d hd => hn d (by simp [hd])
    have hcsT : cs.sum ≤ T := by simp only [List.sum_cons] at hT; linarith
    obtain ⟨y, hy, hxy, hlo, hhi⟩ := ih hcs hcsT
    have hw : Witness (c :: cs) (take c y) := Witness.take (run_sound hy)
    have hm : take c y ∈ candidates c (run up η T cs) :=
      mem_candidates.2 ⟨y, hy, Or.inr rfl⟩
    have hnon : ∀ z ∈ candidates c (run up η T cs), 0 ≤ z.value := by
      intro z hz
      obtain ⟨v, hv, rfl | rfl⟩ := mem_candidates.1 hz
      · exact (witness_bounds hn (Witness.skip (run_sound hv))).1
      · exact (witness_bounds hn (Witness.take (run_sound hv))).1
    obtain ⟨z, hz, _, hyz, hzl, hzu⟩ := trim_approximates hη hnon hm
      ((witness_bounds hn hw).2.trans hT)
    refine ⟨z, hz, ?_, ?_, ?_⟩
    · apply before_trans (b := (take c y).value) _ hyz
      cases up <;> simp_all [Before, take]
    · simp only [take, List.length_cons, Nat.cast_add, Nat.cast_one] at *; nlinarith
    · simp only [take, List.length_cons, Nat.cast_add, Nat.cast_one] at *; nlinarith

/-- Lemma 5.3. Feasibility is an input to this generic numerical component;
the Hill-share application must prove that input independently. -/
theorem final_hit {cs : List ℚ} {L U : ℚ}
    (hs : 0 < cs.length) (hW : L < U) (hn : ∀ c ∈ cs, 0 ≤ c)
    (hfeas : ∃ x, Witness cs x ∧ L ≤ x.value ∧ x.value ≤ U) :
    let η := (U - L) / (2 * (cs.length : ℚ))
    ∃ y, (y ∈ entries (run true η cs.sum cs) ∨
      y ∈ entries (run false η cs.sum cs)) ∧ Witness cs y ∧
      L ≤ y.value ∧ y.value ≤ U := by
  dsimp only
  let η := (U - L) / (2 * (cs.length : ℚ))
  have hsQ : (0 : ℚ) < cs.length := by exact_mod_cast hs
  have hη : 0 < η := div_pos (sub_pos.2 hW) (by positivity)
  have herror : (cs.length : ℚ) * η = (U - L) / 2 := by
    dsimp [η]; field_simp; ring
  obtain ⟨x, hx, hxL, hxU⟩ := hfeas
  by_cases hm : x.value ≤ (L + U) / 2
  · obtain ⟨y, hy, hxy, _, he⟩ := run_approximates (up := true) hη hn le_rfl hx
    have hxy' : x.value ≤ y.value := by simpa [Before] using hxy
    rw [herror] at he
    exact ⟨y, Or.inl hy, run_sound hy, by linarith, by linarith⟩
  · obtain ⟨y, hy, hxy, he, _⟩ := run_approximates (up := false) hη hn le_rfl hx
    have hxy' : y.value ≤ x.value := by simpa [Before] using hxy
    rw [herror] at he
    exact ⟨y, Or.inr hy, run_sound hy, by linarith, by linarith⟩

def solve (cs : List ℚ) (L U : ℚ) : Option State :=
  let η := (U - L) / (2 * (cs.length : ℚ))
  (entries (run true η cs.sum cs) ++ entries (run false η cs.sum cs)).find?
    (fun y => decide (L ≤ y.value ∧ y.value ≤ U))

end ExactHillShares.Trimmed


namespace ExactHillShares.Trimmed

/-- A table has at most one occupied state per physical array cell. -/
theorem entries_length_le (a : Table) : (entries a).length ≤ a.size := by
  exact (List.length_filterMap_le id a.toList).trans_eq (Array.length_toList (xs := a))

@[simp] theorem candidates_length (c : ℚ) (a : Table) :
    (candidates c a).length = 2 * (entries a).length := by
  unfold candidates
  induction entries a with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

/-- The explicit charged array machine allocates the fresh table, scans the old
array, creates two linked witness nodes per old state, and performs at most thirty-two
unit operations per candidate (rational addition/division/floor/comparison,
array read/write and fixed-size record/bit allocation). These counters are
computed from the actual arrays and actual candidate lists of `run`. -/
def runOps (up : Bool) (η T : ℚ) : List ℚ → ℕ
  | [] => buckets η T + 32
  | c :: cs => runOps up η T cs + buckets η T + (run up η T cs).size +
      32 * (candidates c (run up η T cs)).length + 1

/-- Two words (predecessor pointer and include/exclude bit) are allocated for
each generated candidate. Sharing keeps predecessor traversal linear. -/
def predecessorWords (up : Bool) (η T : ℚ) : List ℚ → ℕ
  | [] => 0
  | c :: cs => predecessorWords up η T cs +
      2 * (candidates c (run up η T cs)).length

/-- Old and fresh arrays plus the concrete, untrimmed candidate list. -/
def rollingStates (up : Bool) (η T c : ℚ) (cs : List ℚ) : ℕ :=
  (run up η T cs).size + buckets η T + (candidates c (run up η T cs)).length

theorem runOps_bound (up η T cs) :
    runOps up η T cs ≤ 67 * (cs.length + 1) * buckets η T := by
  have hB : 1 ≤ buckets η T := by unfold buckets; omega
  induction cs with
  | nil => simp [runOps]; omega
  | cons c cs ih =>
    have he := entries_length_le (run up η T cs)
    simp only [size_run] at he
    simp only [runOps, size_run, candidates_length, List.length_cons]
    nlinarith

theorem predecessorWords_bound (up η T cs) :
    predecessorWords up η T cs ≤ 4 * cs.length * buckets η T := by
  induction cs with
  | nil => simp [predecessorWords]
  | cons c cs ih =>
    have he := entries_length_le (run up η T cs)
    simp only [size_run] at he
    simp only [predecessorWords, candidates_length, List.length_cons]
    nlinarith

theorem rollingStates_bound (up η T c cs) :
    rollingStates up η T c cs ≤ 4 * buckets η T := by
  have he := entries_length_le (run up η T cs)
  simp only [size_run] at he
  simp only [rollingStates, size_run, candidates_length]
  omega

/-- The paper's denominator-independent bucket estimate, conservatively rounded
to the integral polynomial `5*s^2+1`. -/
theorem polynomial_bucket_bound {s : ℕ} {T W : ℚ}
    (hs : 0 < s) (_hT : 0 ≤ T) (hW : 0 < W)
    (hw : 3 * T ≤ 7 * (s : ℚ) * W) :
    buckets (W / (2 * (s : ℚ))) T ≤ 5 * s^2 + 1 := by
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hη : 0 < W / (2 * (s : ℚ)) := div_pos hW (by positivity)
  have hquot : T / (W / (2 * (s : ℚ))) ≤ ((5 * s^2 : ℕ) : ℚ) := by
    apply (div_le_iff₀ hη).2
    have hscale : 3 * T * (2 * (s : ℚ)) ≤
        7 * (s : ℚ) * W * (2 * (s : ℚ)) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    have hnon : 0 ≤ (s : ℚ)^2 * W := by positivity
    push_cast
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 * s)).2
    nlinarith
  unfold buckets bucket
  exact Nat.add_le_add_right (Nat.floor_le_of_le hquot) 1

/-- Proposition 5.4 in the explicit rational+floor array model, for one run.
The two directions multiply all bounds by at most two. -/
theorem polynomial_complexity {cs : List ℚ} {W : ℚ}
    (hs : 0 < cs.length) (hn : ∀ c ∈ cs, 0 ≤ c) (hW : 0 < W)
    (hw : 3 * cs.sum ≤ 7 * (cs.length : ℚ) * W) (up : Bool) :
    let η := W / (2 * (cs.length : ℚ))
    (run up η cs.sum cs).size ≤ 5 * cs.length^2 + 1 ∧
    runOps up η cs.sum cs ≤ 67 * (cs.length + 1) * (5 * cs.length^2 + 1) ∧
    predecessorWords up η cs.sum cs ≤ 4 * cs.length * (5 * cs.length^2 + 1) := by
  dsimp only
  have hT : 0 ≤ cs.sum := List.sum_nonneg hn
  have hb := polynomial_bucket_bound hs hT hW hw
  refine ⟨by simpa using hb, ?_, ?_⟩
  · exact (runOps_bound _ _ _ _).trans (Nat.mul_le_mul_left _ hb)
  · exact (predecessorWords_bound _ _ _ _).trans (Nat.mul_le_mul_left _ hb)

end ExactHillShares.Trimmed

namespace ExactHillShares.Trimmed

/-- Every Boolean subset description has its exact rational witness. -/
theorem witness_of_bits {cs : List ℚ} {bs : List Bool}
    (hlen : bs.length = cs.length) : Witness cs ⟨selectedSum cs bs, bs⟩ := by
  induction cs generalizing bs with
  | nil =>
    have hb : bs = [] := List.length_eq_zero_iff.1 hlen
    subst bs
    exact Witness.nil
  | cons c cs ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hh : bs.length = cs.length := by simpa using hlen
      have hw := ih hh
      cases b
      · simpa [selectedSum, skip] using (Witness.skip (c := c) hw)
      · simpa [selectedSum, take, add_comm] using (Witness.take (c := c) hw)

/-- Complement bits reconstruct the other bundle exactly, including zero items. -/
theorem complement_sum {cs : List ℚ} {bs : List Bool}
    (hlen : bs.length = cs.length) :
    selectedSum cs bs + selectedSum cs (bs.map Bool.not) = cs.sum := by
  induction cs generalizing bs with
  | nil => simp [selectedSum]
  | cons c cs ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hh : bs.length = cs.length := by simpa using hlen
      have hrec := ih hh
      cases b <;> simp [selectedSum] <;> linarith

/-- The actual executable scan succeeds and returns a verifiable subset. -/
theorem solve_correct {cs : List ℚ} {L U : ℚ}
    (hs : 0 < cs.length) (hW : L < U) (hn : ∀ c ∈ cs, 0 ≤ c)
    (hfeas : ∃ x, Witness cs x ∧ L ≤ x.value ∧ x.value ≤ U) :
    ∃ y, solve cs L U = some y ∧ Witness cs y ∧ L ≤ y.value ∧ y.value ≤ U := by
  have hf := final_hit hs hW hn hfeas
  dsimp only at hf
  cases he : solve cs L U with
  | none =>
    unfold solve at he
    have hnone := List.find?_eq_none.1 he
    obtain ⟨y, hy, _, hlo, hhi⟩ := hf
    have hm : y ∈ entries (run true ((U - L) / (2 * (cs.length : ℚ))) cs.sum cs) ++
        entries (run false ((U - L) / (2 * (cs.length : ℚ))) cs.sum cs) :=
      List.mem_append.2 hy
    have hc := hnone y hm
    simp [hlo, hhi] at hc
  | some y =>
    refine ⟨y, rfl, ?_, ?_⟩
    · have hm := List.mem_of_find?_eq_some (show _ = some y from he)
      rcases List.mem_append.1 hm with hm | hm <;> exact run_sound hm
    · have hp := List.find?_some (show _ = some y from he)
      simpa using hp

/-- The produced Boolean mask and its complement satisfy the two-bin limit. -/
theorem solve_two_bin {cs : List ℚ} {D : ℚ}
    (hs : 0 < cs.length) (hW : cs.sum < 2 * D) (hn : ∀ c ∈ cs, 0 ≤ c)
    (hfeas : ∃ x, Witness cs x ∧ cs.sum - D ≤ x.value ∧ x.value ≤ D) :
    ∃ y, solve cs (cs.sum - D) D = some y ∧ y.bits.length = cs.length ∧
      selectedSum cs y.bits ≤ D ∧ selectedSum cs (y.bits.map Bool.not) ≤ D := by
  obtain ⟨y, hy, hw, hlo, hhi⟩ := solve_correct hs (by linarith) hn hfeas
  obtain ⟨hlen, hval⟩ := witness_decodes hw
  have hcomp := complement_sum hlen
  exact ⟨y, hy, hlen, by linarith, by linarith⟩

end ExactHillShares.Trimmed

namespace ExactHillShares.Trimmed

/-- Bucket equality cannot hide two different retained witnesses. -/
theorem trim_unique_bucket {up η T xs x y}
    (hx : x ∈ entries (trim up η T xs)) (hy : y ∈ entries (trim up η T xs))
    (hb : bucket η x.value = bucket η y.value) : x = y := by
  obtain ⟨i, hi⟩ := mem_entries.1 hx
  obtain ⟨j, hj⟩ := mem_entries.1 hy
  have hxi := trim_bucketed up η T xs i x hi
  have hyj := trim_bucketed up η T xs j y hj
  have hij : i = j := hxi.symm.trans (hb.trans hyj)
  rw [← hij] at hj
  rw [hi] at hj
  exact Option.some.inj hj

/-- Entire two-direction routine, including total-cost preprocessing, scanning
both final arrays and linear predecessor reconstruction. -/
def solveOps (cs : List ℚ) (L U : ℚ) : ℕ :=
  let η := (U - L) / (2 * (cs.length : ℚ))
  runOps true η cs.sum cs + runOps false η cs.sum cs +
    6 * buckets η cs.sum + 2 * cs.length + 10

/-- An explicit cubic operation bound for the executable two-direction scan. -/
theorem solveOps_cubic {cs : List ℚ} {L U : ℚ}
    (hs : 0 < cs.length) (hn : ∀ c ∈ cs, 0 ≤ c) (hW : L < U)
    (hw : 3 * cs.sum ≤ 7 * (cs.length : ℚ) * (U - L)) :
    solveOps cs L U ≤ 2000 * cs.length^3 := by
  let s := cs.length
  let B := buckets ((U - L) / (2 * (cs.length : ℚ))) cs.sum
  have hs1 : 1 ≤ s := hs
  have hs2 : 1 ≤ s^2 := by nlinarith
  have hs3 : 1 ≤ s^3 := by nlinarith
  have hss : s ≤ s^3 := by nlinarith [sq_nonneg (s : ℤ)]
  have hb : B ≤ 5 * s^2 + 1 :=
    polynomial_bucket_bound hs (List.sum_nonneg hn) (sub_pos.2 hW) hw
  have hB : B ≤ 6 * s^2 := by omega
  have hlen : s + 1 ≤ 2 * s := by omega
  have ht := runOps_bound true ((U - L) / (2 * (cs.length : ℚ))) cs.sum cs
  have hf := runOps_bound false ((U - L) / (2 * (cs.length : ℚ))) cs.sum cs
  change _ ≤ 67 * (s + 1) * B at ht hf
  have hprod : (s + 1) * B ≤ 12 * s^3 := by
    calc
      (s + 1) * B ≤ (2 * s) * (6 * s^2) := Nat.mul_le_mul hlen hB
      _ = 12 * s^3 := by ring
  unfold solveOps
  change _ + _ + 6 * B + 2 * s + 10 ≤ 2000 * s^3
  nlinarith

end ExactHillShares.Trimmed

namespace ExactHillShares.Trimmed
open scoped BigOperators

/-- Bridge from finite-index valuations to the executable list representation. -/
theorem selectedSum_ofFn {m : ℕ} (c : Fin m → ℚ) (b : Fin m → Bool) :
    selectedSum (List.ofFn c) (List.ofFn b) = ∑ j, if b j then c j else 0 := by
  induction m with
  | zero => simp [selectedSum]
  | succ m ih =>
    simp only [List.ofFn_succ, selectedSum, Fin.sum_univ_succ]
    rw [ih]

/-- A finite partition supplies the feasible-witness premise without any search
through the exponential family of subsets in the algorithm itself. -/
theorem finite_feasible_witness {m : ℕ} {c : Fin m → ℚ} {L U : ℚ}
    (hf : ∃ b : Fin m → Bool,
      L ≤ (∑ j, if b j then c j else 0) ∧ (∑ j, if b j then c j else 0) ≤ U) :
    ∃ x, Witness (List.ofFn c) x ∧ L ≤ x.value ∧ x.value ≤ U := by
  obtain ⟨b, hlo, hhi⟩ := hf
  refine ⟨⟨selectedSum (List.ofFn c) (List.ofFn b), List.ofFn b⟩,
    witness_of_bits (by simp), ?_, ?_⟩
  · simpa [selectedSum_ofFn] using hlo
  · simpa [selectedSum_ofFn] using hhi

/-- Direct finite-valuation interface for the constructive terminal component. -/
theorem finite_solve_correct {m : ℕ} {c : Fin m → ℚ} {L U : ℚ}
    (hm : 0 < m) (hW : L < U) (hn : ∀ j, 0 ≤ c j)
    (hf : ∃ b : Fin m → Bool,
      L ≤ (∑ j, if b j then c j else 0) ∧ (∑ j, if b j then c j else 0) ≤ U) :
    ∃ y, solve (List.ofFn c) L U = some y ∧ Witness (List.ofFn c) y ∧
      L ≤ y.value ∧ y.value ≤ U := by
  apply solve_correct (by simpa using hm) hW
  · intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
    exact hn j
  · exact finite_feasible_witness hf

end ExactHillShares.Trimmed

namespace ExactHillShares.Trimmed

/-- The actual retained witness is the extremum of its occupied candidate bucket. -/
theorem trim_extremal {up η T xs x y}
    (hη : 0 < η) (hx : x ∈ xs) (hxT : x.value ≤ T)
    (hy : y ∈ entries (trim up η T xs))
    (hb : bucket η x.value = bucket η y.value) : Before up x.value y.value := by
  obtain ⟨i, hi⟩ := mem_entries.1 hy
  have hiy := trim_bucketed up η T xs i y hi
  obtain ⟨z, hz, hp⟩ := fill_contains (up := up) (η := η)
    (a := Array.replicate (buckets η T) none) hx (by simpa using bucket_lt hη hxT)
  have hxbi : bucket η x.value = i := hb.trans hiy
  change lookup (trim up η T xs) (bucket η x.value) = some z at hz
  rw [hxbi, hi] at hz
  have hyz : y = z := Option.some.inj hz
  simpa [hyz] using hp

/-- Two directions need at most five bucket arrays' worth of rolling states:
one completed table and one run's old/fresh/candidate workspace. Predecessor
storage is counted separately. -/
theorem two_run_memory {cs : List ℚ} {W : ℚ}
    (hs : 0 < cs.length) (hn : ∀ c ∈ cs, 0 ≤ c) (hW : 0 < W)
    (hw : 3 * cs.sum ≤ 7 * (cs.length : ℚ) * W) :
    let η := W / (2 * (cs.length : ℚ))
    5 * buckets η cs.sum ≤ 30 * cs.length^2 ∧
    predecessorWords true η cs.sum cs + predecessorWords false η cs.sum cs ≤
      48 * cs.length^3 := by
  dsimp only
  let s := cs.length
  let B := buckets (W / (2 * (cs.length : ℚ))) cs.sum
  have hs1 : 1 ≤ s := hs
  have hs2 : 1 ≤ s^2 := by nlinarith
  have hb : B ≤ 5 * s^2 + 1 :=
    polynomial_bucket_bound hs (List.sum_nonneg hn) hW hw
  have hB : B ≤ 6 * s^2 := by omega
  have ht := predecessorWords_bound true (W / (2 * (cs.length : ℚ))) cs.sum cs
  have hf := predecessorWords_bound false (W / (2 * (cs.length : ℚ))) cs.sum cs
  change _ ≤ 4 * s * B at ht hf
  have hprod : s * B ≤ 6 * s^3 := by
    calc
      s * B ≤ s * (6 * s^2) := Nat.mul_le_mul_left _ hB
      _ = 6 * s^3 := by ring
  constructor <;> change _ ≤ _
  · change 5 * B ≤ 30 * s^2
    omega
  · change _ + _ ≤ 48 * s^3
    nlinarith

end ExactHillShares.Trimmed

namespace ExactHillShares.Trimmed

/-- Peak non-predecessor live cells in a run, following the actual recursive
execution: the recursive call returns before its old/new/candidate step starts. -/
def runPeak (up : Bool) (η T : ℚ) : List ℚ → ℕ
  | [] => buckets η T + 1
  | c :: cs => max (runPeak up η T cs) (rollingStates up η T c cs)

/-- Peak states when MAX is completed first, its final table retained while MIN
runs, and the two actual lists of retained entries are scanned. -/
def solvePeak (cs : List ℚ) (L U : ℚ) : ℕ :=
  let η := (U - L) / (2 * (cs.length : ℚ))
  let a := run true η cs.sum cs
  let b := run false η cs.sum cs
  max (runPeak true η cs.sum cs)
    (max (a.size + runPeak false η cs.sum cs)
      (a.size + b.size + (entries a).length + (entries b).length))

theorem runPeak_bound (up η T cs) : runPeak up η T cs ≤ 4 * buckets η T := by
  have hB : 1 ≤ buckets η T := by unfold buckets; omega
  induction cs with
  | nil => simp [runPeak]; omega
  | cons c cs ih =>
    exact max_le ih (rollingStates_bound up η T c cs)

theorem solvePeak_bound (cs L U) :
    solvePeak cs L U ≤ 5 * buckets ((U - L) / (2 * (cs.length : ℚ))) cs.sum := by
  unfold solvePeak
  dsimp only
  have ht := runPeak_bound true ((U - L) / (2 * (cs.length : ℚ))) cs.sum cs
  have hf := runPeak_bound false ((U - L) / (2 * (cs.length : ℚ))) cs.sum cs
  have hat := entries_length_le (run true ((U - L) / (2 * (cs.length : ℚ))) cs.sum cs)
  have haf := entries_length_le (run false ((U - L) / (2 * (cs.length : ℚ))) cs.sum cs)
  simp only [size_run] at *
  omega

theorem solvePeak_quadratic {cs : List ℚ} {L U : ℚ}
    (hs : 0 < cs.length) (hn : ∀ c ∈ cs, 0 ≤ c) (hW : L < U)
    (hw : 3 * cs.sum ≤ 7 * (cs.length : ℚ) * (U - L)) :
    solvePeak cs L U ≤ 30 * cs.length^2 := by
  exact (solvePeak_bound cs L U).trans
    (two_run_memory hs hn (sub_pos.2 hW) hw).1

end ExactHillShares.Trimmed

namespace ExactHillShares.Trimmed

/-- The sharper rational coefficient displayed in Proposition 5.4. -/
theorem paper_bucket_bound {s : ℕ} {T W : ℚ}
    (hs : 0 < s) (hT : 0 ≤ T) (hW : 0 < W)
    (hw : 3 * T ≤ 7 * (s : ℚ) * W) :
    (buckets (W / (2 * (s : ℚ))) T : ℚ) ≤ (14 / 3) * (s : ℚ)^2 + 1 := by
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hη : 0 < W / (2 * (s : ℚ)) := div_pos hW (by positivity)
  have hdiv : T / (W / (2 * (s : ℚ))) = (2 * (s : ℚ) * T) / W := by
    field_simp
    ring
  have hscale := mul_le_mul_of_nonneg_left hw hsQ.le
  have hquot : T / (W / (2 * (s : ℚ))) ≤ (14 / 3) * (s : ℚ)^2 := by
    rw [hdiv]
    apply (div_le_iff₀ hW).2
    nlinarith
  have hfloor := Nat.floor_le (div_nonneg hT hη.le)
  unfold buckets bucket
  push_cast
  linarith

end ExactHillShares.Trimmed
