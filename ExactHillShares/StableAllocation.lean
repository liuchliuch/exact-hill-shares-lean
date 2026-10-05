import ExactHillShares.Foundations

/-!
# Exchange-stable finite allocations

A global minimum of the sum of squared bin loads exists because the space of
allocations is finite. It has the subset-exchange property used in the exact Hill
formula proof. This avoids relying on an unformalized lexicographic optimization.
-/

open scoped BigOperators

namespace ExactHillShares

noncomputable def bundleCost {m : ℕ} (v : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  ∑ x, if x ∈ S then v x else 0

lemma bundleCost_eq_sum {m : ℕ} (v : Fin m → ℝ) (S : Finset (Fin m)) :
    bundleCost v S = ∑ x ∈ S, v x := by
  classical
  simp [bundleCost]

noncomputable def exchange {m n : ℕ} (a : Fin m → Fin n) (i j : Fin n)
    (S T : Finset (Fin m)) : Fin m → Fin n :=
  fun x => if x ∈ S then j else if x ∈ T then i else a x

lemma load_exchange_first {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n)
    {i j : Fin n} (hij : i ≠ j) {S T : Finset (Fin m)}
    (hS : ∀ x ∈ S, a x = i) (hT : ∀ x ∈ T, a x = j) :
    load v (exchange a i j S T) i = load v a i - bundleCost v S + bundleCost v T := by
  classical
  simp only [load, bundleCost, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hs : x ∈ S
  · have ht : x ∉ T := by intro ht; exact hij ((hS x hs).symm.trans (hT x ht))
    simp [exchange, hs, ht, hS x hs, hij, Ne.symm hij]
  · by_cases ht : x ∈ T
    · simp [exchange, hs, ht, hT x ht, hij, Ne.symm hij]
    · simp [exchange, hs, ht]

lemma load_exchange_second {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n)
    {i j : Fin n} (hij : i ≠ j) {S T : Finset (Fin m)}
    (hS : ∀ x ∈ S, a x = i) (hT : ∀ x ∈ T, a x = j) :
    load v (exchange a i j S T) j = load v a j + bundleCost v S - bundleCost v T := by
  classical
  simp only [load, bundleCost, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hs : x ∈ S
  · have ht : x ∉ T := by intro ht; exact hij ((hS x hs).symm.trans (hT x ht))
    simp [exchange, hs, ht, hS x hs, hij]
  · by_cases ht : x ∈ T
    · simp [exchange, hs, ht, hT x ht, hij]
    · simp [exchange, hs, ht]

lemma load_exchange_other {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n)
    {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) {S T : Finset (Fin m)}
    (hS : ∀ x ∈ S, a x = i) (hT : ∀ x ∈ T, a x = j) :
    load v (exchange a i j S T) k = load v a k := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hs : x ∈ S
  · simp [exchange, hs, hS x hs, Ne.symm hki, Ne.symm hkj]
  · by_cases ht : x ∈ T
    · simp [exchange, hs, ht, hT x ht, Ne.symm hki, Ne.symm hkj]
    · simp [exchange, hs, ht]

noncomputable def energy {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n) : ℝ :=
  ∑ i, (load v a i) ^ 2

lemma energy_exchange {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n)
    {i j : Fin n} (hij : i ≠ j) {S T : Finset (Fin m)}
    (hS : ∀ x ∈ S, a x = i) (hT : ∀ x ∈ T, a x = j) :
    energy v (exchange a i j S T) - energy v a =
      2 * (bundleCost v S - bundleCost v T) *
        ((bundleCost v S - bundleCost v T) - (load v a i - load v a j)) := by
  classical
  have hfirst := load_exchange_first v a hij hS hT
  have hsecond := load_exchange_second v a hij hS hT
  have hsum : energy v (exchange a i j S T) - energy v a =
      ((load v a i - bundleCost v S + bundleCost v T)^2 - (load v a i)^2) +
      ((load v a j + bundleCost v S - bundleCost v T)^2 - (load v a j)^2) := by
    unfold energy
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ k, ((load v (exchange a i j S T) k)^2 - (load v a k)^2)) =
        ∑ k : Fin n,
          ((if k = i then (load v a i - bundleCost v S + bundleCost v T)^2 - (load v a i)^2
          else 0) +
          (if k = j then (load v a j + bundleCost v S - bundleCost v T)^2 - (load v a j)^2
          else 0)) := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hki : k = i
            · subst k; simp [hfirst, hij]
            · by_cases hkj : k = j
              · subst k; simp [hsecond, Ne.symm hij]
              · simp [hki, hkj, load_exchange_other v a hki hkj hS hT]
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [hsum]
  ring

/-- The subset-exchange inequality of the prior paper's Claim 3. -/
def ExchangeStable {m n : ℕ} (v : Fin m → ℝ) (a : Fin m → Fin n) : Prop :=
  ∀ (i j : Fin n) (S T : Finset (Fin m)), i ≠ j →
    (∀ x ∈ S, a x = i) → (∀ x ∈ T, a x = j) →
    bundleCost v T < bundleCost v S →
    load v a i - load v a j ≤ bundleCost v S - bundleCost v T

lemma exists_exchangeStable {m n : ℕ} (hn : 0 < n) (v : Fin m → ℝ) :
    ∃ a : Fin m → Fin n, ExchangeStable v a := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨a, ha⟩ := (Set.range_nonempty (energy (n := n) v)).csInf_mem (Set.finite_range _)
  refine ⟨a, ?_⟩
  intro i j S T hij hS hT hst
  by_contra h
  have hgap : bundleCost v S - bundleCost v T < load v a i - load v a j := lt_of_not_ge h
  have hmin : energy v a ≤ energy v (exchange a i j S T) := by
    rw [ha]
    exact csInf_le (Set.finite_range _).bddBelow ⟨exchange a i j S T, rfl⟩
  have hnegative : 2 * (bundleCost v S - bundleCost v T) *
      ((bundleCost v S - bundleCost v T) - (load v a i - load v a j)) < 0 := by
    exact mul_neg_of_pos_of_neg (by nlinarith) (by linarith)
  rw [← energy_exchange v a hij hS hT] at hnegative
  linarith

/-- The useful contrapositive exchange form, corresponding to Claim 4. -/
lemma ExchangeStable.swap_obstruction {m n : ℕ} {v : Fin m → ℝ} {a : Fin m → Fin n}
    (ha : ExchangeStable v a) {i j : Fin n} {S T : Finset (Fin m)}
    (hij : i ≠ j) (hS : ∀ x ∈ S, a x = i) (hT : ∀ x ∈ T, a x = j)
    (hsmall : load v a j - bundleCost v T + bundleCost v S < load v a i) :
    bundleCost v S ≤ bundleCost v T := by
  by_contra h
  have hst : bundleCost v T < bundleCost v S := lt_of_not_ge h
  have := ha i j S T hij hS hT hst
  linarith

lemma ExchangeStable.item_gap {m n : ℕ} {v : Fin m → ℝ} {a : Fin m → Fin n}
    (ha : ExchangeStable v a) {x : Fin m} (hx : 0 < v x) {j : Fin n}
    (hj : a x ≠ j) : load v a (a x) - load v a j ≤ v x := by
  classical
  have h := ha (a x) j {x} ∅ hj (by simpa) (by simp)
  simp only [bundleCost, Finset.mem_singleton, Finset.sum_ite_eq', Finset.mem_univ,
    if_pos, Finset.not_mem_empty, if_false, Finset.sum_const_zero, sub_zero] at h
  exact h hx

lemma ExchangeStable.load_gap {m n : ℕ} {v : Fin m → ℝ} {a : Fin m → Fin n}
    (ha : ExchangeStable v a) {p : ℝ} (hp : 0 ≤ p) (hv : ∀ x, v x ≤ p)
    {i : Fin n} (hi : 0 < load v a i) (j : Fin n) : load v a i - load v a j ≤ p := by
  classical
  by_cases hij : i = j
  · subst j; simpa using hp
  have hex : ∃ x, a x = i ∧ 0 < v x := by
    by_contra! h
    have hle : load v a i ≤ 0 := by
      apply Finset.sum_nonpos
      intro x _
      split_ifs with hxi
      · exact h x hxi
      · exact le_rfl
    linarith
  obtain ⟨x, hxi, hx⟩ := hex
  have hgap := ha.item_gap hx (hxi.trans_ne hij)
  rw [hxi] at hgap
  exact hgap.trans (hv x)

/-- A finite balancing bound, proved by actual allocation existence. -/
lemma mms_le_balancing_bound {m n : ℕ} (hn : 0 < n) {v : Fin m → ℝ}
    {p : ℝ} (hp : 0 ≤ p) (hv : ∀ j, 0 ≤ v j ∧ v j ≤ p) :
    mms n v ≤ ((∑ j, v j) + ((n : ℝ) - 1) * p) / n := by
  classical
  obtain ⟨a, ha⟩ := exists_exchangeStable hn v
  apply (mms_le_iff hn v _).2
  refine ⟨a, ?_⟩
  intro i
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hi : 0 < load v a i
  · have hb : ∀ j, load v a i - p + (if j = i then p else 0) ≤ load v a j := by
      intro j
      by_cases hji : j = i
      · subst j; simp
      · have h := ha.load_gap hp (fun x => (hv x).2) hi j
        simp only [if_neg hji]
        linarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
    rw [sum_load] at hsum
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_pos] at hsum
    apply (le_div_iff₀ hnr).2
    nlinarith
  · have ht : 0 ≤ ∑ j, v j := Finset.sum_nonneg (fun j _ => (hv j).1)
    have hh : 0 ≤ ((∑ j, v j) + ((n : ℝ) - 1) * p) / n :=
      div_nonneg (add_nonneg ht (mul_nonneg (sub_nonneg.mpr hn1) hp)) (le_of_lt hnr)
    exact (le_of_not_gt hi).trans hh

lemma mms_two_le_half {m : ℕ} {v : Fin m → ℝ} {p : ℝ}
    (hp : 0 ≤ p) (hv : ∀ j, 0 ≤ v j ∧ v j ≤ p) :
    mms 2 v ≤ ((∑ j, v j) + p) / 2 := by
  convert mms_le_balancing_bound (n := 2) (by decide) hp hv using 1 <;> norm_num

end ExactHillShares
