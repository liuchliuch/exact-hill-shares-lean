import ExactHillShares.Foundations

namespace ExactHillShares

/-- Any injective item-to-agent assignment places at most one item in a bin. -/
theorem injective_load_le {m n : ℕ} (v : Fin m → ℝ)
    (a : Fin m → Fin n) (ha : Function.Injective a) (i : Fin n)
    (b : ℝ) (hb : 0 ≤ b) (hv : ∀ j, v j ≤ b) : load v a i ≤ b := by
  classical
  by_cases hex : ∃ j, a j = i
  · obtain ⟨j, hj⟩ := hex
    have heq : load v a i = v j := by
      unfold load
      rw [Finset.sum_eq_single j]
      · simp [hj]
      · intro k hk hkj
        have hk' : a k ≠ i := by
          intro hki
          exact hkj (ha (hki.trans hj.symm))
        simp [hk']
      · simp
    simpa [heq] using hv j
  · have heq : load v a i = 0 := by
      unfold load
      apply Finset.sum_eq_zero
      intro j hj
      have hji : a j ≠ i := by intro h; exact hex ⟨j, h⟩
      simp [hji]
    simpa [heq] using hb

/-- The additional preprocessing needed for an item-count-only arithmetic
bound: when agents outnumber items, assign each item to a distinct agent.
This assignment does not inspect any cost entry. -/
def singletonAllocation {m n : ℕ} (h : m ≤ n) : Fin m → Fin n := Fin.castLE h

theorem singletonAllocation_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (singletonAllocation h) := by
  intro x y hxy
  apply Fin.ext
  exact congrArg (fun z : Fin n => z.val) hxy

theorem singletonAllocation_safe {m n : ℕ} (h : m ≤ n)
    (v : Fin n → Fin m → ℝ) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hv : ∀ i j, v i j ≤ b i) :
    ∀ i, load (v i) (singletonAllocation h) i ≤ b i := by
  intro i
  exact injective_load_le (v i) _ (singletonAllocation_injective h) i (b i) (hb i) (hv i)

/-- The singleton preprocessing meets the genuine supremum-defined Hill
shares for every normalized row, without using a formula theorem. -/
theorem singletonAllocation_hill_safe {m n : ℕ} (h : m ≤ n) (hn : 0 < n)
    (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ)
    (hv : ∀ i, IsNormalizedExact (v i) (α i)) :
    ∀ i, load (v i) (singletonAllocation h) i ≤ hill n (α i) := by
  intro i
  have hnonneg : ∀ j, 0 ≤ v i j := fun j => ((hv i).1 j).1
  have hM := mms_le_hill hn (hv i)
  have hh : 0 ≤ hill n (α i) := (mms_nonneg hn hnonneg).trans hM
  have hj : ∀ j, v i j ≤ hill n (α i) :=
    fun j => (item_le_mms hn hnonneg j).trans hM
  exact injective_load_le (v i) _ (singletonAllocation_injective h) i _ hh hj

end ExactHillShares
