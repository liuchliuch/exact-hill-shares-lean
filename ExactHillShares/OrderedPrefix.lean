import Mathlib.Order.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ExactHillShares

def prefixCost (a : ℕ → ℝ) (s : ℕ) : ℝ := ∑ i ∈ Finset.range s, a i

theorem prefixCost_succ (a : ℕ → ℝ) (s : ℕ) :
    prefixCost a (s + 1) = prefixCost a s + a s := by
  exact Finset.sum_range_succ a s

theorem prefixCost_mono (a : ℕ → ℝ) (hnonneg : ∀ i, 0 ≤ a i) :
    Monotone (prefixCost a) := by
  intro s m hsm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hsm)
    (fun i hi hnot => hnonneg i)

theorem next_le_residual (a : ℕ → ℝ) (s m : ℕ)
    (hnonneg : ∀ i, 0 ≤ a i) (hsm : s < m) :
    a s ≤ prefixCost a m - prefixCost a s := by
  have h := prefixCost_mono a hnonneg (Nat.succ_le_of_lt hsm)
  rw [prefixCost_succ] at h
  linarith

theorem residual_le_count_mul_next (a : ℕ → ℝ) (s m : ℕ)
    (hanti : Antitone a) (hsm : s ≤ m) :
    prefixCost a m - prefixCost a s ≤ ((m - s : ℕ) : ℝ) * a s := by
  have heq : m = s + (m - s) := (Nat.add_sub_of_le hsm).symm
  conv_lhs => rw [heq]
  unfold prefixCost
  rw [Finset.sum_range_add]
  simp only [add_sub_cancel_left]
  calc
    ∑ i ∈ Finset.range (m - s), a (s + i) ≤ ∑ i ∈ Finset.range (m - s), a s :=
      Finset.sum_le_sum (fun i hi => hanti (Nat.le_add_right s i))
    _ = ((m - s : ℕ) : ℝ) * a s := by simp

theorem next_pos_of_residual_pos (a : ℕ → ℝ) (s m : ℕ)
    (hanti : Antitone a) (hsm : s ≤ m)
    (hres : 0 < prefixCost a m - prefixCost a s) : 0 < a s := by
  have h := residual_le_count_mul_next a s m hanti hsm
  by_contra hp
  have hmul : ((m - s : ℕ) : ℝ) * a s ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_gt hp)
  linarith

/-- Extend a finite cost row by zero without strengthening its order hypotheses. -/
noncomputable def zeroExtend {m : ℕ} (a : Fin m → ℝ) (i : ℕ) : ℝ :=
  if h : i < m then a ⟨i, h⟩ else 0

theorem zeroExtend_nonneg {m : ℕ} (a : Fin m → ℝ) (h : ∀ i, 0 ≤ a i) :
    ∀ i, 0 ≤ zeroExtend a i := by
  intro i
  unfold zeroExtend
  split_ifs <;> simp_all

theorem zeroExtend_antitone {m : ℕ} (a : Fin m → ℝ)
    (hnonneg : ∀ i, 0 ≤ a i) (hanti : Antitone a) : Antitone (zeroExtend a) := by
  intro i j hij
  unfold zeroExtend
  split_ifs with hj hi hi
  · exact hanti hij
  · omega
  · exact hnonneg _
  · exact le_refl 0

theorem prefixCost_le_count_mul_head (a : ℕ → ℝ) (s : ℕ)
    (hanti : Antitone a) : prefixCost a s ≤ (s : ℝ) * a 0 := by
  unfold prefixCost
  calc
    ∑ i ∈ Finset.range s, a i ≤ ∑ i ∈ Finset.range s, a 0 :=
      Finset.sum_le_sum fun i hi => hanti (Nat.zero_le i)
    _ = (s : ℝ) * a 0 := by simp

/-- A strict crossing beyond a bound of `(k+1)` largest items must remove
at least `k+1` items. This is the combinatorial step in Appendix A. -/
theorem crossing_removes_many (a : ℕ → ℝ) (k s : ℕ) (d : ℝ)
    (hanti : Antitone a) (h0 : 0 ≤ a 0)
    (hd : ((k : ℝ) + 1) * a 0 ≤ d)
    (hcross : d < prefixCost a (s + 1)) : k + 1 ≤ s := by
  by_contra h
  have hs : s ≤ k := by omega
  have hsreal : ((s + 1 : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hs
  have hupper := prefixCost_le_count_mul_head a (s + 1) hanti
  have hmul := mul_le_mul_of_nonneg_right hsreal h0
  linarith

/-- The removed mass contains the largest item and at least `k` other
items no smaller than the first residual item. -/
theorem crossing_removed_mass (a : ℕ → ℝ) (k s : ℕ) (d : ℝ)
    (hanti : Antitone a) (hnonneg : ∀ i, 0 ≤ a i)
    (hd : ((k : ℝ) + 1) * a 0 ≤ d)
    (hcross : d < prefixCost a (s + 1)) :
    a 0 + (k : ℝ) * a s ≤ prefixCost a s := by
  have hcount := crossing_removes_many a k s d hanti (hnonneg 0) hd hcross
  have hsub : Finset.range (k + 1) ⊆ Finset.range s := Finset.range_mono hcount
  have hmono : prefixCost a (k + 1) ≤ prefixCost a s := by
    unfold prefixCost
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi hnot => hnonneg i)
  have hsmall : ∑ i ∈ Finset.range k, a s ≤ ∑ i ∈ Finset.range k, a (i + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    apply hanti
    have hi' := Finset.mem_range.mp hi
    omega
  have hsplit : prefixCost a (k + 1) = a 0 + ∑ i ∈ Finset.range k, a (i + 1) := by
    unfold prefixCost
    rw [Finset.sum_range_succ']
    ring
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsmall
  linarith

end ExactHillShares
