import ExactHillShares.Formula

/-! Algebraic core of Lemmas 4.3--4.4 and Corollary 4.5.  Prefix-order
facts and the semantic identification of the numerical formula are separate. -/
namespace ExactHillShares

/-- The minimum of the two crossing affine branches (Appendix A). -/
theorem envelope_minimum {n : ℕ} (hn : 0 < n) (k : ℕ) (a : ℝ) :
    (((k : ℝ) + 1) * ((k : ℝ) + 2)) /
      ((n : ℝ) * ((k : ℝ) + 1) ^ 2 + (k : ℝ) + 2) ≤
    envelope n k 1 a := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) * ((k : ℝ) + 1) ^ 2 + (k : ℝ) + 2 := by positivity
  obtain ⟨hinc, hdec⟩ := (envelope_le_iff hn).mp (le_refl (envelope n k 1 a))
  have hinc' := mul_le_mul_of_nonneg_right hinc (by positivity : 0 ≤ (k : ℝ) + 2)
  have hdec' := mul_le_mul_of_nonneg_right hdec (by positivity : 0 ≤ (k : ℝ) + 1)
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- The numerical threshold used in both appendices.  Its exact validity
condition is `(n-2)k+n-4 ≥ 0`; this covers n≥4 and n=3,k≥1. -/
theorem envelope_threshold {q k : ℕ} (hq : 0 < q)
    (hcrit : 0 ≤ ((q : ℝ) - 1) * k + (q : ℝ) - 3) (a : ℝ) :
    ((k : ℝ) + 3) ≤ envelope (q + 1) k 1 a *
      (((q : ℝ) + 1) * ((k : ℝ) + 2) + 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hD : 0 < ((q : ℝ) + 1) * ((k : ℝ) + 1) ^ 2 + (k : ℝ) + 2 := by positivity
  have hE : 0 < ((q : ℝ) + 1) * ((k : ℝ) + 2) + 1 := by positivity
  have hm := envelope_minimum (n := q + 1) (by omega) k a
  push_cast at hm
  have hm' := (div_le_iff₀ hD).mp hm
  have hcross : ((k : ℝ) + 3) *
      (((q : ℝ) + 1) * ((k : ℝ) + 1) ^ 2 + (k : ℝ) + 2) ≤
      (((k : ℝ) + 1) * ((k : ℝ) + 2)) *
      (((q : ℝ) + 1) * ((k : ℝ) + 2) + 1) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hm' (le_of_lt hE)
  have hall : ((k : ℝ) + 3) *
      (((q : ℝ) + 1) * ((k : ℝ) + 1) ^ 2 + (k : ℝ) + 2) ≤
      (envelope (q + 1) k 1 a * (((q : ℝ) + 1) * ((k : ℝ) + 2) + 1)) *
      (((q : ℝ) + 1) * ((k : ℝ) + 1) ^ 2 + (k : ℝ) + 2) := by nlinarith
  exact (mul_le_mul_right hD).mp hall

/-- The small-next-item envelope comparison in Appendix A/B. -/
theorem tail_envelope_small {q k : ℕ} {a C p : ℝ} (hq : 0 < q)
    (hcrit : 0 ≤ ((q : ℝ) - 1) * k + (q : ℝ) - 3)
    (hcross : envelope (q + 1) k 1 a < C + p)
    (hsmall : ((k : ℝ) + 2) * p ≤ envelope (q + 1) k 1 a) :
    envelope q (k + 1) (1 - C) p ≤ envelope (q + 1) k 1 a := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hthreshold := envelope_threshold hq hcrit a
  apply (envelope_le_iff hq).mpr
  push_cast
  constructor
  · convert hsmall using 1 <;> ring
  · have hc := mul_le_mul_of_nonneg_left (le_of_lt hcross)
      (by positivity : 0 ≤ (k : ℝ) + 3)
    nlinarith

/-- The large-next-item envelope comparison, paid for by ordered prefix mass. -/
theorem tail_envelope_large {q k : ℕ} {a C p : ℝ} (hq : 0 < q)
    (hpa : p ≤ a) (hprefix : a + (k : ℝ) * p ≤ C)
    (hlarge : envelope (q + 1) k 1 a ≤ ((k : ℝ) + 2) * p) :
    envelope q k (1 - C) p ≤ envelope (q + 1) k 1 a := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  obtain ⟨hinc, hdec⟩ := (envelope_le_iff (by omega : 0 < q + 1)).mp
    (le_refl (envelope (q + 1) k 1 a))
  push_cast at hdec
  apply (envelope_le_iff hq).mpr
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left hpa (by positivity)) hinc
  · have hc := mul_le_mul_of_nonneg_left hprefix (by positivity : 0 ≤ (k : ℝ) + 2)
    have hp := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ (k : ℝ) + 1)
    nlinarith

/-- The numerical n≥4 tail-domination theorem. -/
theorem multiFormula_tail_domination {q k : ℕ} {a C p : ℝ}
    (hq : 3 ≤ q) (hp : 0 < p) (hpT : p ≤ 1 - C)
    (hpa : p ≤ a) (hprefix : a + (k : ℝ) * p ≤ C)
    (hcross : envelope (q + 1) k 1 a < C + p) :
    multiFormula q (1 - C) p ≤ envelope (q + 1) k 1 a := by
  have hq0 : 0 < q := by omega
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hcrit : 0 ≤ ((q : ℝ) - 1) * k + (q : ℝ) - 3 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (q : ℝ) - 1) hk]
  by_cases hs : ((k : ℝ) + 2) * p ≤ envelope (q + 1) k 1 a
  · exact le_trans (multiFormula_le_envelope hq0 hp hpT (k + 1))
      (tail_envelope_small hq0 hcrit hcross hs)
  · exact le_trans (multiFormula_le_envelope hq0 hp hpT k)
      (tail_envelope_large hq0 hpa hprefix (le_of_lt (lt_of_not_ge hs)))

/-- The two exceptional-index proof only needs a total/maximum mass cap.
This is an inequality for the universal two-agent formula, not a construction
of one actual tail, so it applies uniformly to every tail with these T,p. -/
theorem twoFormula_mass_cap {T p d : ℝ} (hT : 0 < T)
    (hp : 0 < p) (hpT : p ≤ T) (hpd : p ≤ d) (hmass : 2 * T ≤ 3 * d) :
    T * twoFormula (p / T) ≤ d := by
  by_cases hs : p ≤ d / 2
  · exact le_trans (twoFormula_scaled_le_average hT hp hpT) (by linarith)
  · have hpbig : d / 2 < p := lt_of_not_ge hs
    have hrange : (1 / 3 : ℝ) ≤ p / T := (le_div_iff₀ hT).mpr (by linarith)
    rw [twoFormula, if_pos hrange, mul_max_of_nonneg _ _ (le_of_lt hT)]
    have hfirst : T * (p / T) = p := by field_simp
    have hsecond : T * (1 - p / T) = T - p := by field_simp
    rw [hfirst, hsecond]
    exact max_le hpd (by linarith)

/-- The numerical three-to-two transition, including k=0 and k=1. -/
theorem twoFormula_tail_domination {k : ℕ} {a C p : ℝ}
    (hp : 0 < p) (hpT : p ≤ 1 - C)
    (hpa : p ≤ a) (hprefix : a + (k : ℝ) * p ≤ C)
    (hcross : envelope 3 k 1 a < C + p) :
    (1 - C) * twoFormula (p / (1 - C)) ≤ envelope 3 k 1 a := by
  have hT : 0 < 1 - C := lt_of_lt_of_le hp hpT
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  obtain ⟨hinc, hdec⟩ := (envelope_le_iff (by norm_num : 0 < (3 : ℕ))).mp
    (le_refl (envelope 3 k 1 a))
  rcases k with _ | k
  · norm_num at hprefix hinc hdec
    apply twoFormula_mass_cap hT hp hpT (le_trans hpa hinc)
    linarith
  · rcases k with _ | k
    · norm_num at hprefix hinc hdec
      exact le_trans (twoFormula_scaled_le_average hT hp hpT) (by linarith)
    · have hcrit : 0 ≤ ((2 : ℝ) - 1) * (k + 1 + 1 : ℕ) + (2 : ℝ) - 3 := by
        push_cast
        norm_num
        nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
      by_cases hs : (((k + 1 + 1 : ℕ) : ℝ) + 2) * p ≤ envelope 3 (k + 1 + 1) 1 a
      · exact le_trans (twoFormula_scaled_le_envelope hT hp hpT (k + 1 + 1 + 1) (by omega))
          (tail_envelope_small (q := 2) (by norm_num) hcrit hcross hs)
      · exact le_trans (twoFormula_scaled_le_envelope hT hp hpT (k + 1 + 1) (by omega))
          (tail_envelope_large (q := 2) (by norm_num) hpa hprefix (le_of_lt (lt_of_not_ge hs)))

end ExactHillShares
