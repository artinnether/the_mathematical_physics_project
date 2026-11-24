import TuringTask.Basic

namespace PeriodicPoleTask

lemma summable_gaussian_polynomial (c : ℝ) (hc : 0 < c) (m : ℕ) :
    Summable (fun n : ℕ => (n : ℝ)^m * Real.exp (-c*(n : ℝ)^2)) := by
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
  have hg := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) m hr
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hg
  intro n
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnn : (n : ℝ) ≤ (n : ℝ)^2 := by
    simpa only [pow_two] using (show (n : ℝ) ≤ (n : ℝ)*(n : ℝ) from by exact_mod_cast (Nat.le_mul_self n))
  nlinarith

lemma spectral_summable (α : ℝ) (hα : 0 < α) : Summable (spectralTerm α) := by
  have h := summable_gaussian_polynomial (1 / α) (by positivity) 1
  have hs := (summable_nat_add_iff 1).mpr h
  unfold spectralTerm
  apply hs.congr
  intro n
  simp only [Nat.cast_add, Nat.cast_one, pow_one]
  congr 1
  ring

lemma poleMass_summable (α : ℝ) (hα : 0 < α) :
    Summable (fun k : ℤ => weight α (k * Real.pi)) := by
  have h := summable_gaussian_polynomial (α * Real.pi^2) (by positivity) 0
  have hn : Summable (fun n : ℕ => weight α ((n : ℤ) * Real.pi)) := by
    convert h using 1
    ext n
    simp only [weight, pow_zero, one_mul, Int.cast_natCast, mul_pow]
    congr 1
    ring
  apply summable_int_iff_summable_nat_and_neg.mpr
  refine ⟨hn, ?_⟩
  simpa only [Int.cast_neg, neg_mul, weight_even] using hn

lemma finitePartValue_neg (α : ℝ) (hα : 0 < α) : finitePartValue α < 0 := by
  have hs := spectral_summable α hα
  have hp : 0 < ∑' n : ℕ, spectralTerm α n :=
    hs.tsum_pos (fun n => by unfold spectralTerm; positivity) 0 (by
      unfold spectralTerm
      positivity)
  unfold finitePartValue
  have hg : 0 < Real.sqrt (Real.pi / α) := by positivity
  nlinarith

end PeriodicPoleTask
