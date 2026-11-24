import TuringTask.AbelIntegral
import Mathlib.Analysis.Complex.Trigonometric

set_option maxHeartbeats 800000
open MeasureTheory
namespace PeriodicPoleTask

noncomputable def phase (q θ : ℝ) : ℂ := (q : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

lemma norm_phase (q θ : ℝ) : ‖phase q θ‖ = |q| := by
  simp [phase, norm_mul, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs]

lemma phase_pow_re (q θ : ℝ) (n : ℕ) :
    (phase q θ ^ n).re = q^n * Real.cos (n*θ) := by
  unfold phase
  rw [mul_pow, ← Complex.exp_nat_mul]
  have he : (n : ℂ) * ((θ : ℂ) * Complex.I) = (((n : ℝ)*θ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [he, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    sub_zero, Complex.exp_ofReal_mul_I_re]

lemma cosine_geometric_hasSum (q θ : ℝ) (hq : |q| < 1) :
    HasSum (fun n : ℕ => q^(n+1) * Real.cos ((n+1 : ℝ)*θ))
      ((1-phase q θ)⁻¹ - 1).re := by
  have hz : ‖phase q θ‖ < 1 := by rwa [norm_phase]
  have h : HasSum (fun n : ℕ => phase q θ ^ (n+1)) ((1-phase q θ)⁻¹ - 1) := by
    simpa only [Finset.sum_range_one, pow_zero] using
      (hasSum_nat_add_iff' (f := fun n : ℕ => phase q θ ^ n) 1).mpr
        (hasSum_geometric_of_norm_lt_one hz)
  simpa only [phase_pow_re, Nat.cast_add, Nat.cast_one] using Complex.hasSum_re h

lemma cosine_weighted_hasSum (q θ : ℝ) (hq : |q| < 1) :
    HasSum (fun n : ℕ => (n+1 : ℝ)*q^(n+1) * Real.cos ((n+1 : ℝ)*θ))
      (phase q θ / (1-phase q θ)^2).re := by
  have hz : ‖phase q θ‖ < 1 := by rwa [norm_phase]
  have h : HasSum (fun n : ℕ => (n+1 : ℂ)*phase q θ ^ (n+1))
      (phase q θ / (1-phase q θ)^2) := by
    simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero,
      Nat.cast_add, Nat.cast_one] using
      (hasSum_nat_add_iff' (f := fun n : ℕ => (n : ℂ)*phase q θ ^ n) 1).mpr
        (hasSum_coe_mul_geometric_of_norm_lt_one hz)
  have ht := Complex.hasSum_re h
  simpa only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.natCast_re,
    Complex.natCast_im, Complex.one_re, Complex.one_im, add_zero, zero_add,
    zero_mul, sub_zero, phase_pow_re, Nat.cast_add, Nat.cast_one, mul_assoc] using ht

lemma phase_re (q θ : ℝ) : (phase q θ).re = q * Real.cos θ := by
  simp only [phase, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

lemma phase_im (q θ : ℝ) : (phase q θ).im = q * Real.sin θ := by
  simp only [phase, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]

noncomputable def geometricDenominator (q θ : ℝ) : ℝ := 1 - 2*q*Real.cos θ + q^2

lemma phase_normSq_sub (q θ : ℝ) :
    Complex.normSq (1-phase q θ) = geometricDenominator q θ := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, phase_re, Complex.sub_im,
    Complex.one_im, phase_im]
  unfold geometricDenominator
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma geometricDenominator_pos (q θ : ℝ) (hq : |q| < 1) :
    0 < geometricDenominator q θ := by
  rw [← phase_normSq_sub]
  apply Complex.normSq_pos.mpr
  intro h
  have hz : phase q θ = 1 := by linear_combination -h
  have hn := norm_phase q θ
  rw [hz, norm_one] at hn
  linarith

lemma cosine_geometric_tsum (q θ : ℝ) (hq : |q| < 1) :
    (∑' n : ℕ, q^(n+1)*Real.cos ((n+1 : ℝ)*θ)) =
      (q*Real.cos θ-q^2) / geometricDenominator q θ := by
  rw [(cosine_geometric_hasSum q θ hq).tsum_eq, Complex.sub_re,
    Complex.inv_re, Complex.one_re, Complex.sub_re, phase_re,
    phase_normSq_sub]
  simp only [Complex.one_re]
  have hd := ne_of_gt (geometricDenominator_pos q θ hq)
  field_simp [hd]
  unfold geometricDenominator
  ring

lemma cosine_weighted_tsum (q θ : ℝ) (hq : |q| < 1) :
    (∑' n : ℕ, (n+1 : ℝ)*q^(n+1)*Real.cos ((n+1 : ℝ)*θ)) =
      (q*(1+q^2)*Real.cos θ-2*q^2) / geometricDenominator q θ ^ 2 := by
  rw [(cosine_weighted_hasSum q θ hq).tsum_eq, Complex.div_re,
    pow_two, Complex.normSq_mul, phase_normSq_sub]
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, phase_re, phase_im]
  have hd := ne_of_gt (geometricDenominator_pos q θ hq)
  field_simp [hd]
  linear_combination (q^3 * Real.cos θ - 2*q^2) * (Real.sin_sq_add_cos_sq θ)

end PeriodicPoleTask
