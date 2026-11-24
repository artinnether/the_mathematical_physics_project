import ShiftedCosine.ComplexSeries
import Mathlib.Analysis.Complex.Trigonometric

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def positivePhase (q : ℂ) (x : ℝ) : ℂ := q*Complex.exp ((x : ℂ)*Complex.I)
noncomputable def negativePhase (q : ℂ) (x : ℝ) : ℂ := q*Complex.exp ((-x : ℝ)*Complex.I)

lemma phase_norms (q : ℂ) (x : ℝ) : ‖positivePhase q x‖=‖q‖ ∧ ‖negativePhase q x‖=‖q‖ := by
  constructor <;> simp only [positivePhase,negativePhase,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]

lemma phase_sum (q : ℂ) (x : ℝ) : positivePhase q x+negativePhase q x=2*q*(Real.cos x : ℂ) := by
  unfold positivePhase negativePhase
  have he : Complex.exp ((x : ℂ)*Complex.I)+Complex.exp ((-x : ℝ)*Complex.I)=2*(Real.cos x : ℂ) := by
    apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
      Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,Real.cos_neg,Real.sin_neg] <;> ring
  rw [← mul_add,he]
  ring

lemma phase_product (q : ℂ) (x : ℝ) : positivePhase q x*negativePhase q x=q^2 := by
  unfold positivePhase negativePhase
  calc
    _ = q^2*(Complex.exp ((x : ℂ)*Complex.I)*Complex.exp ((-x : ℝ)*Complex.I)) := by ring
    _ = q^2 := by rw [← Complex.exp_add]; simp

lemma phase_power_sum (q : ℂ) (x : ℝ) (n : ℕ) :
    positivePhase q x^n+negativePhase q x^n=2*q^n*(Real.cos ((n : ℝ)*x) : ℂ) := by
  unfold positivePhase negativePhase
  rw [mul_pow,mul_pow,← Complex.exp_nat_mul,← Complex.exp_nat_mul]
  have hp : (n : ℂ)*((x : ℂ)*Complex.I)=(((n : ℝ)*x : ℝ) : ℂ)*Complex.I := by push_cast; ring
  have hm : (n : ℂ)*(((-x : ℝ) : ℂ)*Complex.I)=((-((n : ℝ)*x) : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [hp,hm]
  exact phase_sum (q^n) ((n : ℝ)*x)

lemma complex_cosine_geometric_hasSum (q : ℂ) (x : ℝ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q^(n+1)*(Real.cos ((n+1 : ℝ)*x) : ℂ))
      ((((1-positivePhase q x)⁻¹-1)+((1-negativePhase q x)⁻¹-1))/2) := by
  have hp : HasSum (fun n : ℕ => positivePhase q x^(n+1)) ((1-positivePhase q x)⁻¹-1) := by
    simpa only [Finset.sum_range_one,pow_zero] using
      (hasSum_nat_add_iff' (f := fun n : ℕ => positivePhase q x^n) 1).mpr
        (hasSum_geometric_of_norm_lt_one (by rw [(phase_norms q x).1]; exact hq))
  have hm : HasSum (fun n : ℕ => negativePhase q x^(n+1)) ((1-negativePhase q x)⁻¹-1) := by
    simpa only [Finset.sum_range_one,pow_zero] using
      (hasSum_nat_add_iff' (f := fun n : ℕ => negativePhase q x^n) 1).mpr
        (hasSum_geometric_of_norm_lt_one (by rw [(phase_norms q x).2]; exact hq))
  have h := (hp.add hm).div_const 2
  apply h.congr_fun
  intro n
  rw [phase_power_sum]
  push_cast
  ring

lemma complex_cosine_weighted_hasSum (q : ℂ) (x : ℝ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (n+1 : ℂ)*q^(n+1)*(Real.cos ((n+1 : ℝ)*x) : ℂ))
      ((positivePhase q x/(1-positivePhase q x)^2+negativePhase q x/(1-negativePhase q x)^2)/2) := by
  have hp : HasSum (fun n : ℕ => (n+1 : ℂ)*positivePhase q x^(n+1))
      (positivePhase q x/(1-positivePhase q x)^2) := by
    simpa only [Finset.sum_range_one,Nat.cast_zero,zero_mul,sub_zero,Nat.cast_add,Nat.cast_one] using
      (hasSum_nat_add_iff' (f := fun n : ℕ => (n : ℂ)*positivePhase q x^n) 1).mpr
        (hasSum_coe_mul_geometric_of_norm_lt_one (by rw [(phase_norms q x).1]; exact hq))
  have hm : HasSum (fun n : ℕ => (n+1 : ℂ)*negativePhase q x^(n+1))
      (negativePhase q x/(1-negativePhase q x)^2) := by
    simpa only [Finset.sum_range_one,Nat.cast_zero,zero_mul,sub_zero,Nat.cast_add,Nat.cast_one] using
      (hasSum_nat_add_iff' (f := fun n : ℕ => (n : ℂ)*negativePhase q x^n) 1).mpr
        (hasSum_coe_mul_geometric_of_norm_lt_one (by rw [(phase_norms q x).2]; exact hq))
  have h := (hp.add hm).div_const 2
  apply h.congr_fun
  intro n
  rw [← mul_add,phase_power_sum]
  push_cast
  ring

lemma complex_geometricDenominator_ne (q : ℂ) (x : ℝ) (hq : ‖q‖ < 1) :
    1-2*q*(Real.cos x : ℂ)+q^2 ≠ 0 := by
  have hp : 1-positivePhase q x ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have hn := (phase_norms q x).1
    rw [← he,norm_one] at hn
    linarith
  have hm : 1-negativePhase q x ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have hn := (phase_norms q x).2
    rw [← he,norm_one] at hn
    linarith
  have he : (1-positivePhase q x)*(1-negativePhase q x)=1-2*q*(Real.cos x : ℂ)+q^2 := by
    calc
      _ = 1-(positivePhase q x+negativePhase q x)+positivePhase q x*negativePhase q x := by ring
      _ = _ := by rw [phase_sum,phase_product]
  rw [← he]
  exact mul_ne_zero hp hm

lemma phase_denominator_ne (q : ℂ) (x : ℝ) (hq : ‖q‖ < 1) :
    1-positivePhase q x ≠ 0 ∧ 1-negativePhase q x ≠ 0 := by
  constructor
  · intro h
    have he := sub_eq_zero.mp h
    have hn := (phase_norms q x).1
    rw [← he,norm_one] at hn
    linarith
  · intro h
    have he := sub_eq_zero.mp h
    have hn := (phase_norms q x).2
    rw [← he,norm_one] at hn
    linarith

lemma complex_geometric_tsum (q : ℂ) (x : ℝ) (hq : ‖q‖ < 1) :
    1+2*complexCosineSeries (fun n => q^(n+1)) x =
      (1-q^2)/(1-2*q*(Real.cos x : ℂ)+q^2) := by
  unfold complexCosineSeries
  rw [(complex_cosine_geometric_hasSum q x hq).tsum_eq]
  have h := phase_denominator_ne q x hq
  have hden : 1-2*q*(Real.cos x : ℂ)+q^2 =
      (1-positivePhase q x)*(1-negativePhase q x) := by
    rw [show (1-positivePhase q x)*(1-negativePhase q x)=
      1-(positivePhase q x+negativePhase q x)+positivePhase q x*negativePhase q x by ring,
      phase_sum,phase_product]
  rw [hden,← phase_product q x]
  field_simp [h.1,h.2]
  ring

lemma complex_weighted_tsum (q : ℂ) (x : ℝ) (hq : ‖q‖ < 1) :
    complexCosineSeries (fun n => (n+1 : ℂ)*q^(n+1)) x =
      (q*(1+q^2)*(Real.cos x : ℂ)-2*q^2)/(1-2*q*(Real.cos x : ℂ)+q^2)^2 := by
  unfold complexCosineSeries
  rw [(complex_cosine_weighted_hasSum q x hq).tsum_eq]
  have h := phase_denominator_ne q x hq
  have hden : 1-2*q*(Real.cos x : ℂ)+q^2 =
      (1-positivePhase q x)*(1-negativePhase q x) := by
    rw [show (1-positivePhase q x)*(1-negativePhase q x)=
      1-(positivePhase q x+negativePhase q x)+positivePhase q x*negativePhase q x by ring,
      phase_sum,phase_product]
  have hnum : q*(1+q^2)*(Real.cos x : ℂ)-2*q^2 =
      ((positivePhase q x+negativePhase q x)*(1+positivePhase q x*negativePhase q x)-
        4*(positivePhase q x*negativePhase q x))/2 := by
    rw [phase_sum,phase_product]
    ring
  rw [hden,hnum]
  field_simp [h.1,h.2]
  ring

lemma complex_kernel_fourier (q : ℂ) (x : ℝ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    1/((Real.cos x : ℂ)-(1+q^2)/(2*q))^2 =
      ((1+q^2)/(2*q))/((1-q^2)/(2*q))^3*
        (1+2*complexCosineSeries (fun n => q^(n+1)) x)+
      2/((1-q^2)/(2*q))^2*complexCosineSeries (fun n => (n+1 : ℂ)*q^(n+1)) x := by
  have hD := complex_geometricDenominator_ne q x hq
  have hsq : 1-q^2 ≠ 0 := by
    intro h
    have he : q^2=1 := (sub_eq_zero.mp h).symm
    have hn := congrArg norm he
    rw [norm_pow,norm_one] at hn
    nlinarith [norm_nonneg q]
  have hcos : (Real.cos x : ℂ)-(1+q^2)/(2*q) ≠ 0 := by
    intro h
    apply hD
    have he := sub_eq_zero.mp h
    have he : 2*q*(Real.cos x : ℂ)=1+q^2 := by
      rw [he]
      field_simp
    linear_combination -he
  rw [complex_geometric_tsum q x hq,complex_weighted_tsum q x hq]
  field_simp [hq0,hsq,hD,hcos]
  ring

end ShiftedCosineTask
