import TuringTask.Series
import TuringTask.GaussianFourier

open Filter MeasureTheory Set
open scoped Topology
namespace TangentShiftTask

noncomputable def weight (α x : ℝ) : ℝ := Real.exp (-α*x^2)
noncomputable def angle (b : ℝ) : ℝ := Real.arctan b
noncomputable def denominator (b x : ℝ) : ℝ := Real.sin x^2-b^2*Real.cos x^2
noncomputable def poleIntegrand (α b x : ℝ) : ℝ :=
  weight α x*Real.cos x^2/denominator b x
noncomputable def cell (α b δ : ℝ) (k : ℤ) : ℝ :=
  (∫ t in (-Real.pi/2)..(-angle b-δ), poleIntegrand α b (k*Real.pi+t)) +
  (∫ t in (-angle b+δ)..(angle b-δ), poleIntegrand α b (k*Real.pi+t)) +
  (∫ t in (angle b+δ)..(Real.pi/2), poleIntegrand α b (k*Real.pi+t))
noncomputable def truncation (α b δ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), cell α b δ k
noncomputable def poleMass (α b : ℝ) : ℝ :=
  ∑' k : ℤ, (weight α (k*Real.pi+angle b)+weight α (k*Real.pi-angle b))
noncomputable def spectralTerm (α b : ℝ) (n : ℕ) : ℝ :=
  Real.sin (2*(n+1 : ℝ)*angle b)*Real.exp (-((n+1 : ℝ)^2)/α)
noncomputable def principalValue (α b : ℝ) : ℝ :=
  -Real.sqrt (Real.pi/α)/(1+b^2)*(1+2/b*∑' n : ℕ, spectralTerm α b n)
noncomputable def regulatedDenominator (b ε x : ℝ) : ℂ :=
  (denominator b x : ℂ)+Complex.I*(ε : ℂ)*(Real.cos x : ℂ)^2
noncomputable def feynmanIntegrand (α b ε x : ℝ) : ℂ :=
  (weight α x : ℂ)*(Real.cos x : ℂ)^2/regulatedDenominator b ε x
noncomputable def feynmanIntegral (α b ε : ℝ) : ℂ := ∫ x : ℝ, feynmanIntegrand α b ε x
noncomputable def abelKernel (b r x : ℝ) : ℝ :=
  -1/(1+b^2)-2/(b*(1+b^2))*∑' n : ℕ,
    r^(n+1)*Real.sin (2*(n+1 : ℝ)*angle b)*Real.cos (2*(n+1 : ℝ)*x)
noncomputable def abelIntegral (α b r : ℝ) : ℝ :=
  ∫ x : ℝ, weight α x*abelKernel b r x

lemma regulatedDenominator_ne_zero (b ε x : ℝ) (hε : 0 < ε) :
    regulatedDenominator b ε x ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  simp only [regulatedDenominator, ← Complex.ofReal_pow, Complex.add_im,
    Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_zero, one_mul, zero_add] at hi
  simp only [regulatedDenominator, ← Complex.ofReal_pow, Complex.add_re,
    Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, zero_mul, mul_zero, sub_zero,
    add_zero] at hr
  have hc : Real.cos x = 0 := by
    have : Real.cos x^2 = 0 := (mul_eq_zero.mp hi).resolve_left (ne_of_gt hε)
    nlinarith [sq_nonneg (Real.cos x)]
  have hs := Real.sin_sq_add_cos_sq x
  simp [denominator, hc] at hr
  rw [hr, hc] at hs
  norm_num at hs

lemma feynman_integrable (α b ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    Integrable (feynmanIntegrand α b ε) := by
  have hc : Continuous (feynmanIntegrand α b ε) := by
    unfold feynmanIntegrand regulatedDenominator denominator weight
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact regulatedDenominator_ne_zero b ε x hε
  have hb (x : ℝ) : ‖feynmanIntegrand α b ε x‖ ≤ weight α x/ε := by
    have hd : ε*Real.cos x^2 ≤ ‖regulatedDenominator b ε x‖ := by
      have h := Complex.abs_im_le_norm (regulatedDenominator b ε x)
      simpa only [regulatedDenominator, ← Complex.ofReal_pow, Complex.add_im,
        Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, zero_mul, mul_zero, one_mul, zero_add, add_zero,
        abs_of_nonneg (mul_nonneg hε.le (sq_nonneg _))] using h
    have hp : 0 < ‖regulatedDenominator b ε x‖ :=
      norm_pos_iff.mpr (regulatedDenominator_ne_zero b ε x hε)
    unfold feynmanIntegrand
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < weight α x from Real.exp_pos _),
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    apply (div_le_div_iff₀ hp hε).mpr
    have hw : 0 ≤ weight α x := (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left hd hw]
  exact ((integrable_exp_neg_mul_sq hα).div_const ε).mono'
    hc.aestronglyMeasurable (Eventually.of_forall hb)

end TangentShiftTask
