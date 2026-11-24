import SimpleTangent.Transformed
import SimpleTangent.PrincipalValue
import ShiftedCosine.HadamardEvaluation

open Filter MeasureTheory Set
open scoped Topology

namespace TangentSquaredTask

noncomputable def weight (α x : ℝ) : ℝ := Real.exp (-α*x^2)
noncomputable abbrev angle (b : ℝ) : ℝ := TangentShiftTask.angle b
noncomputable def denominator (b x : ℝ) : ℝ := Real.sin x^2-b^2*Real.cos x^2
noncomputable def poleIntegrand (α b x : ℝ) : ℝ :=
  weight α x*Real.cos x^4/(denominator b x)^2
noncomputable def cell (α b δ : ℝ) (k : ℤ) : ℝ :=
  (∫ t in (-Real.pi/2)..(-angle b-δ), poleIntegrand α b (k*Real.pi+t)) +
  (∫ t in (-angle b+δ)..(angle b-δ), poleIntegrand α b (k*Real.pi+t)) +
  (∫ t in (angle b+δ)..(Real.pi/2), poleIntegrand α b (k*Real.pi+t))
noncomputable def truncation (α b δ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), cell α b δ k
noncomputable def poleMass (α b : ℝ) : ℝ :=
  ∑' k : ℤ, (weight α (k*Real.pi+angle b)+weight α (k*Real.pi-angle b))
noncomputable def subtraction (α b δ : ℝ) : ℝ :=
  poleMass α b/(2*b^2*(1+b^2)^2*δ)
noncomputable def coefficient (b : ℝ) (n : ℕ) : ℝ :=
  (1+3*b^2)/b^3*Real.sin (2*(n+1 : ℝ)*angle b) -
  2*(n+1 : ℝ)/b^2*Real.cos (2*(n+1 : ℝ)*angle b)
noncomputable def spectralTerm (α b : ℝ) (n : ℕ) : ℝ :=
  coefficient b n*Real.exp (-((n+1 : ℝ)^2)/α)
noncomputable def finitePartValue (α b : ℝ) : ℝ :=
  Real.sqrt (Real.pi/α)/(1+b^2)^2*(1+∑' n : ℕ, spectralTerm α b n)
noncomputable def massDerivativeTerm (α b : ℝ) (k : ℤ) : ℝ :=
  (-2*α*(k*Real.pi+angle b)*weight α (k*Real.pi+angle b) +
    2*α*(k*Real.pi-angle b)*weight α (k*Real.pi-angle b))/(1+b^2)
noncomputable def massDerivativeValue (α b : ℝ) : ℝ :=
  ∑' k : ℤ, massDerivativeTerm α b k
noncomputable def imaginaryValue (α b : ℝ) : ℝ :=
  Real.pi*(1+3*b^2)*poleMass α b/(4*b^3*(1+b^2)^2) -
  Real.pi*massDerivativeValue α b/(4*b^2*(1+b^2))
noncomputable def regulatedDenominator (b ε x : ℝ) : ℂ :=
  (denominator b x : ℂ)+Complex.I*(ε : ℂ)*(Real.cos x : ℂ)^2
noncomputable def feynmanIntegrand (α b ε x : ℝ) : ℂ :=
  (weight α x : ℂ)*(Real.cos x : ℂ)^4/(regulatedDenominator b ε x)^2
noncomputable def feynmanIntegral (α b ε : ℝ) : ℂ :=
  ∫ x : ℝ, feynmanIntegrand α b ε x
noncomputable def abelKernel (b r x : ℝ) : ℝ :=
  (1+∑' n : ℕ, coefficient b n*r^(n+1)*Real.cos (2*(n+1 : ℝ)*x))/(1+b^2)^2
noncomputable def abelIntegral (α b r : ℝ) : ℝ :=
  ∫ x : ℝ, weight α x*abelKernel b r x

lemma feynman_integrable (α b ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    Integrable (feynmanIntegrand α b ε) := by
  have hn (x : ℝ) : regulatedDenominator b ε x ≠ 0 :=
    TangentShiftTask.regulatedDenominator_ne_zero b ε x hε
  have hc : Continuous (feynmanIntegrand α b ε) := by
    unfold feynmanIntegrand regulatedDenominator denominator weight
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact pow_ne_zero 2 (hn x)
  have hb (x : ℝ) : ‖feynmanIntegrand α b ε x‖ ≤ weight α x/ε^2 := by
    have hd : ε*Real.cos x^2 ≤ ‖regulatedDenominator b ε x‖ := by
      have h := Complex.abs_im_le_norm (regulatedDenominator b ε x)
      simpa only [regulatedDenominator, ← Complex.ofReal_pow, Complex.add_im,
        Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, zero_mul, mul_zero, one_mul, zero_add, add_zero,
        abs_of_nonneg (mul_nonneg hε.le (sq_nonneg _))] using h
    have hd2 := pow_le_pow_left₀ (mul_nonneg hε.le (sq_nonneg (Real.cos x))) hd 2
    have hp : 0 < ‖regulatedDenominator b ε x‖^2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (hn x))
    unfold feynmanIntegrand
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < weight α x from Real.exp_pos _),
      Complex.norm_real, Real.norm_eq_abs]
    rw [show |Real.cos x|^4 = Real.cos x^4 by
      calc
        _ = (|Real.cos x|^2)^2 := by ring
        _ = (Real.cos x^2)^2 := by rw [sq_abs]
        _ = _ := by ring]
    apply (div_le_div_iff₀ hp (sq_pos_of_pos hε)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd2 (show 0 ≤ weight α x from (Real.exp_pos _).le)]
  exact ((integrable_exp_neg_mul_sq hα).div_const (ε^2)).mono'
    hc.aestronglyMeasurable (Eventually.of_forall hb)

end TangentSquaredTask
