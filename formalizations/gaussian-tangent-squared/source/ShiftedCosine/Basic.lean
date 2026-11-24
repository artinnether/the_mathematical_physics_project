import TuringTask.Series
import TuringTask.GaussianFourier
import Mathlib.Analysis.Normed.Group.Tannery

open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def weight (a x : ℝ) : ℝ := Real.exp (-a*x^2)
noncomputable def cell (a θ δ : ℝ) (k : ℤ) : ℝ :=
  (∫ t in (-Real.pi)..(-θ-δ), weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2) +
  (∫ t in (-θ+δ)..(θ-δ), weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2) +
  (∫ t in (θ+δ)..Real.pi, weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2)
noncomputable def truncation (a θ δ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ShiftedCosineTask.cell a θ δ k
noncomputable def poleMass (a θ : ℝ) : ℝ :=
  ∑' k : ℤ, (weight a (2*k*Real.pi+θ)+weight a (2*k*Real.pi-θ))
noncomputable def realCoefficient (θ : ℝ) (n : ℕ) : ℝ :=
  -(n+1 : ℝ)*Real.cos ((n+1 : ℝ)*θ)/Real.sin θ^2 +
    Real.cos θ*Real.sin ((n+1 : ℝ)*θ)/Real.sin θ^3
noncomputable def imaginaryCoefficient (θ : ℝ) (n : ℕ) : ℝ :=
  -(n+1 : ℝ)*Real.sin ((n+1 : ℝ)*θ)/Real.sin θ^2 -
    Real.cos θ*Real.cos ((n+1 : ℝ)*θ)/Real.sin θ^3
noncomputable def gaussianTerm (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((n+1 : ℝ)^2)/(4*a))
noncomputable def finitePartValue (a θ : ℝ) : ℝ :=
  2*Real.sqrt (Real.pi/a)*∑' n : ℕ, realCoefficient θ n*gaussianTerm a n
noncomputable def imaginaryValue (a θ : ℝ) : ℝ :=
  Real.sqrt (Real.pi/a)*(-Real.cos θ/Real.sin θ^3+
    2*∑' n : ℕ, imaginaryCoefficient θ n*gaussianTerm a n)
noncomputable def feynmanIntegrand (a θ ε x : ℝ) : ℂ :=
  (weight a x : ℂ)/((Real.cos x-Real.cos θ : ℝ)+Complex.I*(ε : ℂ))^2
noncomputable def feynmanIntegral (a θ ε : ℝ) : ℂ := ∫ x : ℝ, feynmanIntegrand a θ ε x
noncomputable def abelKernel (θ r x : ℝ) : ℝ :=
  2*∑' n : ℕ, realCoefficient θ n*r^(n+1)*Real.cos ((n+1 : ℝ)*x)
noncomputable def abelIntegral (a θ r : ℝ) : ℝ := ∫ x : ℝ, weight a x*abelKernel θ r x

lemma feynman_denominator_ne_zero (θ ε x : ℝ) (hε : 0 < ε) :
    ((Real.cos x-Real.cos θ : ℝ) : ℂ)+Complex.I*(ε : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

lemma feynman_integrable (a θ ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    Integrable (feynmanIntegrand a θ ε) := by
  have hc : Continuous (feynmanIntegrand a θ ε) := by
    unfold feynmanIntegrand weight
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact pow_ne_zero 2 (feynman_denominator_ne_zero θ ε x hε)
  have hb (x : ℝ) : ‖feynmanIntegrand a θ ε x‖ ≤ weight a x/ε^2 := by
    have hd : ε ≤ ‖((Real.cos x-Real.cos θ : ℝ) : ℂ)+Complex.I*(ε : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (((Real.cos x-Real.cos θ : ℝ) : ℂ)+Complex.I*(ε : ℂ))
      simpa [abs_of_pos hε] using h
    have hd2 : ε^2 ≤ ‖((Real.cos x-Real.cos θ : ℝ) : ℂ)+Complex.I*(ε : ℂ)‖^2 :=
      pow_le_pow_left₀ hε.le hd 2
    unfold feynmanIntegrand
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < weight a x from Real.exp_pos _)]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (sq_pos_of_pos hε) hd2
  exact ((integrable_exp_neg_mul_sq ha).div_const (ε^2)).mono'
    hc.aestronglyMeasurable (Eventually.of_forall hb)

end ShiftedCosineTask
