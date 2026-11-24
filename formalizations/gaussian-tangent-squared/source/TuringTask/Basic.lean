import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter MeasureTheory Set
open scoped Topology

namespace PeriodicPoleTask

noncomputable def weight (α x : ℝ) : ℝ := Real.exp (-α * x ^ 2)

noncomputable def poleIntegrand (α x : ℝ) : ℝ := weight α x / Real.sin x ^ 2

noncomputable def cellTruncation (α δ : ℝ) (k : ℤ) : ℝ :=
  (∫ x in (k * Real.pi - Real.pi / 2)..(k * Real.pi - δ), poleIntegrand α x) +
  (∫ x in (k * Real.pi + δ)..(k * Real.pi + Real.pi / 2), poleIntegrand α x)

noncomputable def truncation (α δ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), cellTruncation α δ k

noncomputable def poleMass (α : ℝ) : ℝ := ∑' k : ℤ, weight α (k * Real.pi)

noncomputable def periodizedWeight (α t : ℝ) : ℝ :=
  ∑' k : ℤ, weight α (t + k * Real.pi)

noncomputable def spectralTerm (α : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * Real.exp (-((n + 1 : ℝ)^2) / α)

noncomputable def finitePartValue (α : ℝ) : ℝ :=
  -4 * Real.sqrt (Real.pi / α) * ∑' n : ℕ, spectralTerm α n

noncomputable def feynmanIntegrand (α ε x : ℝ) : ℂ :=
  (weight α x : ℂ) / (((Real.sin x : ℝ) : ℂ) + Complex.I * (ε : ℂ)) ^ 2

noncomputable def feynmanIntegral (α ε : ℝ) : ℂ :=
  ∫ x : ℝ, feynmanIntegrand α ε x

noncomputable def abelKernel (r x : ℝ) : ℝ :=
  -4 * ∑' n : ℕ,
    (n + 1 : ℝ) * r ^ (n + 1) * Real.cos (2 * (n + 1 : ℝ) * x)

noncomputable def abelIntegral (α r : ℝ) : ℝ :=
  ∫ x : ℝ, weight α x * abelKernel r x

lemma weight_pos (α x : ℝ) : 0 < weight α x := Real.exp_pos _

lemma weight_even (α x : ℝ) : weight α (-x) = weight α x := by
  simp [weight]

lemma denominator_ne_zero (ε x : ℝ) (hε : 0 < ε) :
    ((Real.sin x : ℂ) + Complex.I * (ε : ℂ)) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

lemma norm_denominator_ge (ε x : ℝ) (hε : 0 < ε) :
    ε ≤ ‖(Real.sin x : ℂ) + Complex.I * (ε : ℂ)‖ := by
  have h := Complex.abs_im_le_norm ((Real.sin x : ℂ) + Complex.I * (ε : ℂ))
  simpa [abs_of_pos hε] using h

lemma feynman_integrable (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    Integrable (feynmanIntegrand α ε) := by
  have hc : Continuous (feynmanIntegrand α ε) := by
    unfold feynmanIntegrand weight
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      exact pow_ne_zero 2 (denominator_ne_zero ε x hε)
  have hbound (x : ℝ) : ‖feynmanIntegrand α ε x‖ ≤ weight α x / ε^2 := by
    have hd := norm_denominator_ge ε x hε
    unfold feynmanIntegrand weight
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply div_le_div_of_nonneg_left (Real.exp_pos _).le (sq_pos_of_pos hε)
    nlinarith [norm_nonneg ((Real.sin x : ℂ) + Complex.I * (ε : ℂ))]
  exact ((integrable_exp_neg_mul_sq hα).div_const (ε^2)).mono'
    hc.aestronglyMeasurable (Eventually.of_forall hbound)

end PeriodicPoleTask
