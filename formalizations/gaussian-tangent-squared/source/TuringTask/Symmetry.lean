import TuringTask.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory
open scoped ComplexConjugate
namespace PeriodicPoleTask

lemma feynman_reflection (α ε x : ℝ) :
    feynmanIntegrand α ε (-x) = starRingEnd ℂ (feynmanIntegrand α ε x) := by
  unfold feynmanIntegrand
  rw [weight_even, Real.sin_neg]
  simp only [map_div₀, map_pow, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_neg]
  congr 1
  ring

lemma feynmanIntegral_conj (α ε : ℝ) :
    starRingEnd ℂ (feynmanIntegral α ε) = feynmanIntegral α ε := by
  unfold feynmanIntegral
  rw [← integral_conj]
  simpa only [← feynman_reflection] using
    (integral_neg_eq_self (feynmanIntegrand α ε) volume)

lemma feynmanIntegral_im_zero (α ε : ℝ) :
    (feynmanIntegral α ε).im = 0 := by
  have h := congrArg Complex.im (feynmanIntegral_conj α ε)
  simp only [Complex.conj_im] at h
  linarith

end PeriodicPoleTask
