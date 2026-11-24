import TuringTask.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open MeasureTheory
namespace PeriodicPoleTask

lemma gaussian_cosine_integral (α t : ℝ) (hα : 0 < α) :
    (∫ x : ℝ, weight α x * Real.cos (t*x)) =
      Real.sqrt (Real.pi / α) * Real.exp (-t^2/(4*α)) := by
  have hi := fourierIntegral_gaussian (b := (α : ℂ)) (by simpa using hα) (t : ℂ)
  have hgi : Integrable (fun x : ℝ =>
      Complex.exp (Complex.I * (t : ℂ) * x) * Complex.exp (-(α : ℂ) * x^2)) := by
    simpa only [Complex.exp_add, add_zero, mul_comm] using
      integrable_cexp_quadratic (b := (α : ℂ)) (by simpa using hα)
        (Complex.I * (t : ℂ)) 0
  have hs : ((Real.pi : ℂ) / (α : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (Real.pi / α) : ℂ) := by
    rw [← Complex.ofReal_div, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [hs] at hi
  have he : -(t : ℂ)^2 / (4*(α : ℂ)) = ((-t^2/(4*α) : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← Complex.ofReal_exp] at hi
  have hre := congrArg Complex.re hi
  have hir : (∫ x : ℝ, (Complex.exp (Complex.I * (t : ℂ) * x) *
      Complex.exp (-(α : ℂ) * x^2)).re) =
      (∫ x : ℝ, Complex.exp (Complex.I * (t : ℂ) * x) *
      Complex.exp (-(α : ℂ) * x^2)).re := integral_re hgi
  rw [← hir] at hre
  have hpoint (x : ℝ) :
      (Complex.exp (Complex.I * (t : ℂ) * x) * Complex.exp (-(α : ℂ) * x^2)).re =
      weight α x * Real.cos (t*x) := by
    have harg : Complex.I * (t : ℂ) * (x : ℂ) = ((t*x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hw : -(α : ℂ) * (x : ℂ)^2 = ((-α*x^2 : ℝ) : ℂ) := by push_cast; ring
    rw [harg, hw, ← Complex.ofReal_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
    unfold weight
    ring
  simpa only [hpoint, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using hre

end PeriodicPoleTask
