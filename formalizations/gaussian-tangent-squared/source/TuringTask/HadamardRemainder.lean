import TuringTask.PeriodizationSmooth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter MeasureTheory Set
open scoped Topology
namespace PeriodicPoleTask

noncomputable def hadamardRemainder (α t : ℝ) : ℝ :=
  (periodizedWeight α t - poleMass α) / Real.sin t^2

lemma periodizedWeight_measurable (α : ℝ) : Measurable (periodizedWeight α) := by
  exact Measurable.tsum (fun k => by unfold weight; fun_prop)

lemma hadamardRemainder_measurable (α : ℝ) : Measurable (hadamardRemainder α) :=
  ((periodizedWeight_measurable α).sub_const _).div (by fun_prop : Measurable (fun t : ℝ => Real.sin t^2))

lemma hadamardRemainder_bound (α t : ℝ) (hα : 0 < α) (ht : |t| < Real.pi/2) :
    ‖hadamardRemainder α t‖ ≤ (∑' k : ℤ, latticeSecondMajorant α k) * Real.pi^2/4 := by
  let M := ∑' k : ℤ, latticeSecondMajorant α k
  have hM : 0 ≤ M := tsum_nonneg (fun k => by unfold latticeSecondMajorant latticeMajorant weight; positivity)
  by_cases ht0 : t = 0
  · subst t
    simp only [hadamardRemainder,Real.sin_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),div_zero,norm_zero]
    positivity
  have hj := Real.mul_abs_le_abs_sin ht.le
  have hsin0 : 0 < |Real.sin t| := lt_of_lt_of_le (by positivity : 0 < 2/Real.pi*|t|) hj
  have hs2 : 0 < Real.sin t^2 := by nlinarith [sq_abs (Real.sin t)]
  have hj' : 2*|t| ≤ Real.pi*|Real.sin t| := by
    have h := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
    field_simp at h
    nlinarith
  have hsq : 4*t^2 ≤ Real.pi^2*Real.sin t^2 := by
    nlinarith [sq_abs t,sq_abs (Real.sin t),
      mul_nonneg (sub_nonneg.mpr hj') (show 0 ≤ Real.pi*|Real.sin t|+2*|t| by positivity)]
  unfold hadamardRemainder
  rw [norm_div]
  simp only [Real.norm_eq_abs,abs_of_pos hs2]
  apply (div_le_iff₀ hs2).mpr
  have hn := periodizedWeight_quadratic_bound α t hα ht
  rw [Real.norm_eq_abs] at hn
  have hm := mul_le_mul_of_nonneg_left hsq hM
  dsimp [M] at hm hM
  nlinarith

lemma hadamardRemainder_integrableOn (α : ℝ) (hα : 0 < α) :
    IntegrableOn (hadamardRemainder α) (Ioo (-Real.pi/2) (Real.pi/2)) := by
  apply (integrable_const ((∑' k : ℤ, latticeSecondMajorant α k)*Real.pi^2/4)
    (μ := volume.restrict (Ioo (-Real.pi/2) (Real.pi/2)))).mono'
    (hadamardRemainder_measurable α).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hadamardRemainder_bound α t hα (abs_lt.mpr ⟨by linarith [ht.1],ht.2⟩)

lemma hadamardRemainder_intervalIntegrable (α : ℝ) (hα : 0 < α) :
    IntervalIntegrable (hadamardRemainder α) volume (-Real.pi/2) (Real.pi/2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos]),
    integrableOn_Ioc_iff_integrableOn_Ioo]
  exact hadamardRemainder_integrableOn α hα

end PeriodicPoleTask
