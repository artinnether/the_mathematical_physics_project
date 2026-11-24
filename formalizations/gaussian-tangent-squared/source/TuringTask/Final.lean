import TuringTask.Specification
import TuringTask.HadamardEvaluation
import TuringTask.PoleOrientation
import TuringTask.AbelIntegral
import Mathlib.Topology.Algebra.Order.Field

open Filter MeasureTheory
open scoped Topology
namespace PeriodicPoleTask

lemma outerValue_tendsto_atTop (α : ℝ) (hα : 0 < α) :
    Tendsto (outerValue α) (𝓝[>] (0 : ℝ)) atTop := by
  have hp : 0 < 2*poleMass α := mul_pos (by norm_num) (poleMass_pos α hα)
  have hd : Tendsto (fun δ : ℝ => 2*poleMass α/δ) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [div_eq_mul_inv] using (tendsto_inv_nhdsGT_zero : Tendsto (fun δ : ℝ => δ⁻¹) (𝓝[>] (0 : ℝ)) atTop).const_mul_atTop hp
  have h := (hadamard_tendsto α hα).add_atTop hd
  simpa only [sub_add_cancel] using h

/-- Complete solution with the original definitions and common actual-limit witnesses. -/
theorem periodic_gaussian_double_poles (α : ℝ) (hα : 0 < α) : PeriodicPoleClaim α := by
  refine ⟨outerValue α,finitePartValue α,(finitePartValue α : ℂ),
    poleMass_summable α hα,?_,?_,rfl,spectral_summable α hα,
    outerValue_tendsto_atTop α hα,?_,feynmanIntegral_tendsto α hα,rfl,sub_self _,
    pole_orientation,?_,?_,abelIntegral_tendsto α hα,finitePartValue_neg α hα⟩
  · exact fun δ hδ hδp => truncation_tendsto α δ hα hδ hδp
  · rw [← hadamardIntegralValue_eq α hα]
    exact hadamard_tendsto α hα
  · exact fun ε hε => feynman_integrable α ε hα hε
  · exact fun ε _ => feynmanIntegral_im_zero α ε
  · exact fun r hr hr1 => abel_integrable α r hα hr.le hr1

end PeriodicPoleTask
