import TangentSquared.Evaluation
import Mathlib.Topology.Algebra.Order.Field

open Filter
open scoped Topology
namespace TangentSquaredTask

lemma outerValue_scaled_tendsto (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Tendsto (fun δ => δ*outerValue α b δ) (𝓝[>] (0 : ℝ))
      (𝓝 (poleMass α b/(2*b^2*(1+b^2)^2))) := by
  have hi : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (hi.mul (hadamard_tendsto α b hα hb)).add
    (tendsto_const_nhds (x := poleMass α b/(2*b^2*(1+b^2)^2)))
  simp only [zero_mul,zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  unfold subtraction
  field_simp [ne_of_gt (show 0 < δ from hδ),hb.ne',show (1 : ℝ)+b^2 ≠ 0 by positivity]
  ring

lemma outerValue_tendsto_atTop (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Tendsto (outerValue α b) (𝓝[>] (0 : ℝ)) atTop := by
  have hp : 0 < poleMass α b/(2*b^2*(1+b^2)^2) :=
    div_pos (poleMass_pos α b hα hb) (by positivity)
  have hd : Tendsto (subtraction α b) (𝓝[>] (0 : ℝ)) atTop := by
    have h := (tendsto_inv_nhdsGT_zero :
      Tendsto (fun δ : ℝ => δ⁻¹) (𝓝[>] (0 : ℝ)) atTop).const_mul_atTop hp
    convert h using 1
    funext δ
    unfold subtraction
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have h := (hadamard_tendsto α b hα hb).add_atTop hd
  simpa only [sub_add_cancel] using h

end TangentSquaredTask
