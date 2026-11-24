import TangentSquared.Basic
import SimpleTangent.Mass
import SimpleTangent.Series

open Filter
open scoped Topology
namespace TangentSquaredTask

lemma poleMass_summable (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Summable (fun k : ℤ => weight α (k*Real.pi+angle b)+weight α (k*Real.pi-angle b)) :=
  TangentShiftTask.poleMass_summable α b hα hb

lemma poleMass_pos (α b : ℝ) (hα : 0 < α) (hb : 0 < b) : 0 < poleMass α b :=
  TangentShiftTask.poleMass_pos α b hα hb

lemma coefficient_bound (b : ℝ) (n : ℕ) :
    ‖coefficient b n‖ ≤ |(1+3*b^2)/b^3|+|2/b^2| *(n+1 : ℝ) := by
  unfold coefficient
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · have he : 2*(n+1 : ℝ)/b^2*Real.cos (2*(n+1 : ℝ)*angle b)=
        (2/b^2)*(n+1 : ℝ)*Real.cos (2*(n+1 : ℝ)*angle b) := by ring
    rw [he,norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (n+1 : ℝ))]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

lemma spectral_majorant_summable (α b : ℝ) (hα : 0 < α) :
    Summable (fun n : ℕ => (|(1+3*b^2)/b^3|+|2/b^2| *(n+1 : ℝ))*
      Real.exp (-((n+1 : ℝ)^2)/α)) := by
  have h0 := TangentShiftTask.gaussian_sequence_summable α hα
  have h1 := PeriodicPoleTask.spectral_summable α hα
  have h := (h0.mul_left |(1+3*b^2)/b^3|).add (h1.mul_left |2/b^2|)
  apply h.congr
  intro n
  unfold PeriodicPoleTask.spectralTerm
  ring

lemma spectral_summable (α b : ℝ) (hα : 0 < α) : Summable (spectralTerm α b) := by
  apply Summable.of_norm_bounded (spectral_majorant_summable α b hα)
  intro n
  unfold spectralTerm
  rw [norm_mul,show ‖Real.exp (-((n+1 : ℝ)^2)/α)‖ = Real.exp (-((n+1 : ℝ)^2)/α) by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]]
  exact mul_le_mul_of_nonneg_right (coefficient_bound b n) (Real.exp_pos _).le

end TangentSquaredTask
