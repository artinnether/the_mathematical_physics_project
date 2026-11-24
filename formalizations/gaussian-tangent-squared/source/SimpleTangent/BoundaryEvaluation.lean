import SimpleTangent.Trigonometry
import ShiftedCosine.Poisson

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set
open scoped Topology
namespace TangentShiftTask

noncomputable def cosineSpectral (α b : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-((n+1 : ℝ)^2)/α)*Real.cos (2*(n+1 : ℝ)*angle b)

lemma boundary_series_summable (α b : ℝ) (hα : 0 < α) :
    Summable (fun n : ℕ => boundaryRatio b^(n+1)*(Real.exp (-((n+1 : ℝ)^2)/α) : ℂ)) := by
  apply (gaussian_sequence_summable α hα).of_norm_bounded
  intro n
  rw [norm_mul,norm_pow,boundaryRatio_phase,ShiftedCosineTask.unitPhase_norm,
    one_pow,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

lemma boundary_series_parts (α b : ℝ) (hα : 0 < α) :
    (∑' n : ℕ, boundaryRatio b^(n+1)*(Real.exp (-((n+1 : ℝ)^2)/α) : ℂ)) =
      (cosineSpectral α b : ℂ)-Complex.I*((∑' n : ℕ, spectralTerm α b n : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.re_tsum (boundary_series_summable α b hα)]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero]
    unfold cosineSpectral
    apply tsum_congr
    intro n
    rw [boundaryRatio_phase,ShiftedCosineTask.unitPhase_pow]
    simp only [ShiftedCosineTask.unitPhase,Complex.mul_re,Complex.add_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show (n+1 : ℝ)*(-2*angle b)=-(2*(n+1 : ℝ)*angle b) by ring,Real.cos_neg]
    ring
  · rw [Complex.im_tsum (boundary_series_summable α b hα)]
    simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,one_mul,zero_add,zero_sub]
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    rw [boundaryRatio_phase,ShiftedCosineTask.unitPhase_pow]
    simp only [ShiftedCosineTask.unitPhase,Complex.mul_im,Complex.add_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,one_mul,zero_add]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show (n+1 : ℝ)*(-2*angle b)=-(2*(n+1 : ℝ)*angle b) by ring,Real.sin_neg]
    unfold spectralTerm
    ring

lemma boundary_constants (b : ℝ) (hb : 0 < b) :
    1/((Complex.I*(b : ℂ))*(1+Complex.I*(b : ℂ))) =
      ((-1/(1+b^2) : ℝ) : ℂ)-Complex.I*((1/(b*(1+b^2)) : ℝ) : ℂ) ∧
    2/((Complex.I*(b : ℂ))*(1-(Complex.I*(b : ℂ))^2)) =
      -Complex.I*((2/(b*(1+b^2)) : ℝ) : ℂ) := by
  have hB : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hA : (1+b^2 : ℂ) ≠ 0 := by exact_mod_cast (show (1+b^2 : ℝ) ≠ 0 by positivity)
  have hP : 1+Complex.I*(b : ℂ) ≠ 0 := by rw [← root_at_zero b hb]; exact one_add_root_ne b 0
  have hQ : 1-(Complex.I*(b : ℂ))^2=1+(b : ℂ)^2 := by rw [mul_pow,Complex.I_sq]; ring
  constructor
  · push_cast
    field_simp [hB,hA,hP,Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]
    ring
  · rw [hQ]
    push_cast
    field_simp [hB,hA,Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]

lemma boundary_value_parts (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    feynmanBoundaryValue α b=(principalValue α b : ℂ)-Complex.I*
      ((Real.sqrt (Real.pi/α)/(b*(1+b^2))*(1+2*cosineSpectral α b) : ℝ) : ℂ) := by
  unfold feynmanBoundaryValue
  rw [(boundary_constants b hb).1,(boundary_constants b hb).2,boundary_series_parts α b hα]
  unfold principalValue
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hb.ne', show (1+(b : ℂ)^2) ≠ 0 by exact_mod_cast (show (1+b^2 : ℝ) ≠ 0 by positivity)]
  ring_nf
  simp [Complex.I_sq]
  ring

end TangentShiftTask
