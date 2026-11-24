import SimpleTangent.Mass
import SimpleTangent.FeynmanLimit

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set
open scoped Topology
namespace TangentShiftTask

lemma angle_cos_two (b : ℝ) : Real.cos (2*angle b)=(1-b^2)/(1+b^2) := by
  unfold angle
  rw [Real.cos_two_mul,Real.cos_arctan]
  have hs : Real.sqrt (1+b^2)^2=1+b^2 := Real.sq_sqrt (by positivity)
  have hn : Real.sqrt (1+b^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hn]
  nlinarith

lemma angle_sin_two (b : ℝ) : Real.sin (2*angle b)=2*b/(1+b^2) := by
  unfold angle
  rw [Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
  have hs := Real.sq_sqrt (show 0 ≤ 1+b^2 by positivity)
  have hn : Real.sqrt (1+b^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hn]
  rw [hs]

lemma denominator_cos (b x : ℝ) : denominator b x =
    -(1+b^2)/2*(Real.cos (2*x)-Real.cos (2*angle b)) := by
  rw [angle_cos_two,Real.cos_two_mul]
  unfold denominator
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma tangent_kernel_cos (b x : ℝ) (hq : Real.cos (2*x)-Real.cos (2*angle b) ≠ 0) :
    Real.cos x^2/denominator b x =
      -1/(1+b^2)-2/(1+b^2)^2/(Real.cos (2*x)-Real.cos (2*angle b)) := by
  have hA : (1+b^2 : ℝ) ≠ 0 := by positivity
  have hc : Real.cos x^2=(1+Real.cos (2*x))/2 := by nlinarith [Real.cos_two_mul x]
  rw [denominator_cos,hc]
  have hd : -(1+b^2)/2*(Real.cos (2*x)-Real.cos (2*angle b)) ≠ 0 :=
    mul_ne_zero (div_ne_zero (neg_ne_zero.mpr hA) (by norm_num)) hq
  field_simp [hA,hq,hd]
  rw [angle_cos_two]
  field_simp
  ring

lemma boundaryRatio_phase (b : ℝ) : boundaryRatio b=ShiftedCosineTask.unitPhase (-2*angle b) := by
  have hden : (1+Complex.I*(b : ℂ)) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
  unfold boundaryRatio ShiftedCosineTask.unitPhase
  rw [show -2*angle b=-(2*angle b) by ring,Real.cos_neg,Real.sin_neg,angle_cos_two,angle_sin_two]
  push_cast
  field_simp [hden,show (1+b^2 : ℂ) ≠ 0 by exact_mod_cast (show (1+b^2 : ℝ) ≠ 0 by positivity)]
  ring_nf
  simp [Complex.I_sq]
  ring

end TangentShiftTask
