import SimpleTangent.Trigonometry
import SimpleTangent.CutFold

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set
open scoped Topology
namespace TangentShiftTask

noncomputable def transformedKernel (b t : ℝ) : ℝ :=
  (1+Real.cos t)/((1-b^2)-(1+b^2)*Real.cos t)
noncomputable def transformedCell (α b δ : ℝ) (k : ℤ) : ℝ :=
  ShiftedCosineTask.cutIntegral (2*angle b) (2*δ)
    (fun t => ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t)

lemma transformed_point (α b t : ℝ) (k : ℤ) :
    poleIntegrand α b (k*Real.pi+t/2) =
      ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t := by
  have hc : Real.cos (2*((k : ℝ)*Real.pi+t/2))=Real.cos t := by
    rw [show 2*((k : ℝ)*Real.pi+t/2)=t+k*(2*Real.pi) by ring,
      Real.cos_add_int_mul_two_pi]
  have hsq : Real.cos (k*Real.pi+t/2)^2=(1+Real.cos t)/2 := by
    nlinarith [Real.cos_two_mul ((k : ℝ)*Real.pi+t/2)]
  have hd : denominator b (k*Real.pi+t/2)=((1-b^2)-(1+b^2)*Real.cos t)/2 := by
    rw [denominator_cos,hc,angle_cos_two]
    field_simp
    ring
  have hw : weight α (k*Real.pi+t/2)=ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t) := by
    unfold weight ShiftedCosineTask.weight
    congr 1
    ring
  unfold poleIntegrand transformedKernel
  rw [hsq,hd,hw]
  rw [mul_div_assoc,div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]

lemma cell_eq_transformed (α b δ : ℝ) (k : ℤ) :
    cell α b δ k=(1/2 : ℝ)*transformedCell α b δ k := by
  have he (u v : ℝ) :
      (∫ t in u..v, poleIntegrand α b (k*Real.pi+t)) =
        (1/2 : ℝ)*(∫ t in (2*u)..(2*v),
          ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t) := by
    have hpoint (t : ℝ) : poleIntegrand α b (k*Real.pi+t)=
      ShiftedCosineTask.weight (α/4) (2*k*Real.pi+2*t)*transformedKernel b (2*t) := by
      simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using transformed_point α b (2*t) k
    simp_rw [hpoint]
    simpa only [inv_eq_one_div,smul_eq_mul] using intervalIntegral.integral_comp_mul_left
      (a := u) (b := v)
      (fun t : ℝ => ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t)
      (by norm_num : (2 : ℝ) ≠ 0)
  unfold cell transformedCell ShiftedCosineTask.cutIntegral
  rw [he,he,he]
  rw [show 2*(-Real.pi/2)=-Real.pi by ring,
    show 2*(-angle b-δ)=-(2*angle b)-2*δ by ring,
    show 2*(-angle b+δ)=-(2*angle b)+2*δ by ring,
    show 2*(angle b-δ)=2*angle b-2*δ by ring,
    show 2*(angle b+δ)=2*angle b+2*δ by ring,
    show 2*(Real.pi/2)=Real.pi by ring]
  ring

lemma transformed_kernel_eq (b t : ℝ) (hq : Real.cos t-Real.cos (2*angle b) ≠ 0) :
    transformedKernel b t=-1/(1+b^2)-2/(1+b^2)^2/(Real.cos t-Real.cos (2*angle b)) := by
  have htwo : 2*(t/2)=t := by ring
  have he := tangent_kernel_cos b (t/2) (by rw [htwo]; exact hq)
  have hp := transformed_point 0 b t 0
  simp only [poleIntegrand,weight,mul_zero,zero_mul,neg_zero,Real.exp_zero,one_mul,
    Int.cast_zero,zero_add,ShiftedCosineTask.weight,zero_div] at hp
  rw [← hp]
  simpa only [htwo] using he

end TangentShiftTask
