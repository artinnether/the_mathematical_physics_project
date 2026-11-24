import TangentSquared.Basic

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set
open scoped Topology
namespace TangentSquaredTask

noncomputable def transformedKernel (b t : ℝ) : ℝ :=
  (TangentShiftTask.transformedKernel b t)^2
noncomputable def transformedCell (α b δ : ℝ) (k : ℤ) : ℝ :=
  ShiftedCosineTask.cutIntegral (2*angle b) (2*δ)
    (fun t => ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t)

lemma transformed_point (α b t : ℝ) (k : ℤ) :
    poleIntegrand α b (k*Real.pi+t/2) =
      ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t := by
  have hq := TangentShiftTask.transformed_point 0 b t k
  simp only [TangentShiftTask.poleIntegrand,TangentShiftTask.weight,zero_mul,neg_zero,Real.exp_zero,one_mul,ShiftedCosineTask.weight,zero_div] at hq
  have hw : weight α (k*Real.pi+t/2)=ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t) := by
    unfold weight ShiftedCosineTask.weight
    congr 1
    ring
  unfold poleIntegrand transformedKernel
  rw [← hq,div_pow,hw]
  change _ = _
  unfold denominator TangentShiftTask.denominator
  ring

lemma transformed_kernel_decomposition (b t : ℝ)
    (hq : Real.cos t-Real.cos (2*angle b) ≠ 0) :
    transformedKernel b t =
      1/(1+b^2)^2 + 4/(1+b^2)^3/(Real.cos t-Real.cos (2*angle b)) +
      4/(1+b^2)^4/(Real.cos t-Real.cos (2*angle b))^2 := by
  unfold transformedKernel
  rw [TangentShiftTask.transformed_kernel_eq b t hq]
  change (-1/(1+b^2)-2/(1+b^2)^2/(Real.cos t-Real.cos (2*angle b)))^2 = _
  field_simp [hq,show (1 : ℝ)+b^2 ≠ 0 by positivity]
  ring

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

end TangentSquaredTask
