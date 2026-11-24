import SimpleTangent.Transformed

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set
open scoped Topology
namespace TangentShiftTask

noncomputable def clippedKernel (b C t : ℝ) : ℝ :=
  -1/(1+b^2)-2/(1+b^2)^2*(Real.cos t-Real.cos (2*angle b))/
    max ((Real.cos t-Real.cos (2*angle b))^2) (1/(C+1))

lemma clippedKernel_continuous (b C : ℝ) (hC : 0 ≤ C) : Continuous (clippedKernel b C) := by
  unfold clippedKernel
  apply Continuous.sub continuous_const
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact (lt_of_lt_of_le (by positivity : 0 < 1/(C+1)) (le_max_right _ _)).ne'

lemma clippedKernel_bound (b C t : ℝ) (hC : 0 ≤ C) :
    ‖clippedKernel b C t‖ ≤ 1/(1+b^2)+4/(1+b^2)^2*(C+1) := by
  have hd : 0 < max ((Real.cos t-Real.cos (2*angle b))^2) (1/(C+1)) :=
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hq : ‖Real.cos t-Real.cos (2*angle b)‖ ≤ 2 := by
    have h := add_le_add (Real.abs_cos_le_one t) (Real.abs_cos_le_one (2*angle b))
    exact (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs,show (1 : ℝ)+1=2 by norm_num] using h)
  have hr : 1/max ((Real.cos t-Real.cos (2*angle b))^2) (1/(C+1)) ≤ C+1 := by
    apply (div_le_iff₀ hd).mpr
    have he := mul_le_mul_of_nonneg_left (le_max_right ((Real.cos t-Real.cos (2*angle b))^2) (1/(C+1)))
      (show 0 ≤ C+1 by positivity)
    have hc : (C+1)*(1/(C+1))=1 := by field_simp
    nlinarith
  unfold clippedKernel
  apply (norm_sub_le _ _).trans
  rw [norm_div,norm_neg,norm_one,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 1+b^2),
    norm_div,norm_mul,norm_div,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<2),
    norm_pow,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 1+b^2),
    Real.norm_eq_abs]
  rw [Real.norm_eq_abs,abs_of_pos hd]
  have hm := mul_le_mul hq hr (by positivity : 0 ≤ 1/max ((Real.cos t-Real.cos (2*angle b))^2) (1/(C+1))) (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Real.norm_eq_abs,div_eq_mul_inv] at hm ⊢
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2/(1+b^2)^2 by positivity)
  convert add_le_add_left hh (1/(1+b^2)) using 1 <;> simp only [div_eq_mul_inv,one_mul] <;> ring

lemma clippedKernel_eq (b δ C t : ℝ) (hb : 0 < b) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ ShiftedCosineTask.excludedCell (2*angle b) (2*δ),
      ‖1/(Real.cos t-Real.cos (2*angle b))^2‖ ≤ C)
    (ht : t ∈ ShiftedCosineTask.excludedCell (2*angle b) (2*δ)) :
    clippedKernel b C t=transformedKernel b t := by
  have hθ : 0 < 2*angle b := by linarith [angle_pos b hb]
  have hπ : 2*angle b < Real.pi := by linarith [angle_lt_half_pi b]
  have hq := ShiftedCosineTask.cut_cos_ne (2*angle b) (2*δ) t hθ hπ (by positivity) ht
  have hf : 1/(C+1) ≤ (Real.cos t-Real.cos (2*angle b))^2 := by
    have hc := hbound t ht
    rw [Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 1/(Real.cos t-Real.cos (2*angle b))^2)] at hc
    have he := (div_le_iff₀ (sq_pos_of_ne_zero hq)).mp hc
    apply (div_le_iff₀ (by positivity : 0 < C+1)).mpr
    nlinarith [sq_nonneg (Real.cos t-Real.cos (2*angle b))]
  unfold clippedKernel
  rw [max_eq_left hf,transformed_kernel_eq b t hq]
  field_simp [hq]

noncomputable def outerValue (α b δ : ℝ) : ℝ := ∑' k : ℤ,cell α b δ k

lemma cell_summable_and_folded (α b δ : ℝ) (hα : 0 < α) (hb : 0 < b)
    (hδ : 0 < δ) (hδθ : δ < angle b) (hδπ : δ < Real.pi/2-angle b) :
    Summable (cell α b δ) ∧
    outerValue α b δ=(1/2 : ℝ)*ShiftedCosineTask.cutIntegral (2*angle b) (2*δ)
      (fun t => ShiftedCosineTask.periodWeight (α/4) t*transformedKernel b t) := by
  have hθ : 0 < 2*angle b := by linarith [angle_pos b hb]
  have hπ : 2*angle b < Real.pi := by linarith [angle_lt_half_pi b]
  obtain ⟨C,hC,hbound⟩ := ShiftedCosineTask.cut_kernel_bounded (2*angle b) (2*δ) hθ hπ (by positivity)
  let K := clippedKernel b C
  have hK : Continuous K := clippedKernel_continuous b C hC
  have he (t : ℝ) (ht : t ∈ ShiftedCosineTask.excludedCell (2*angle b) (2*δ)) : K t=transformedKernel b t :=
    clippedKernel_eq b δ C t hb hδ hC hbound ht
  have hf (u v : ℝ) (hu : -Real.pi ≤ u) (hv : v ≤ Real.pi) (huv : u ≤ v)
      (hsub : Icc u v ⊆ ShiftedCosineTask.excludedCell (2*angle b) (2*δ)) :
      Summable (fun k : ℤ => ∫ t in u..v, ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t) ∧
      (∑' k : ℤ,∫ t in u..v, ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t)=
        ∫ t in u..v,ShiftedCosineTask.periodWeight (α/4) t*transformedKernel b t := by
    have h := ShiftedCosineTask.gaussian_interval_fold (α/4) u v
      (1/(1+b^2)+4/(1+b^2)^2*(C+1)) (by positivity) (by positivity) K hK
      (fun t _ => clippedKernel_bound b C t hC) hu hv huv
    have hi (k : ℤ) : (∫ t in u..v,ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*K t)=
        ∫ t in u..v,ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le huv] at ht
      dsimp only
      rw [he t (hsub ht)]
    have hj : (∫ t in u..v,ShiftedCosineTask.periodWeight (α/4) t*K t)=
        ∫ t in u..v,ShiftedCosineTask.periodWeight (α/4) t*transformedKernel b t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le huv] at ht
      dsimp only
      rw [he t (hsub ht)]
    simpa only [hi,hj] using h
  have hl := hf (-Real.pi) (-(2*angle b)-2*δ) le_rfl (by linarith) (by linarith) (fun t ht => Or.inl (Or.inl ht))
  have hm := hf (-(2*angle b)+2*δ) (2*angle b-2*δ) (by linarith) (by linarith) (by linarith) (fun t ht => Or.inl (Or.inr ht))
  have hr := hf (2*angle b+2*δ) Real.pi (by linarith) le_rfl (by linarith) (fun t ht => Or.inr ht)
  have hs := ((hl.1.add hm.1).add hr.1).mul_left (1/2 : ℝ)
  constructor
  · apply hs.congr
    intro k
    exact (cell_eq_transformed α b δ k).symm
  · unfold outerValue
    simp_rw [cell_eq_transformed,transformedCell,ShiftedCosineTask.cutIntegral]
    rw [tsum_mul_left,(hl.1.add hm.1).tsum_add hr.1,hl.1.tsum_add hm.1,hl.2,hm.2,hr.2]

lemma truncation_tendsto (α b δ : ℝ) (hα : 0 < α) (hb : 0 < b)
    (hδ : 0 < δ) (hδθ : δ < angle b) (hδπ : δ < Real.pi/2-angle b) :
    Tendsto (truncation α b δ) atTop (𝓝 (outerValue α b δ)) :=
  (cell_summable_and_folded α b δ hα hb hδ hδθ hδπ).1.hasSum.comp
    (Finset.tendsto_Icc_neg (R := ℤ))

end TangentShiftTask
