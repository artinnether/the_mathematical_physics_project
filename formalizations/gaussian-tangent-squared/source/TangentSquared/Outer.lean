import TangentSquared.Transformed
import SimpleTangent.Outer

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set
open scoped Topology
namespace TangentSquaredTask

noncomputable def outerValue (α b δ : ℝ) : ℝ := ∑' k : ℤ,cell α b δ k

lemma cell_summable_and_folded (α b δ : ℝ) (hα : 0 < α) (hb : 0 < b)
    (hδ : 0 < δ) (hδθ : δ < angle b) (hδπ : δ < Real.pi/2-angle b) :
    Summable (cell α b δ) ∧
    outerValue α b δ=(1/2 : ℝ)*ShiftedCosineTask.cutIntegral (2*angle b) (2*δ)
      (fun t => ShiftedCosineTask.periodWeight (α/4) t*transformedKernel b t) := by
  have hθ : 0 < 2*angle b := by linarith [TangentShiftTask.angle_pos b hb]
  have hπ : 2*angle b < Real.pi := by linarith [TangentShiftTask.angle_lt_half_pi b]
  obtain ⟨C,hC,hbound⟩ := ShiftedCosineTask.cut_kernel_bounded (2*angle b) (2*δ) hθ hπ (by positivity)
  let K := fun t => (TangentShiftTask.clippedKernel b C t)^2
  have hK : Continuous K := (TangentShiftTask.clippedKernel_continuous b C hC).pow 2
  have he (t : ℝ) (ht : t ∈ ShiftedCosineTask.excludedCell (2*angle b) (2*δ)) : K t=transformedKernel b t :=
    congrArg (fun z : ℝ => z^2) (TangentShiftTask.clippedKernel_eq b δ C t hb hδ hC hbound ht)
  have hf (u v : ℝ) (hu : -Real.pi ≤ u) (hv : v ≤ Real.pi) (huv : u ≤ v)
      (hsub : Icc u v ⊆ ShiftedCosineTask.excludedCell (2*angle b) (2*δ)) :
      Summable (fun k : ℤ => ∫ t in u..v, ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t) ∧
      (∑' k : ℤ,∫ t in u..v, ShiftedCosineTask.weight (α/4) (2*k*Real.pi+t)*transformedKernel b t)=
        ∫ t in u..v,ShiftedCosineTask.periodWeight (α/4) t*transformedKernel b t := by
    have h := ShiftedCosineTask.gaussian_interval_fold (α/4) u v
      ((1/(1+b^2)+4/(1+b^2)^2*(C+1))^2) (by positivity) (by positivity) K hK
      (fun t _ => by
        change ‖(TangentShiftTask.clippedKernel b C t)^2‖ ≤ _
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (TangentShiftTask.clippedKernel_bound b C t hC) 2) hu hv huv
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

end TangentSquaredTask
