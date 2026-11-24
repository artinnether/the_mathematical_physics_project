import TangentSquared.Outer
import TangentSquared.Series

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace TangentSquaredTask

lemma outerValue_decomposition (α b δ : ℝ) (hα : 0 < α) (hb : 0 < b)
    (hδ : 0 < δ) (hδθ : δ < angle b) (hδπ : δ < Real.pi/2-angle b) :
    outerValue α b δ=(1/2 : ℝ)*
      (1/(1+b^2)^2*ShiftedCosineTask.cutIntegral (2*angle b) (2*δ)
        (ShiftedCosineTask.periodWeight (α/4)) +
       4/(1+b^2)^3*ShiftedCosineTask.cutIntegral (2*angle b) (2*δ)
        (fun t => ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b))) +
       4/(1+b^2)^4*ShiftedCosineTask.outerValue (α/4) (2*angle b) (2*δ)) := by
  have hθ : 0 < 2*angle b := by linarith [TangentShiftTask.angle_pos b hb]
  have hπ : 2*angle b < Real.pi := by linarith [TangentShiftTask.angle_lt_half_pi b]
  have hW := (ShiftedCosineTask.periodWeight_continuousOn (α/4) (by positivity)).mono
    (ShiftedCosineTask.excludedCell_subset (2*angle b) (2*δ) (by positivity) (by linarith) (by linarith))
  have hQ : ContinuousOn (fun t => ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b)))
      (ShiftedCosineTask.excludedCell (2*angle b) (2*δ)) :=
    hW.div (by fun_prop) (fun t ht => ShiftedCosineTask.cut_cos_ne (2*angle b) (2*δ) t hθ hπ (by positivity) ht)
  have hQ2 : ContinuousOn (fun t => ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b))^2)
      (ShiftedCosineTask.excludedCell (2*angle b) (2*δ)) :=
    hW.div (by fun_prop) (fun t ht => pow_ne_zero 2 (ShiftedCosineTask.cut_cos_ne (2*angle b) (2*δ) t hθ hπ (by positivity) ht))
  rw [(cell_summable_and_folded α b δ hα hb hδ hδθ hδπ).2]
  have he := ShiftedCosineTask.cutIntegral_congr (2*angle b) (2*δ)
    (fun t => ShiftedCosineTask.periodWeight (α/4) t*transformedKernel b t)
    (fun t => (1/(1+b^2)^2)*ShiftedCosineTask.periodWeight (α/4) t +
      (4/(1+b^2)^3)*(ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b))) +
      (4/(1+b^2)^4)*(ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b))^2))
    hθ hπ (by positivity) (by linarith) (by linarith) (fun t ht => by
      rw [transformed_kernel_decomposition b t (ShiftedCosineTask.cut_cos_ne (2*angle b) (2*δ) t hθ hπ (by positivity) ht)]
      ring)
  rw [he,ShiftedCosineTask.cutIntegral_add (2*angle b) (2*δ)
    (fun t => (1/(1+b^2)^2)*ShiftedCosineTask.periodWeight (α/4) t +
      (4/(1+b^2)^3)*(ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b))))
    (fun t => (4/(1+b^2)^4)*(ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b))^2))
    hθ hπ (by positivity) (by linarith) (by linarith)
    ((continuousOn_const.mul hW).add (continuousOn_const.mul hQ)) (continuousOn_const.mul hQ2),
    ShiftedCosineTask.cutIntegral_add (2*angle b) (2*δ)
    (fun t => (1/(1+b^2)^2)*ShiftedCosineTask.periodWeight (α/4) t)
    (fun t => (4/(1+b^2)^3)*(ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b))))
    hθ hπ (by positivity) (by linarith) (by linarith) (continuousOn_const.mul hW) (continuousOn_const.mul hQ),
    ShiftedCosineTask.cutIntegral_const_mul,ShiftedCosineTask.cutIntegral_const_mul,
    ShiftedCosineTask.cutIntegral_const_mul,
    ← ShiftedCosineTask.outerValue_periodized (α/4) (2*angle b) (2*δ) (by positivity) hθ hπ
      (by positivity) (by linarith) (by linarith)]


lemma poleMass_transformed (α b : ℝ) :
    ShiftedCosineTask.poleMass (α/4) (2*angle b)=poleMass α b := by
  unfold ShiftedCosineTask.poleMass poleMass
  apply tsum_congr
  intro k
  unfold ShiftedCosineTask.weight weight
  congr 1 <;> congr 1 <;> ring

lemma subtraction_transformed (α b δ : ℝ) (hb : 0 < b) :
    (1/2 : ℝ)*(4/(1+b^2)^4)*
      (2*ShiftedCosineTask.poleMass (α/4) (2*angle b)/(Real.sin (2*angle b)^2*(2*δ))) =
      subtraction α b δ := by
  rw [poleMass_transformed,TangentShiftTask.angle_sin_two]
  unfold subtraction
  field_simp [hb.ne',show (1 : ℝ)+b^2 ≠ 0 by positivity]
  ring

noncomputable def decomposedValue (α b : ℝ) : ℝ :=
  (1/2 : ℝ)*(1/(1+b^2)^2*Real.sqrt (Real.pi/(α/4)) +
    4/(1+b^2)^3*ShiftedCosineTask.simplePVIntegral (α/4) (2*angle b) +
    4/(1+b^2)^4*ShiftedCosineTask.finitePartValue (α/4) (2*angle b))

lemma hadamard_tendsto_decomposed (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Tendsto (fun δ => outerValue α b δ-subtraction α b δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (decomposedValue α b)) := by
  have hθ : 0 < 2*angle b := by linarith [TangentShiftTask.angle_pos b hb]
  have hπ : 2*angle b < Real.pi := by linarith [TangentShiftTask.angle_lt_half_pi b]
  have ha : 0 < α/4 := by positivity
  have hscale : Tendsto (fun δ : ℝ => 2*δ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun δ : ℝ => 2*δ) (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℝ)*0)))
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < 2*δ
      exact mul_pos (by norm_num) hδ
  have hi : IntegrableOn (ShiftedCosineTask.periodWeight (α/4)) (Icc (-Real.pi) Real.pi) :=
    (ShiftedCosineTask.periodWeight_continuousOn (α/4) ha).integrableOn_Icc
  have h0 := (ShiftedCosineTask.integrable_cut_tendsto _ _ hθ hπ hi).comp hscale
  rw [TangentShiftTask.periodWeight_integral (α/4) ha] at h0
  have h1 := (ShiftedCosineTask.simple_cut_tendsto_value (α/4) (2*angle b) ha hθ hπ).comp hscale
  have h2 := (ShiftedCosineTask.hadamard_tendsto (α/4) (2*angle b) ha hθ hπ).comp hscale
  have h := (((h0.const_mul (1/(1+b^2)^2)).add (h1.const_mul (4/(1+b^2)^3))).add
    (h2.const_mul (4/(1+b^2)^4))).const_mul (1/2 : ℝ)
  apply h.congr'
  have hl1 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < angle b :=
    (eventually_lt_nhds (TangentShiftTask.angle_pos b hb)).filter_mono nhdsWithin_le_nhds
  have hl2 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi/2-angle b :=
    (eventually_lt_nhds (sub_pos.mpr (TangentShiftTask.angle_lt_half_pi b))).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hl1,hl2] with δ hδ hδ1 hδ2
  dsimp only [Function.comp_def]
  rw [outerValue_decomposition α b δ hα hb hδ hδ1 hδ2]
  rw [← subtraction_transformed α b δ hb]
  ring

end TangentSquaredTask
