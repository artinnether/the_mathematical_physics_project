import SimpleTangent.Outer
import SimpleTangent.SimpleEvaluation

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace TangentShiftTask

lemma outerValue_decomposition (α b δ : ℝ) (hα : 0 < α) (hb : 0 < b)
    (hδ : 0 < δ) (hδθ : δ < angle b) (hδπ : δ < Real.pi/2-angle b) :
    outerValue α b δ=(1/2 : ℝ)*
      (-1/(1+b^2)*ShiftedCosineTask.cutIntegral (2*angle b) (2*δ)
        (ShiftedCosineTask.periodWeight (α/4))-
       2/(1+b^2)^2*ShiftedCosineTask.cutIntegral (2*angle b) (2*δ)
        (fun t => ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b)))) := by
  have hθ : 0 < 2*angle b := by linarith [angle_pos b hb]
  have hπ : 2*angle b < Real.pi := by linarith [angle_lt_half_pi b]
  have hW := (ShiftedCosineTask.periodWeight_continuousOn (α/4) (by positivity)).mono
    (ShiftedCosineTask.excludedCell_subset (2*angle b) (2*δ) (by positivity) (by linarith) (by linarith))
  have hQ : ContinuousOn (fun t => ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b)))
      (ShiftedCosineTask.excludedCell (2*angle b) (2*δ)) :=
    hW.div (by fun_prop) (fun t ht => ShiftedCosineTask.cut_cos_ne (2*angle b) (2*δ) t hθ hπ (by positivity) ht)
  rw [(cell_summable_and_folded α b δ hα hb hδ hδθ hδπ).2]
  have he := ShiftedCosineTask.cutIntegral_congr (2*angle b) (2*δ)
    (fun t => ShiftedCosineTask.periodWeight (α/4) t*transformedKernel b t)
    (fun t => (-1/(1+b^2))*ShiftedCosineTask.periodWeight (α/4) t+
      (-2/(1+b^2)^2)*(ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b))))
    hθ hπ (by positivity) (by linarith) (by linarith) (fun t ht => by
      rw [transformed_kernel_eq b t (ShiftedCosineTask.cut_cos_ne (2*angle b) (2*δ) t hθ hπ (by positivity) ht)]
      ring)
  rw [he,ShiftedCosineTask.cutIntegral_add (2*angle b) (2*δ)
    (fun t => (-1/(1+b^2))*ShiftedCosineTask.periodWeight (α/4) t)
    (fun t => (-2/(1+b^2)^2)*(ShiftedCosineTask.periodWeight (α/4) t/(Real.cos t-Real.cos (2*angle b))))
    hθ hπ (by positivity) (by linarith) (by linarith) (continuousOn_const.mul hW) (continuousOn_const.mul hQ),
    ShiftedCosineTask.cutIntegral_const_mul,ShiftedCosineTask.cutIntegral_const_mul]
  ring

lemma periodWeight_integral (a : ℝ) (ha : 0 < a) :
    (∫ t in (-Real.pi)..Real.pi,ShiftedCosineTask.periodWeight a t)=Real.sqrt (Real.pi/a) := by
  have h := ShiftedCosineTask.gaussian_fold_bounded a ha (fun _ => (1 : ℂ)) continuous_const 1
    (by norm_num) (fun _ => by simp) (fun _ _ => rfl)
  simp only [mul_one] at h
  have hcW : ContinuousOn (ShiftedCosineTask.periodWeight a) (uIcc (-Real.pi) Real.pi) := by
    rw [uIcc_of_le (by linarith [Real.pi_pos])]
    exact ShiftedCosineTask.periodWeight_continuousOn a ha
  have hi : IntervalIntegrable (ShiftedCosineTask.periodWeight a) volume (-Real.pi) Real.pi := hcW.intervalIntegrable
  have hc := Complex.ofRealCLM.intervalIntegral_comp_comm hi
  change (∫ t in (-Real.pi)..Real.pi,(ShiftedCosineTask.periodWeight a t : ℂ))=
    ((∫ t in (-Real.pi)..Real.pi,ShiftedCosineTask.periodWeight a t : ℝ) : ℂ) at hc
  have hg : (∫ t : ℝ,(ShiftedCosineTask.weight a t : ℂ))=(Real.sqrt (Real.pi/a) : ℂ) := by
    rw [integral_complex_ofReal]
    have hG : (∫ t : ℝ,ShiftedCosineTask.weight a t)=Real.sqrt (Real.pi/a) := integral_gaussian a
    rw [hG]
  rw [hg,hc] at h
  exact (Complex.ofReal_injective h).symm

lemma outerValue_tendsto (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Tendsto (outerValue α b) (𝓝[>] (0 : ℝ)) (𝓝 (principalValue α b)) := by
  let θ := 2*angle b
  let a := α/4
  have hθ : 0 < θ := by dsimp [θ]; linarith [angle_pos b hb]
  have hπ : θ < Real.pi := by dsimp [θ]; linarith [angle_lt_half_pi b]
  have ha : 0 < a := by dsimp [a]; positivity
  have hW : IntegrableOn (ShiftedCosineTask.periodWeight a) (Icc (-Real.pi) Real.pi) :=
    (ShiftedCosineTask.periodWeight_continuousOn a ha).integrableOn_Icc
  have hscale : Tendsto (fun δ : ℝ => 2*δ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun δ : ℝ => 2*δ) (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℝ)*0)))
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < 2*δ
      exact mul_pos (by norm_num) hδ
  have h1 := (ShiftedCosineTask.integrable_cut_tendsto (ShiftedCosineTask.periodWeight a) θ hθ hπ hW).comp hscale
  rw [periodWeight_integral a ha] at h1
  have h2 := (ShiftedCosineTask.simple_cut_tendsto_value a θ ha hθ hπ).comp hscale
  have h := ((h1.const_mul (-1/(1+b^2))).sub (h2.const_mul (2/(1+b^2)^2))).const_mul (1/2 : ℝ)
  have hv : (1/2 : ℝ)*(-1/(1+b^2)*Real.sqrt (Real.pi/a)-
      2/(1+b^2)^2*ShiftedCosineTask.simplePVIntegral a θ)=principalValue α b := by
    rw [ShiftedCosineTask.simplePVIntegral_eq_series a θ ha hθ hπ]
    have hs : Real.sqrt (Real.pi/a)=2*Real.sqrt (Real.pi/α) := by
      dsimp [a]
      rw [show Real.pi/(α/4)=4*(Real.pi/α) by ring,Real.sqrt_mul (by norm_num),
        show (4 : ℝ)=(2 : ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
    have ht : Real.sin θ=2*b/(1+b^2) := angle_sin_two b
    have hsum : (∑' n : ℕ,ShiftedCosineTask.gaussianTerm a n*Real.sin ((n+1 : ℝ)*θ))=∑' n : ℕ,spectralTerm α b n := by
      apply tsum_congr
      intro n
      unfold ShiftedCosineTask.gaussianTerm spectralTerm
      dsimp [a,θ]
      rw [mul_comm]
      congr 1
      · congr 1
        ring
      · congr 1
        ring
    rw [hs,ht,hsum]
    unfold principalValue
    field_simp [hb.ne']
    ring
  rw [hv] at h
  apply h.congr'
  have hlt1 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < angle b :=
    (eventually_lt_nhds (angle_pos b hb)).filter_mono nhdsWithin_le_nhds
  have hlt2 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi/2-angle b :=
    (eventually_lt_nhds (sub_pos.mpr (angle_lt_half_pi b))).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hlt1,hlt2] with δ hδ hδ1 hδ2
  exact (outerValue_decomposition α b δ hα hb hδ hδ1 hδ2).symm

end TangentShiftTask
