import ShiftedCosine.HadamardEvaluation

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def simpleRemainder (a θ t : ℝ) : ℝ :=
  remainder a θ t*(Real.cos t-Real.cos θ)-periodDerivative a θ/Real.sin θ
noncomputable def simplePVIntegral (a θ : ℝ) : ℝ :=
  ∫ t in (-Real.pi)..Real.pi,simpleRemainder a θ t

lemma simple_remainder_identity (a θ t : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (ht : |t| ≤ Real.pi) :
    periodWeight a t=periodWeight a θ+(Real.cos t-Real.cos θ)*simpleRemainder a θ t := by
  have he := remainder_identity a θ t hθ hπ ht
  unfold interpolationNumerator at he
  unfold simpleRemainder
  nlinarith [he]

lemma simple_remainder_integrable (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    IntervalIntegrable (simpleRemainder a θ) volume (-Real.pi) Real.pi := by
  have hr := remainder_intervalIntegrable a θ ha hθ hπ
  have hc : Continuous (fun t : ℝ => Real.cos t-Real.cos θ) := by fun_prop
  exact (hr.mul_continuousOn hc.continuousOn).sub (intervalIntegrable_const)

lemma simple_cut_decomposition (a θ δ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ) :
    cutIntegral θ δ (fun t => periodWeight a t/(Real.cos t-Real.cos θ)) =
      periodWeight a θ*cutIntegral θ δ (fun t => 1/(Real.cos t-Real.cos θ))+
      cutIntegral θ δ (simpleRemainder a θ) := by
  have hK : ContinuousOn (fun t : ℝ => 1/(Real.cos t-Real.cos θ)) (excludedCell θ δ) :=
    ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => cut_cos_ne θ δ t hθ hπ hδ ht)
  have hR : ContinuousOn (simpleRemainder a θ) (excludedCell θ δ) := by
    unfold simpleRemainder remainder interpolationNumerator
    exact ((((periodWeight_continuousOn a ha).mono (excludedCell_subset θ δ hδ hδθ hδπ)).sub continuousOn_const).add
      (continuousOn_const.mul (by fun_prop))).div (by fun_prop)
      (fun t ht => pow_ne_zero 2 (cut_cos_ne θ δ t hθ hπ hδ ht)) |>.mul (by fun_prop) |>.sub continuousOn_const
  have he := cutIntegral_congr θ δ (fun t => periodWeight a t/(Real.cos t-Real.cos θ))
    (fun t => periodWeight a θ*(1/(Real.cos t-Real.cos θ))+simpleRemainder a θ t)
    hθ hπ hδ hδθ hδπ (fun t ht => by
      have hi := simple_remainder_identity a θ t hθ hπ
        (abs_le.mpr ((excludedCell_subset θ δ hδ hδθ hδπ) ht))
      rw [hi]
      field_simp [cut_cos_ne θ δ t hθ hπ hδ ht])
  rw [he,cutIntegral_add θ δ (fun t => periodWeight a θ*(1/(Real.cos t-Real.cos θ))) (simpleRemainder a θ) hθ hπ hδ hδθ hδπ (continuousOn_const.mul hK) hR,
    cutIntegral_const_mul]

lemma simple_cut_tendsto_value (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun δ => cutIntegral θ δ (fun t => periodWeight a t/(Real.cos t-Real.cos θ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (simplePVIntegral a θ)) := by
  have hR := simple_remainder_integrable a θ ha hθ hπ
  have hRi : IntegrableOn (simpleRemainder a θ) (Icc (-Real.pi) Real.pi) := by
    apply (integrableOn_Icc_iff_integrableOn_Ioc (by simp)).mpr
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).mp hR
  have h := ((simple_cut_tendsto θ hθ hπ).const_mul (periodWeight a θ)).add
    (integrable_cut_tendsto (simpleRemainder a θ) θ hθ hπ hRi)
  simp only [mul_zero,zero_add] at h
  apply h.congr'
  have hltθ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < θ :=
    (eventually_lt_nhds hθ).filter_mono nhdsWithin_le_nhds
  have hltπ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi-θ :=
    (eventually_lt_nhds (sub_pos.mpr hπ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hltθ,hltπ] with δ hδ hδθ hδπ
  exact (simple_cut_decomposition a θ δ ha hθ hπ hδ hδθ hδπ).symm

noncomputable def simpleRegulatedRemainder (a θ ε t : ℝ) : ℂ :=
  (((Real.cos t-Real.cos θ)*simpleRemainder a θ t : ℝ) : ℂ)/
    ((Real.cos t : ℂ)-regulatorZ θ ε)

lemma simple_regulated_bound (a θ ε t : ℝ) (hε : 0 < ε) :
    ‖simpleRegulatedRemainder a θ ε t‖ ≤ ‖simpleRemainder a θ t‖ := by
  let q : ℝ := Real.cos t-Real.cos θ
  have hd : (Real.cos t : ℂ)-regulatorZ θ ε=(q : ℂ)+Complex.I*(ε : ℂ) := by
    unfold q regulatorZ; push_cast; ring
  have hb : |q| ≤ ‖(q : ℂ)+Complex.I*(ε : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm ((q : ℂ)+Complex.I*(ε : ℂ))
  have hz : 0 < ‖(q : ℂ)+Complex.I*(ε : ℂ)‖ :=
    norm_pos_iff.mpr (feynman_denominator_ne_zero θ ε t hε)
  unfold simpleRegulatedRemainder
  rw [hd,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  change |q| *|simpleRemainder a θ t|/‖(q : ℂ)+Complex.I*(ε : ℂ)‖ ≤ _
  apply (div_le_iff₀ hz).mpr
  simpa [Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_right hb (abs_nonneg (simpleRemainder a θ t))

lemma simple_regulated_integral_tendsto (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun ε => ∫ t in (-Real.pi)..Real.pi,simpleRegulatedRemainder a θ ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (simplePVIntegral a θ : ℂ)) := by
  have hi := simple_remainder_integrable a θ ha hθ hπ
  have he := Complex.ofRealCLM.intervalIntegral_comp_comm hi
  change (∫ t in (-Real.pi)..Real.pi,(simpleRemainder a θ t : ℂ))=(simplePVIntegral a θ : ℂ) at he
  rw [← he]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => ‖simpleRemainder a θ t‖)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hm : Measurable (simpleRegulatedRemainder a θ ε) := by
      unfold simpleRegulatedRemainder simpleRemainder
      have hr := remainder_measurable a θ
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ae_of_all _ (fun t ht => simple_regulated_bound a θ ε t hε)
  · exact hi.norm
  · have hp : ∀ᵐ t : ℝ ∂volume, t ∉ ({θ,-θ} : Set ℝ) := by
      rw [ae_iff]
      simp only [not_not]
      change volume ({θ,-θ} : Set ℝ)=0
      exact (Set.Finite.measure_zero (by simp : ({θ,-θ} : Set ℝ).Finite) volume)
    filter_upwards [hp] with t htp ht
    have htbound : |t| ≤ Real.pi := by
      rw [uIoc_of_le (by linarith [Real.pi_pos])] at ht
      exact abs_le.mpr ⟨ht.1.le,ht.2⟩
    have hq : Real.cos t-Real.cos θ ≠ 0 := by
      intro hq
      have hc : Real.cos |t|=Real.cos t := by
        by_cases hp : 0 ≤ t
        · rw [abs_of_nonneg hp]
        · rw [abs_of_neg (lt_of_not_ge hp),Real.cos_neg]
      have he : |t|=θ := Real.injOn_cos ⟨abs_nonneg _,htbound⟩ ⟨hθ.le,hπ.le⟩ (hc.trans (sub_eq_zero.mp hq))
      have he : t=θ ∨ t=-θ := by
        by_cases hp : 0 ≤ t
        · left; simpa [abs_of_nonneg hp] using he
        · right; rw [abs_of_neg (lt_of_not_ge hp)] at he; linarith
      exact htp (by simpa using he)
    have hc : ContinuousAt (fun ε : ℝ => simpleRegulatedRemainder a θ ε t) 0 := by
      unfold simpleRegulatedRemainder regulatorZ
      fun_prop (disch := simpa using Complex.ofReal_ne_zero.mpr hq)
    have hv : simpleRegulatedRemainder a θ 0 t=(simpleRemainder a θ t : ℂ) := by
      unfold simpleRegulatedRemainder regulatorZ
      simp only [Complex.ofReal_zero,mul_zero,sub_zero,← Complex.ofReal_sub,Complex.ofReal_mul]
      exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hq)
    rw [← hv]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

end ShiftedCosineTask
