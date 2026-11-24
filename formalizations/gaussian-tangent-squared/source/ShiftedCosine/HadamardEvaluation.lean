import ShiftedCosine.RegulatedPeriodization

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

lemma weight_at_poles (a θ t : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (ht : |t| ≤ Real.pi) (hq : Real.cos t-Real.cos θ=0) : periodWeight a t=periodWeight a θ := by
  have hc : Real.cos |t|=Real.cos t := by
    by_cases hp : 0 ≤ t
    · rw [abs_of_nonneg hp]
    · rw [abs_of_neg (lt_of_not_ge hp),Real.cos_neg]
  have he : |t|=θ := Real.injOn_cos ⟨abs_nonneg _,ht⟩ ⟨hθ.le,hπ.le⟩ (hc.trans (sub_eq_zero.mp hq))
  have hw : periodWeight a |t|=periodWeight a t := by
    by_cases hp : 0 ≤ t
    · rw [abs_of_nonneg hp]
    · rw [abs_of_neg (lt_of_not_ge hp),periodWeight_even]
  rw [← hw,he]

lemma remainder_identity (a θ t : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (ht : |t| ≤ Real.pi) :
    (Real.cos t-Real.cos θ)^2*remainder a θ t=interpolationNumerator a θ t := by
  by_cases hq : Real.cos t-Real.cos θ=0
  · rw [hq]
    have hw := weight_at_poles a θ t hθ hπ ht hq
    simp [interpolationNumerator,hw,hq]
  · unfold remainder
    field_simp

noncomputable def regulatedRemainder (a θ ε t : ℝ) : ℂ :=
  (((Real.cos t-Real.cos θ)^2*remainder a θ t : ℝ) : ℂ)*complexKernel θ ε t

lemma regulatedRemainder_bound (a θ ε t : ℝ) (hε : 0 < ε) :
    ‖regulatedRemainder a θ ε t‖ ≤ ‖remainder a θ t‖ := by
  let q : ℝ := Real.cos t-Real.cos θ
  have he : ((Real.cos t : ℂ)-regulatorZ θ ε)=(q : ℂ)+Complex.I*(ε : ℂ) := by unfold q regulatorZ; push_cast; ring
  have hn : q^2 ≤ ‖(q : ℂ)+Complex.I*(ε : ℂ)‖^2 := by
    have h := Complex.abs_re_le_norm ((q : ℂ)+Complex.I*(ε : ℂ))
    have h : |q| ≤ ‖(q : ℂ)+Complex.I*(ε : ℂ)‖ := by simpa using h
    have h := pow_le_pow_left₀ (abs_nonneg q) h 2
    simpa only [sq_abs] using h
  have hd : 0 < ‖(q : ℂ)+Complex.I*(ε : ℂ)‖^2 := by
    apply sq_pos_of_pos (norm_pos_iff.mpr (feynman_denominator_ne_zero θ ε t hε))
  unfold regulatedRemainder complexKernel
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _),
    norm_div,norm_one,norm_pow,Real.norm_eq_abs]
  have hb : q^2*(1/‖(q : ℂ)+Complex.I*(ε : ℂ)‖^2) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hd).2 hn
  change q^2*|remainder a θ t| *(1/‖(q : ℂ)+Complex.I*(ε : ℂ)‖^2) ≤ |remainder a θ t|
  calc
    _ = |remainder a θ t| *(q^2*(1/‖(q : ℂ)+Complex.I*(ε : ℂ)‖^2)) := by ring
    _ ≤ |remainder a θ t| *1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := mul_one _

lemma regulatedRemainder_tendsto (a θ t : ℝ) :
    Tendsto (fun ε => regulatedRemainder a θ ε t) (𝓝[>] (0 : ℝ)) (𝓝 (remainder a θ t : ℂ)) := by
  by_cases hq : Real.cos t-Real.cos θ=0
  · have hr : remainder a θ t=0 := by simp [remainder,hq]
    simp only [regulatedRemainder,hq,hr,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul,Complex.ofReal_zero]
    exact tendsto_const_nhds
  · have hc : ContinuousAt (fun ε : ℝ => regulatedRemainder a θ ε t) 0 := by
      unfold regulatedRemainder complexKernel regulatorZ
      fun_prop (disch := simpa using Complex.ofReal_ne_zero.mpr hq)
    have he : regulatedRemainder a θ 0 t=(remainder a θ t : ℂ) := by
      unfold regulatedRemainder complexKernel regulatorZ
      simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_sub,Complex.ofReal_zero,mul_zero,sub_zero]
      have hd : (Real.cos t : ℂ)-(Real.cos θ : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_sub]
        exact Complex.ofReal_ne_zero.mpr hq
      field_simp [hd]
    rw [← he]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

lemma regulatedRemainder_integral_tendsto (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun ε => ∫ t in (-Real.pi)..Real.pi,regulatedRemainder a θ ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (hadamardIntegralValue a θ : ℂ)) := by
  have hi := remainder_intervalIntegrable a θ ha hθ hπ
  have he : (∫ t in (-Real.pi)..Real.pi,(remainder a θ t : ℂ))=(hadamardIntegralValue a θ : ℂ) :=
    Complex.ofRealCLM.intervalIntegral_comp_comm hi
  rw [← he]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => ‖remainder a θ t‖)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hm : Measurable (regulatedRemainder a θ ε) := by
      unfold regulatedRemainder
      exact ((Complex.measurable_ofReal.comp ((by fun_prop : Measurable (fun t : ℝ => (Real.cos t-Real.cos θ)^2)).mul
        (remainder_measurable a θ))).mul (complexKernel_continuous θ ε hε).measurable)
    exact hm.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ae_of_all _ (fun t ht => regulatedRemainder_bound a θ ε t hε)
  · exact hi.norm
  · exact ae_of_all _ (fun t ht => regulatedRemainder_tendsto a θ t)

lemma feynmanIntegral_remainder_decomposition (a θ ε : ℝ) (ha : 0 < a) (hθ : 0 < θ)
    (hπ : θ < Real.pi) (hε : 0 < ε) :
    feynmanIntegral a θ ε=
      ((periodWeight a θ : ℂ)+Complex.I*(ε : ℂ)*(periodDerivative a θ/Real.sin θ : ℝ))*
        ((2*Real.pi : ℂ)*regulatorZ θ ε/regulatorD θ ε^3)-
      (periodDerivative a θ/Real.sin θ : ℝ)*(-(2*Real.pi : ℂ)/regulatorD θ ε)+
      (∫ t in (-Real.pi)..Real.pi,regulatedRemainder a θ ε t) := by
  let L : ℂ := ((periodDerivative a θ/Real.sin θ : ℝ) : ℂ)
  let A : ℂ := (periodWeight a θ : ℂ)+Complex.I*(ε : ℂ)*L
  have hK : IntervalIntegrable (complexKernel θ ε) volume (-Real.pi) Real.pi :=
    (complexKernel_continuous θ ε hε).intervalIntegrable _ _
  have hS : IntervalIntegrable (fun t : ℝ => 1/((Real.cos t : ℂ)-regulatorZ θ ε)) volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    have h := feynman_denominator_ne_zero θ ε t hε
    convert h using 1; unfold regulatorZ; push_cast; ring
  have hm : Measurable (regulatedRemainder a θ ε) := by
    have hR := remainder_measurable a θ
    have hK := (complexKernel_continuous θ ε hε).measurable
    unfold regulatedRemainder
    fun_prop
  have hRi : IntegrableOn (regulatedRemainder a θ ε) (Icc (-Real.pi) Real.pi) :=
    (remainder_integrableOn a θ ha hθ hπ).norm.mono' hm.aestronglyMeasurable
      (Eventually.of_forall (fun t => regulatedRemainder_bound a θ ε t hε))
  have hR : IntervalIntegrable (regulatedRemainder a θ ε) volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
    exact hRi.mono_set Ioc_subset_Icc_self
  rw [feynmanIntegral_periodized a θ ε ha hε]
  have hp : (∫ t in (-Real.pi)..Real.pi,(periodWeight a t : ℂ)*complexKernel θ ε t)=
      ∫ t in (-Real.pi)..Real.pi,A*complexKernel θ ε t+
        (-L)*(1/((Real.cos t : ℂ)-regulatorZ θ ε))+regulatedRemainder a θ ε t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht : |t| ≤ Real.pi := by
      rw [uIcc_of_le (by linarith [Real.pi_pos])] at ht
      exact abs_le.mpr ht
    have hi := congrArg Complex.ofReal (remainder_identity a θ t hθ hπ ht)
    unfold interpolationNumerator at hi
    simp only [Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_pow] at hi
    unfold A L regulatedRemainder complexKernel regulatorZ
    simp only [Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_pow]
    have hd := feynman_denominator_ne_zero θ ε t hε
    simp only [Complex.ofReal_sub] at hd
    have hd' : (Real.cos t : ℂ)-((Real.cos θ : ℂ)-Complex.I*(ε : ℂ)) ≠ 0 := by
      convert hd using 1; ring
    simp only [mul_one_div]
    field_simp [hd']
    linear_combination -hi
  rw [hp,intervalIntegral.integral_add ((hK.const_mul A).add (hS.const_mul (-L))) hR,
    intervalIntegral.integral_add (hK.const_mul A) (hS.const_mul (-L)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  unfold complexKernel
  rw [regulated_double_cell θ ε hθ hπ hε,regulated_simple_cell θ ε hθ hπ hε]
  dsimp only [A,L]
  ring

lemma feynmanIntegral_re_tendsto_hadamard (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun ε => (feynmanIntegral a θ ε).re) (𝓝[>] (0 : ℝ)) (𝓝 (hadamardIntegralValue a θ)) := by
  let L : ℝ := periodDerivative a θ/Real.sin θ
  let d : ℂ := -Complex.I*(Real.sin θ : ℂ)
  have hd := regulatorD_tendsto θ hθ hπ
  have hd0 : d ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne')
  have hz : Tendsto (regulatorZ θ) (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos θ : ℂ)) := by
    have hc : ContinuousAt (regulatorZ θ) 0 := by unfold regulatorZ; fun_prop
    simpa [regulatorZ] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hK2 := ((tendsto_const_nhds (x := (2*Real.pi : ℂ))).mul hz).div (hd.pow 3) (pow_ne_zero 3 hd0)
  have hK1 := (tendsto_const_nhds (x := -(2*Real.pi : ℂ))).div hd hd0
  have hid : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hA := (tendsto_const_nhds (x := (periodWeight a θ : ℂ))).add
    ((hid.const_mul Complex.I).mul_const (L : ℂ))
  simp only [mul_zero,zero_mul,add_zero] at hA
  have h := ((hA.mul hK2).sub (hK1.const_mul (L : ℂ))).add
    (regulatedRemainder_integral_tendsto a θ ha hθ hπ)
  have hs : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne'
  have hval2 : (2*Real.pi : ℂ)*(Real.cos θ : ℂ)/d^3=
      ((-2*Real.pi*Real.cos θ/Real.sin θ^3 : ℝ) : ℂ)*Complex.I := by
    dsimp only [d]
    rw [mul_div_assoc,(boundary_constants θ hθ hπ).1]
    push_cast
    ring
  have hval1 : -(2*Real.pi : ℂ)/d=((-2*Real.pi/Real.sin θ : ℝ) : ℂ)*Complex.I := by
    dsimp only [d]
    push_cast
    field_simp [hs]
    ring_nf
    simp [Complex.I_sq]
  rw [hval2,hval1] at h
  have h := Complex.continuous_re.continuousAt.tendsto.comp h
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [feynmanIntegral_remainder_decomposition a θ ε ha hθ hπ hε]
  rfl

lemma hadamardIntegralValue_eq (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    hadamardIntegralValue a θ=finitePartValue a θ := by
  have hf := Complex.continuous_re.continuousAt.tendsto.comp (feynmanIntegral_tendsto a θ ha hθ hπ)
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    zero_mul,mul_zero,sub_zero,add_zero] at hf
  exact tendsto_nhds_unique (feynmanIntegral_re_tendsto_hadamard a θ ha hθ hπ) hf

lemma hadamard_tendsto (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun δ => outerValue a θ δ-2*poleMass a θ/(Real.sin θ^2*δ)) (𝓝[>] (0 : ℝ))
      (𝓝 (finitePartValue a θ)) := by
  rw [← hadamardIntegralValue_eq a θ ha hθ hπ]
  exact hadamard_tendsto_integral a θ ha hθ hπ

end ShiftedCosineTask
