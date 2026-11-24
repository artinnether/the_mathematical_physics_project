import SimpleTangent.GenericFold
import ShiftedCosine.FeynmanLimit

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def simpleWhole (a θ ε : ℝ) : ℂ :=
  ∫ t : ℝ,(weight a t : ℂ)/((Real.cos t : ℂ)-regulatorZ θ ε)
noncomputable def simpleCell (a θ ε : ℝ) : ℂ :=
  ∫ t in (-Real.pi)..Real.pi,(periodWeight a t : ℂ)/((Real.cos t : ℂ)-regulatorZ θ ε)

lemma simple_kernel_continuous (θ ε : ℝ) (hε : 0 < ε) :
    Continuous (fun t : ℝ => 1/((Real.cos t : ℂ)-regulatorZ θ ε)) := by
  apply Continuous.div continuous_const (by unfold regulatorZ; fun_prop)
  intro t
  convert feynman_denominator_ne_zero θ ε t hε using 1; unfold regulatorZ; push_cast; ring

lemma simple_kernel_bound (θ ε t : ℝ) (hε : 0 < ε) :
    ‖1/((Real.cos t : ℂ)-regulatorZ θ ε)‖ ≤ 1/ε := by
  have hb := Complex.abs_im_le_norm ((Real.cos t : ℂ)-regulatorZ θ ε)
  have hd : ε ≤ ‖(Real.cos t : ℂ)-regulatorZ θ ε‖ := by
    simpa [regulatorZ,abs_of_pos hε] using hb
  rw [norm_div,norm_one]
  exact one_div_le_one_div_of_le hε hd

lemma simpleWhole_eq_cell (a θ ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    simpleWhole a θ ε=simpleCell a θ ε := by
  unfold simpleWhole simpleCell
  simpa only [div_eq_mul_inv,one_div,one_mul] using gaussian_fold_bounded a ha _ (simple_kernel_continuous θ ε hε) (1/ε) (by positivity)
    (fun t => simple_kernel_bound θ ε t hε) (fun t k => by rw [Real.cos_add_int_mul_two_pi])

lemma simpleWhole_eq_series (a θ ε : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) (hε : 0 < ε) :
    simpleWhole a θ ε=-(Real.sqrt (Real.pi/a) : ℂ)/regulatorD θ ε*
      (1+2*∑' n : ℕ,regulatorQ θ ε^(n+1)*(gaussianTerm a n : ℂ)) := by
  have hb := complex_geometric_summable (regulatorQ θ ε) (regulatorQ_norm_lt_one θ ε hθ hπ hε)
  have hw : Integrable (fun t : ℝ => (weight a t : ℂ)) := (integrable_exp_neg_mul_sq ha).ofReal
  have hB := gaussian_complexSeries_integrable a ha _ hb
  have he (t : ℝ) : (weight a t : ℂ)/((Real.cos t : ℂ)-regulatorZ θ ε)=
      -(1/regulatorD θ ε)*((weight a t : ℂ)+2*((weight a t : ℂ)*complexCosineSeries (fun n => regulatorQ θ ε^(n+1)) t)) := by
    rw [div_eq_mul_one_div,simple_kernel_fourier θ ε t hθ hπ hε]
    ring
  unfold simpleWhole
  simp_rw [he]
  rw [integral_const_mul,integral_add hw (hB.const_mul (2 : ℂ)),integral_const_mul,
    gaussian_complexSeries_integral a ha _ hb,integral_complex_ofReal]
  have hg : (∫ t : ℝ,weight a t)=Real.sqrt (Real.pi/a) := integral_gaussian a
  rw [hg]
  ring

lemma simpleCell_decomposition (a θ ε : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) (hε : 0 < ε) :
    simpleCell a θ ε=(periodWeight a θ : ℂ)*(-(2*Real.pi : ℂ)/regulatorD θ ε)+
      ∫ t in (-Real.pi)..Real.pi,simpleRegulatedRemainder a θ ε t := by
  have hK : IntervalIntegrable (fun t : ℝ => 1/((Real.cos t : ℂ)-regulatorZ θ ε)) volume (-Real.pi) Real.pi :=
    (simple_kernel_continuous θ ε hε).intervalIntegrable _ _
  have hR : IntervalIntegrable (simpleRegulatedRemainder a θ ε) volume (-Real.pi) Real.pi := by
    apply (simple_remainder_integrable a θ ha hθ hπ).mono_fun
    · have hm : Measurable (simpleRegulatedRemainder a θ ε) := by
        unfold simpleRegulatedRemainder simpleRemainder
        have hr := remainder_measurable a θ
        fun_prop
      exact hm.aestronglyMeasurable
    · exact ae_of_all _ (fun t => simple_regulated_bound a θ ε t hε)
  have he : simpleCell a θ ε=
      ∫ t in (-Real.pi)..Real.pi,(periodWeight a θ : ℂ)*(1/((Real.cos t : ℂ)-regulatorZ θ ε))+simpleRegulatedRemainder a θ ε t := by
    unfold simpleCell
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith [Real.pi_pos])] at ht
    dsimp only
    rw [simple_remainder_identity a θ t hθ hπ (abs_le.mpr ht)]
    unfold simpleRegulatedRemainder
    push_cast
    ring
  rw [he,intervalIntegral.integral_add (hK.const_mul _) hR,
    intervalIntegral.integral_const_mul,regulated_simple_cell θ ε hθ hπ hε]

lemma simplePVIntegral_eq_series (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    simplePVIntegral a θ=2*Real.sqrt (Real.pi/a)/Real.sin θ*
      ∑' n : ℕ,gaussianTerm a n*Real.sin ((n+1 : ℝ)*θ) := by
  have hd := regulatorD_tendsto θ hθ hπ
  have hdz : -Complex.I*(Real.sin θ : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne')
  have hl : Tendsto (simpleCell a θ) (𝓝[>] (0 : ℝ))
      (𝓝 ((periodWeight a θ : ℂ)*(-(2*Real.pi : ℂ)/(-Complex.I*(Real.sin θ : ℂ)))+(simplePVIntegral a θ : ℂ))) := by
    have h := ((tendsto_const_nhds (x := (periodWeight a θ : ℂ))).mul ((tendsto_const_nhds (x := -(2*Real.pi : ℂ))).div hd hdz)).add
      (simple_regulated_integral_tendsto a θ ha hθ hπ)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (simpleCell_decomposition a θ ε ha hθ hπ hε).symm
  have hr : Tendsto (simpleCell a θ) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.sqrt (Real.pi/a) : ℂ)/(-Complex.I*(Real.sin θ : ℂ))*
        (1+2*∑' n : ℕ,unitPhase θ^(n+1)*(gaussianTerm a n : ℂ)))) := by
    have h := ((tendsto_const_nhds (x := -(Real.sqrt (Real.pi/a) : ℂ))).div hd hdz).mul
      ((tendsto_const_nhds (x := (1 : ℂ))).add ((regulated_geometric_tendsto a θ ha hθ hπ).const_mul 2))
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← simpleWhole_eq_cell a θ ε ha hε]
    exact (simpleWhole_eq_series a θ ε ha hθ hπ hε).symm
  have he := congrArg Complex.re (tendsto_nhds_unique hl hr)
  have hi : -(1 : ℂ)/(-Complex.I*(Real.sin θ : ℂ)) =
      -Complex.I*((1/Real.sin θ : ℝ) : ℂ) := by
    push_cast
    field_simp [Complex.I_ne_zero,Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne']
    ring_nf
    simp [Complex.I_sq]
  have hleft : -(2*Real.pi : ℂ)/(-Complex.I*(Real.sin θ : ℂ))=(2*Real.pi : ℂ)*(-(1 : ℂ)/(-Complex.I*(Real.sin θ : ℂ))) := by ring
  have hright : -(Real.sqrt (Real.pi/a) : ℂ)/(-Complex.I*(Real.sin θ : ℂ))=
      (Real.sqrt (Real.pi/a) : ℂ)*(-(1 : ℂ)/(-Complex.I*(Real.sin θ : ℂ))) := by ring
  rw [hleft,hright,hi] at he
  have hs : (∑' n : ℕ,unitPhase θ^(n+1)*(gaussianTerm a n : ℂ)).im=
      ∑' n : ℕ,gaussianTerm a n*Real.sin ((n+1 : ℝ)*θ) := by
    rw [Complex.im_tsum (phase_gaussian_summable a θ ha)]
    apply tsum_congr
    intro n
    rw [unitPhase_pow]
    simp only [unitPhase,Complex.mul_im,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,one_mul,zero_add]
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.one_re,Complex.one_im,
    Complex.re_ofNat,Complex.im_ofNat,zero_mul,mul_zero,zero_add,add_zero,sub_zero,zero_sub,neg_zero,Complex.add_im,hs] at he
  convert he using 1; ring

end ShiftedCosineTask
