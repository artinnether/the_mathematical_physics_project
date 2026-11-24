import ShiftedCosine.ComplexGeometric

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def regulatorA (θ ε : ℝ) : ℝ := 1+ε^2-Real.cos θ^2
noncomputable def regulatorV (θ ε : ℝ) : ℝ :=
  Real.sqrt ((regulatorA θ ε+Real.sqrt (regulatorA θ ε^2+4*Real.cos θ^2*ε^2))/2)
noncomputable def regulatorD (θ ε : ℝ) : ℂ :=
  ((Real.cos θ*ε/regulatorV θ ε : ℝ) : ℂ)-Complex.I*(regulatorV θ ε : ℂ)
noncomputable def regulatorZ (θ ε : ℝ) : ℂ := (Real.cos θ : ℂ)-Complex.I*(ε : ℂ)
noncomputable def regulatorQ (θ ε : ℝ) : ℂ := regulatorZ θ ε-regulatorD θ ε

lemma regulatorA_positive (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) : 0 < regulatorA θ ε := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  unfold regulatorA
  nlinarith [Real.sin_sq_add_cos_sq θ,sq_pos_of_pos hs,sq_nonneg ε]

lemma regulatorV_positive (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) : 0 < regulatorV θ ε := by
  apply Real.sqrt_pos.2
  have h := regulatorA_positive θ ε hθ hπ
  positivity

lemma regulatorV_equation (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    (regulatorV θ ε)^4-regulatorA θ ε*(regulatorV θ ε)^2=Real.cos θ^2*ε^2 := by
  have hA := regulatorA_positive θ ε hθ hπ
  have hrad : 0 ≤ regulatorA θ ε^2+4*Real.cos θ^2*ε^2 := by positivity
  have hv : 0 ≤ (regulatorA θ ε+Real.sqrt (regulatorA θ ε^2+4*Real.cos θ^2*ε^2))/2 := by positivity
  have he := Real.sq_sqrt hv
  have hr := Real.sq_sqrt hrad
  change regulatorV θ ε^2 = _ at he
  nlinarith [sq_nonneg (regulatorV θ ε)]

lemma regulatorV_gt_epsilon (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (hε : 0 < ε) :
    ε < regulatorV θ ε := by
  have hv := regulatorV_positive θ ε hθ hπ
  have he := regulatorV_equation θ ε hθ hπ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have he2 : ε^2 < regulatorV θ ε^2 := by
    by_contra hn
    have hn := le_of_not_gt hn
    unfold regulatorA at he
    have hprod := mul_nonneg (show 0 ≤ ε^2-regulatorV θ ε^2 by linarith)
      (show 0 ≤ regulatorV θ ε^2 by positivity)
    nlinarith [Real.sin_sq_add_cos_sq θ,sq_pos_of_pos hs,sq_pos_of_pos hε]
  nlinarith

lemma regulatorD_square (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    regulatorD θ ε^2=regulatorZ θ ε^2-1 := by
  have hv := (regulatorV_positive θ ε hθ hπ).ne'
  have he := regulatorV_equation θ ε hθ hπ
  unfold regulatorA at he
  apply Complex.ext
  · simp only [regulatorD,regulatorZ,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.one_re,pow_two,zero_mul,mul_zero,one_mul,sub_zero,zero_sub,zero_add]
    field_simp [hv]
    nlinarith
  · simp only [regulatorD,regulatorZ,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.one_im,
      pow_two,zero_mul,mul_zero,one_mul,sub_zero,zero_sub,zero_add]
    field_simp [hv]

lemma regulatorV_identity (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    (regulatorV θ ε^2-ε^2)*(regulatorV θ ε^2+Real.cos θ^2)=regulatorV θ ε^2 := by
  have h := regulatorV_equation θ ε hθ hπ
  unfold regulatorA at h
  nlinarith

lemma regulatorQ_formula (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    regulatorQ θ ε = ((regulatorV θ ε-ε : ℝ) : ℂ)*
      (((Real.cos θ/regulatorV θ ε : ℝ) : ℂ)+Complex.I) := by
  have hv := (regulatorV_positive θ ε hθ hπ).ne'
  unfold regulatorQ regulatorZ regulatorD
  apply Complex.ext <;> simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_sub,add_zero,zero_add]
  · field_simp [hv]
  · ring

lemma regulatorQ_normSq (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (hε : 0 < ε) :
    Complex.normSq (regulatorQ θ ε) = (regulatorV θ ε-ε)/(regulatorV θ ε+ε) := by
  have hv := (regulatorV_positive θ ε hθ hπ).ne'
  have hplus : regulatorV θ ε+ε ≠ 0 := (add_pos (regulatorV_positive θ ε hθ hπ) hε).ne'
  have hid := regulatorV_identity θ ε hθ hπ
  rw [regulatorQ_formula θ ε hθ hπ,Complex.normSq_mul]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,add_zero,zero_add,
    mul_zero,mul_one]
  field_simp [hv,hplus]
  linear_combination (regulatorV θ ε-ε)*hid

lemma regulatorQ_norm_lt_one (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (hε : 0 < ε) :
    ‖regulatorQ θ ε‖ < 1 := by
  have hv := regulatorV_positive θ ε hθ hπ
  have hsq := regulatorQ_normSq θ ε hθ hπ hε
  have hlt : Complex.normSq (regulatorQ θ ε) < 1 := by
    rw [hsq]
    apply (div_lt_one (by positivity : 0 < regulatorV θ ε+ε)).2
    linarith
  rw [Complex.normSq_eq_norm_sq] at hlt
  nlinarith [norm_nonneg (regulatorQ θ ε)]

lemma regulatorD_ne_zero (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) : regulatorD θ ε ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp [regulatorD] at hi
  have hv := regulatorV_positive θ ε hθ hπ
  linarith

lemma regulatorQ_ne_zero (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) : regulatorQ θ ε ≠ 0 := by
  have h := regulatorD_square θ ε hθ hπ
  intro he
  have he : regulatorZ θ ε=regulatorD θ ε := sub_eq_zero.mp he
  rw [he] at h
  have hone : (1 : ℂ)=0 := by linear_combination h
  exact one_ne_zero hone

lemma regulatorV_at_zero (θ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) : regulatorV θ 0=Real.sin θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hA : regulatorA θ 0=Real.sin θ^2 := by
    unfold regulatorA
    nlinarith [Real.sin_sq_add_cos_sq θ]
  unfold regulatorV
  rw [hA]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,add_zero]
  rw [Real.sqrt_sq (sq_nonneg _)]
  rw [show (Real.sin θ^2+Real.sin θ^2)/2=Real.sin θ^2 by ring,Real.sqrt_sq hs.le]

lemma regulatorD_tendsto (θ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (regulatorD θ) (𝓝[>] (0 : ℝ)) (𝓝 (-Complex.I*(Real.sin θ : ℂ))) := by
  have hc : ContinuousAt (regulatorD θ) 0 := by
    unfold regulatorD
    have hv : regulatorV θ 0 ≠ 0 := (regulatorV_positive θ 0 hθ hπ).ne'
    have hvc : Continuous (regulatorV θ) := by unfold regulatorV regulatorA; fun_prop
    fun_prop
  have he : regulatorD θ 0 = -Complex.I*(Real.sin θ : ℂ) := by
    simp [regulatorD,regulatorV_at_zero θ hθ hπ]
  rw [← he]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

lemma regulatorQ_tendsto (θ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (regulatorQ θ) (𝓝[>] (0 : ℝ)) (𝓝 ((Real.cos θ : ℂ)+Complex.I*(Real.sin θ : ℂ))) := by
  have hz : Tendsto (regulatorZ θ) (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos θ : ℂ)) := by
    have hc : ContinuousAt (regulatorZ θ) 0 := by unfold regulatorZ; fun_prop
    simpa [regulatorZ] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := hz.sub (regulatorD_tendsto θ hθ hπ)
  change Tendsto (fun ε => regulatorZ θ ε-regulatorD θ ε) _ _
  simpa only [sub_neg_eq_add,neg_mul] using h

lemma regulatorZ_of_Q (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    regulatorZ θ ε=(1+regulatorQ θ ε^2)/(2*regulatorQ θ ε) := by
  have hq := regulatorQ_ne_zero θ ε hθ hπ
  have he := regulatorD_square θ ε hθ hπ
  apply (eq_div_iff (mul_ne_zero (by norm_num) hq)).2
  unfold regulatorQ
  linear_combination -he

lemma regulatorD_of_Q (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    regulatorD θ ε=(1-regulatorQ θ ε^2)/(2*regulatorQ θ ε) := by
  have hq := regulatorQ_ne_zero θ ε hθ hπ
  have he := regulatorD_square θ ε hθ hπ
  apply (eq_div_iff (mul_ne_zero (by norm_num) hq)).2
  unfold regulatorQ
  linear_combination -he

end ShiftedCosineTask
