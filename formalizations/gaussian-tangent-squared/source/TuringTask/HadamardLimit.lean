import TuringTask.HadamardRemainder
import TuringTask.PeriodizedTruncation
import TuringTask.CotangentBoundary

set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace PeriodicPoleTask

lemma sin_ne_zero_on_cut (δ t : ℝ) (hδ : 0 < δ) (hδp : δ < Real.pi/2)
    (ht : |t| ≤ Real.pi/2) (hcut : δ ≤ |t|) : Real.sin t ≠ 0 := by
  have h := cut_sin_bound δ t hδ hδp ht hcut
  have hs := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  exact abs_pos.mp (lt_of_lt_of_le hs h)

lemma negative_cotangent_hasDerivAt (t : ℝ) (ht : Real.sin t ≠ 0) :
    HasDerivAt (fun x : ℝ => -Real.cos x/Real.sin x) (1/Real.sin t^2) t := by
  have h := ((Real.hasDerivAt_cos t).neg).div (Real.hasDerivAt_sin t) ht
  convert h using 1 <;> (try rfl) <;> (try simp only [Pi.neg_apply,Pi.div_apply]) <;> (try field_simp) <;> nlinarith [Real.sin_sq_add_cos_sq t]

lemma inverse_sin_sq_integral (a b : ℝ) (hs : ∀ t ∈ uIcc a b, Real.sin t ≠ 0) :
    (∫ t in a..b, 1/Real.sin t^2) = -Real.cos b/Real.sin b - (-Real.cos a/Real.sin a) := by
  have hc : ContinuousOn (fun t : ℝ => 1/Real.sin t^2) (uIcc a b) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    exact fun t ht => pow_ne_zero 2 (hs t ht)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => negative_cotangent_hasDerivAt t (hs t ht)) hc.intervalIntegrable

lemma outerValue_decomposition (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hδp : δ < Real.pi/2) :
    outerValue α δ = 2*poleMass α*(Real.cos δ/Real.sin δ) +
      ((∫ t in (-Real.pi/2)..(-δ), hadamardRemainder α t) +
      (∫ t in δ..(Real.pi/2), hadamardRemainder α t)) := by
  rw [outerValue_periodized α δ hα hδ hδp]
  have hl : -Real.pi/2 ≤ -δ := by linarith
  have hr : δ ≤ Real.pi/2 := hδp.le
  have hls (t : ℝ) (ht : t ∈ uIcc (-Real.pi/2) (-δ)) : Real.sin t ≠ 0 := by
    rw [uIcc_of_le hl] at ht
    apply sin_ne_zero_on_cut δ t hδ hδp
    · exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2,Real.pi_pos]⟩
    · rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2]
  have hrs (t : ℝ) (ht : t ∈ uIcc δ (Real.pi/2)) : Real.sin t ≠ 0 := by
    rw [uIcc_of_le hr] at ht
    apply sin_ne_zero_on_cut δ t hδ hδp
    · exact abs_le.mpr ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
    · rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1
  have hR := hadamardRemainder_intervalIntegrable α hα
  have hRleft : IntervalIntegrable (hadamardRemainder α) volume (-Real.pi/2) (-δ) :=
    hR.mono_set (by rw [uIcc_of_le hl,uIcc_of_le (by linarith [Real.pi_pos])]; exact Icc_subset_Icc le_rfl (by linarith))
  have hRright : IntervalIntegrable (hadamardRemainder α) volume δ (Real.pi/2) :=
    hR.mono_set (by rw [uIcc_of_le hr,uIcc_of_le (by linarith [Real.pi_pos])]; exact Icc_subset_Icc (by linarith) le_rfl)
  have hcleft : IntervalIntegrable (fun t : ℝ => poleMass α*(1/Real.sin t^2)) volume (-Real.pi/2) (-δ) :=
    (show ContinuousOn (fun t : ℝ => 1/Real.sin t^2) (uIcc (-Real.pi/2) (-δ)) from
      ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => pow_ne_zero 2 (hls t ht))).intervalIntegrable.const_mul _
  have hcright : IntervalIntegrable (fun t : ℝ => poleMass α*(1/Real.sin t^2)) volume δ (Real.pi/2) :=
    (show ContinuousOn (fun t : ℝ => 1/Real.sin t^2) (uIcc δ (Real.pi/2)) from
      ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => pow_ne_zero 2 (hrs t ht))).intervalIntegrable.const_mul _
  have he (t : ℝ) : periodizedWeight α t/Real.sin t^2 = poleMass α*(1/Real.sin t^2)+hadamardRemainder α t := by
    unfold hadamardRemainder; ring
  simp_rw [he]
  rw [intervalIntegral.integral_add hcleft hRleft,intervalIntegral.integral_add hcright hRright,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    inverse_sin_sq_integral _ _ hls,inverse_sin_sq_integral _ _ hrs]
  simp only [Real.cos_neg,Real.sin_neg,Real.cos_pi_div_two,Real.sin_pi_div_two,
    show -Real.pi/2 = -(Real.pi/2) by ring,Real.cos_neg,Real.sin_neg,neg_zero,zero_div,sub_zero,zero_sub,div_neg,neg_div,neg_neg]
  ring

noncomputable def hadamardIntegralValue (α : ℝ) : ℝ :=
  ∫ t in (-Real.pi/2)..(Real.pi/2), hadamardRemainder α t

lemma hadamard_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (fun δ : ℝ => outerValue α δ-2*poleMass α/δ) (𝓝[>] (0 : ℝ))
      (𝓝 (hadamardIntegralValue α)) := by
  have hRi := hadamardRemainder_intervalIntegrable α hα
  have hRc : IntegrableOn (hadamardRemainder α) (uIcc (-Real.pi/2) (Real.pi/2)) := by
    rw [uIcc_of_le (by linarith [Real.pi_pos]),integrableOn_Icc_iff_integrableOn_Ioo]
    exact hadamardRemainder_integrableOn α hα
  have hnh : uIcc (-Real.pi/2) (Real.pi/2) ∈ 𝓝 (0 : ℝ) := by
    rw [uIcc_of_le (by linarith [Real.pi_pos])]
    apply Icc_mem_nhds <;> linarith [Real.pi_pos]
  have hleft := ((intervalIntegral.continuousOn_primitive_interval hRc).continuousAt hnh).tendsto.comp
    ((show Tendsto (fun δ : ℝ => -δ) (𝓝[>] (0 : ℝ)) (𝓝 0) by simpa using ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds).neg))
  have hright := ((intervalIntegral.continuousOn_primitive_interval_left hRc).continuousAt hnh).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hsub := cotangent_sub_inv_tendsto.const_mul (2*poleMass α)
  have h := hsub.add (hleft.add hright)
  have hl0 : IntervalIntegrable (hadamardRemainder α) volume (-Real.pi/2) 0 :=
    hRi.mono_set (by simp only [uIcc_of_le (show -Real.pi/2 ≤ (0 : ℝ) by linarith [Real.pi_pos]),uIcc_of_le (show -Real.pi/2 ≤ Real.pi/2 by linarith [Real.pi_pos])]; exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))
  have hr0 : IntervalIntegrable (hadamardRemainder α) volume 0 (Real.pi/2) :=
    hRi.mono_set (by simp only [uIcc_of_le (show (0 : ℝ) ≤ Real.pi/2 by linarith [Real.pi_pos]),uIcc_of_le (show -Real.pi/2 ≤ Real.pi/2 by linarith [Real.pi_pos])]; exact Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl)
  have hj := intervalIntegral.integral_add_adjacent_intervals hl0 hr0
  have ht : Tendsto (fun δ : ℝ => 2*poleMass α*(Real.cos δ/Real.sin δ-1/δ)+
      ((∫ t in (-Real.pi/2)..(-δ),hadamardRemainder α t)+(∫ t in δ..(Real.pi/2),hadamardRemainder α t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (hadamardIntegralValue α)) := by
    simpa only [Function.comp_apply,neg_zero,mul_zero,zero_add,hj,hadamardIntegralValue] using h
  apply ht.congr'
  have hp : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi/2 :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < Real.pi/2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hp] with δ hδ hδp
  rw [outerValue_decomposition α δ hα hδ hδp]
  ring

end PeriodicPoleTask
