import ShiftedCosine.Outer
import TuringTask.CotangentBoundary

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def cutIntegral (θ δ : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ t in (-Real.pi)..(-θ-δ), f t)+(∫ t in (-θ+δ)..(θ-δ), f t)+
    (∫ t in (θ+δ)..Real.pi, f t)
noncomputable def simplePrimitive (θ t : ℝ) : ℝ :=
  (Real.log (Real.sin ((t+θ)/2))-Real.log (Real.sin ((t-θ)/2)))/Real.sin θ
noncomputable def rationalPrimitive (θ t : ℝ) : ℝ := Real.sin t/(Real.cos t-Real.cos θ)
noncomputable def doublePrimitive (θ t : ℝ) : ℝ :=
  (rationalPrimitive θ t+Real.cos θ*simplePrimitive θ t)/Real.sin θ^2

lemma half_sines_ne (θ t : ℝ) (hq : Real.cos t-Real.cos θ ≠ 0) :
    Real.sin ((t+θ)/2) ≠ 0 ∧ Real.sin ((t-θ)/2) ≠ 0 := by
  rw [Real.cos_sub_cos] at hq
  exact ⟨fun h => hq (by rw [h]; ring),fun h => hq (by rw [h]; ring)⟩

lemma simplePrimitive_hasDerivAt (θ t : ℝ) (hs : Real.sin θ ≠ 0)
    (hq : Real.cos t-Real.cos θ ≠ 0) :
    HasDerivAt (simplePrimitive θ) (1/(Real.cos t-Real.cos θ)) t := by
  have hp := (half_sines_ne θ t hq).1
  have hm := (half_sines_ne θ t hq).2
  have hP0 : HasDerivAt (fun y : ℝ => Real.sin ((y+θ)/2)) (Real.cos ((t+θ)/2)/2) t := by
    convert (Real.hasDerivAt_sin ((t+θ)/2)).comp t
      (((hasDerivAt_id t).add_const θ).div_const 2) using 1 <;> (try rfl); ring
  have hM0 : HasDerivAt (fun y : ℝ => Real.sin ((y-θ)/2)) (Real.cos ((t-θ)/2)/2) t := by
    convert (Real.hasDerivAt_sin ((t-θ)/2)).comp t
      (((hasDerivAt_id t).sub_const θ).div_const 2) using 1 <;> (try rfl); ring
  have hP := hP0.log hp
  have hM := hM0.log hm
  have h := (hP.sub hM).div_const (Real.sin θ)
  apply h.congr_deriv
  have he : Real.cos ((t+θ)/2)*Real.sin ((t-θ)/2)-
      Real.cos ((t-θ)/2)*Real.sin ((t+θ)/2) = -Real.sin θ := by
    have hx := Real.sin_sub ((t-θ)/2) ((t+θ)/2)
    rw [show (t-θ)/2-(t+θ)/2 = -θ by ring,Real.sin_neg] at hx
    linear_combination -hx
  rw [Real.cos_sub_cos]
  field_simp [hs,hp,hm]
  linear_combination he

lemma rationalPrimitive_hasDerivAt (θ t : ℝ) (hq : Real.cos t-Real.cos θ ≠ 0) :
    HasDerivAt (rationalPrimitive θ)
      (Real.sin θ^2/(Real.cos t-Real.cos θ)^2-Real.cos θ/(Real.cos t-Real.cos θ)) t := by
  have h := (Real.hasDerivAt_sin t).div ((Real.hasDerivAt_cos t).sub_const (Real.cos θ)) hq
  apply h.congr_deriv
  field_simp [hq]
  nlinarith [Real.sin_sq_add_cos_sq t,Real.sin_sq_add_cos_sq θ]

lemma doublePrimitive_hasDerivAt (θ t : ℝ) (hs : Real.sin θ ≠ 0)
    (hq : Real.cos t-Real.cos θ ≠ 0) :
    HasDerivAt (doublePrimitive θ) (1/(Real.cos t-Real.cos θ)^2) t := by
  have h := ((rationalPrimitive_hasDerivAt θ t hq).add
    ((simplePrimitive_hasDerivAt θ t hs hq).const_mul (Real.cos θ))).div_const (Real.sin θ^2)
  apply h.congr_deriv
  field_simp [hs,hq]
  ring

lemma primitive_cut_integral (θ δ : ℝ) (P f : ℝ → ℝ) (_hθ : 0 < θ) (_hπ : θ < Real.pi)
    (_hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ)
    (hd : ∀ t ∈ excludedCell θ δ, HasDerivAt P (f t) t)
    (hc : ContinuousOn f (excludedCell θ δ)) :
    cutIntegral θ δ f=P (-θ-δ)-P (-Real.pi)+P (θ-δ)-P (-θ+δ)+P Real.pi-P (θ+δ) := by
  have hl : -Real.pi ≤ -θ-δ := by linarith
  have hm : -θ+δ ≤ θ-δ := by linarith
  have hr : θ+δ ≤ Real.pi := by linarith
  have hleft : uIcc (-Real.pi) (-θ-δ) ⊆ excludedCell θ δ := by
    rw [uIcc_of_le hl]; exact fun t ht => Or.inl (Or.inl ht)
  have hmid : uIcc (-θ+δ) (θ-δ) ⊆ excludedCell θ δ := by
    rw [uIcc_of_le hm]; exact fun t ht => Or.inl (Or.inr ht)
  have hright : uIcc (θ+δ) Real.pi ⊆ excludedCell θ δ := by
    rw [uIcc_of_le hr]; exact fun t ht => Or.inr ht
  unfold cutIntegral
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hleft ht))
      (hc.mono hleft).intervalIntegrable,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hmid ht))
      (hc.mono hmid).intervalIntegrable,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hright ht))
      (hc.mono hright).intervalIntegrable]
  ring

lemma simplePrimitive_odd (θ t : ℝ) : simplePrimitive θ (-t) = -simplePrimitive θ t := by
  unfold simplePrimitive
  rw [show (-t+θ)/2 = -((t-θ)/2) by ring,show (-t-θ)/2 = -((t+θ)/2) by ring,
    Real.sin_neg,Real.sin_neg,Real.log_neg_eq_log,Real.log_neg_eq_log]
  ring

lemma simplePrimitive_at_pi (θ : ℝ) : simplePrimitive θ Real.pi=0 := by
  unfold simplePrimitive
  rw [show (Real.pi+θ)/2=Real.pi/2+θ/2 by ring,
    show (Real.pi-θ)/2=Real.pi/2-θ/2 by ring]
  simp [Real.sin_add,Real.sin_sub]

lemma rationalPrimitive_odd (θ t : ℝ) : rationalPrimitive θ (-t) = -rationalPrimitive θ t := by
  simp [rationalPrimitive,Real.sin_neg,Real.cos_neg,neg_div]
lemma rationalPrimitive_at_pi (θ : ℝ) : rationalPrimitive θ Real.pi=0 := by
  simp [rationalPrimitive]

lemma doublePrimitive_odd (θ t : ℝ) : doublePrimitive θ (-t) = -doublePrimitive θ t := by
  unfold doublePrimitive
  rw [rationalPrimitive_odd,simplePrimitive_odd]
  ring
lemma doublePrimitive_at_pi (θ : ℝ) : doublePrimitive θ Real.pi=0 := by
  simp [doublePrimitive,simplePrimitive_at_pi,rationalPrimitive_at_pi]

lemma simple_cut_formula (θ δ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ) :
    cutIntegral θ δ (fun t => 1/(Real.cos t-Real.cos θ))=
      2*(simplePrimitive θ (θ-δ)-simplePrimitive θ (θ+δ)) := by
  rw [primitive_cut_integral θ δ (simplePrimitive θ) _ hθ hπ hδ hδθ hδπ
    (fun t ht => simplePrimitive_hasDerivAt θ t
      (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne' (cut_cos_ne θ δ t hθ hπ hδ ht))
    (ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => cut_cos_ne θ δ t hθ hπ hδ ht))]
  rw [show -θ-δ=-(θ+δ) by ring,show -θ+δ=-(θ-δ) by ring,
    simplePrimitive_odd,simplePrimitive_odd,simplePrimitive_odd,simplePrimitive_at_pi]
  ring

lemma simple_cut_log_formula (θ δ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ) :
    cutIntegral θ δ (fun t => 1/(Real.cos t-Real.cos θ))=
      (2/Real.sin θ)*(Real.log (Real.sin (θ-δ/2))-Real.log (Real.sin (θ+δ/2))) := by
  rw [simple_cut_formula θ δ hθ hπ hδ hδθ hδπ]
  unfold simplePrimitive
  rw [show (θ-δ+θ)/2=θ-δ/2 by ring,show (θ-δ-θ)/2=-(δ/2) by ring,
    show (θ+δ+θ)/2=θ+δ/2 by ring,show (θ+δ-θ)/2=δ/2 by ring,
    Real.sin_neg,Real.log_neg_eq_log]
  ring

lemma simple_cut_tendsto (θ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun δ => cutIntegral θ δ (fun t => 1/(Real.cos t-Real.cos θ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne'
  have hc : ContinuousAt (fun δ : ℝ =>
      (2/Real.sin θ)*(Real.log (Real.sin (θ-δ/2))-Real.log (Real.sin (θ+δ/2)))) 0 := by
    fun_prop (disch := simp [hs])
  have ht : Tendsto (fun δ : ℝ => (2/Real.sin θ)*
      (Real.log (Real.sin (θ-δ/2))-Real.log (Real.sin (θ+δ/2))))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  have hltθ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < θ :=
    (eventually_lt_nhds hθ).filter_mono nhdsWithin_le_nhds
  have hltπ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi-θ :=
    (eventually_lt_nhds (sub_pos.mpr hπ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hltθ,hltπ] with δ hδ hδθ hδπ
  exact (simple_cut_log_formula θ δ hθ hπ hδ hδθ hδπ).symm

lemma rationalPrimitive_half_angles (θ t : ℝ) (hq : Real.cos t-Real.cos θ ≠ 0) :
    rationalPrimitive θ t = -(1/2 : ℝ)*
      (Real.cos ((t-θ)/2)/Real.sin ((t-θ)/2)+Real.cos ((t+θ)/2)/Real.sin ((t+θ)/2)) := by
  have hp := (half_sines_ne θ t hq).1
  have hm := (half_sines_ne θ t hq).2
  unfold rationalPrimitive
  rw [Real.cos_sub_cos]
  have he := Real.sin_add ((t+θ)/2) ((t-θ)/2)
  rw [show (t+θ)/2+(t-θ)/2=t by ring] at he
  field_simp [hp,hm]
  linear_combination -he

lemma double_cut_formula (θ δ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ) :
    cutIntegral θ δ (fun t => 1/(Real.cos t-Real.cos θ)^2)=
      (2*(Real.cos (δ/2)/Real.sin (δ/2))+
        Real.cos (θ+δ/2)/Real.sin (θ+δ/2)-Real.cos (θ-δ/2)/Real.sin (θ-δ/2)+
        Real.cos θ*cutIntegral θ δ (fun t => 1/(Real.cos t-Real.cos θ)))/Real.sin θ^2 := by
  rw [primitive_cut_integral θ δ (doublePrimitive θ) _ hθ hπ hδ hδθ hδπ
    (fun t ht => doublePrimitive_hasDerivAt θ t
      (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne' (cut_cos_ne θ δ t hθ hπ hδ ht))
    (ContinuousOn.div continuousOn_const (by fun_prop)
      (fun t ht => pow_ne_zero 2 (cut_cos_ne θ δ t hθ hπ hδ ht)))]
  rw [show -θ-δ=-(θ+δ) by ring,show -θ+δ=-(θ-δ) by ring,
    doublePrimitive_odd,doublePrimitive_odd,doublePrimitive_odd,doublePrimitive_at_pi]
  unfold doublePrimitive
  have hl : Real.cos (θ-δ)-Real.cos θ ≠ 0 := cut_cos_ne θ δ (θ-δ) hθ hπ hδ
    (Or.inl (Or.inr ⟨by linarith,le_rfl⟩))
  have hr : Real.cos (θ+δ)-Real.cos θ ≠ 0 := cut_cos_ne θ δ (θ+δ) hθ hπ hδ
    (Or.inr ⟨le_rfl,by linarith⟩)
  rw [rationalPrimitive_half_angles θ (θ-δ) hl,rationalPrimitive_half_angles θ (θ+δ) hr,
    show (θ-δ-θ)/2=-(δ/2) by ring,show (θ-δ+θ)/2=θ-δ/2 by ring,
    show (θ+δ-θ)/2=δ/2 by ring,show (θ+δ+θ)/2=θ+δ/2 by ring,
    Real.cos_neg,Real.sin_neg,simple_cut_formula θ δ hθ hπ hδ hδθ hδπ]
  ring

lemma double_cut_subtraction_tendsto (θ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun δ => cutIntegral θ δ (fun t => 1/(Real.cos t-Real.cos θ)^2)-
      4/(Real.sin θ^2*δ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne'
  have hh : Tendsto (fun δ : ℝ => δ/2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa using (show Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) from
        tendsto_id.mono_left nhdsWithin_le_nhds).div_const (2 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (div_pos hδ (by norm_num) : 0 < δ/2)
  have hcot := PeriodicPoleTask.cotangent_sub_inv_tendsto.comp hh
  have hc : ContinuousAt (fun δ : ℝ =>
      Real.cos (θ+δ/2)/Real.sin (θ+δ/2)-Real.cos (θ-δ/2)/Real.sin (θ-δ/2)) 0 := by
    fun_prop (disch := simp [hs])
  have hc0 : Tendsto (fun δ : ℝ =>
      Real.cos (θ+δ/2)/Real.sin (θ+δ/2)-Real.cos (θ-δ/2)/Real.sin (θ-δ/2))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := (((hcot.const_mul 2).add hc0).add ((simple_cut_tendsto θ hθ hπ).const_mul (Real.cos θ))).div_const (Real.sin θ^2)
  simp only [mul_zero,zero_add,zero_div] at h
  apply h.congr'
  have hltθ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < θ :=
    (eventually_lt_nhds hθ).filter_mono nhdsWithin_le_nhds
  have hltπ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi-θ :=
    (eventually_lt_nhds (sub_pos.mpr hπ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hltθ,hltπ] with δ hδ hδθ hδπ
  rw [double_cut_formula θ δ hθ hπ hδ hδθ hδπ]
  dsimp only [Function.comp_apply]
  field_simp
  ring

end ShiftedCosineTask
