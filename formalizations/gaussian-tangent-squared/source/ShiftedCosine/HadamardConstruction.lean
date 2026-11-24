import ShiftedCosine.CutPeriodization
import ShiftedCosine.Mass

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

lemma cutIntegral_const_mul (θ δ c : ℝ) (f : ℝ → ℝ) :
    cutIntegral θ δ (fun t => c*f t)=c*cutIntegral θ δ f := by
  unfold cutIntegral
  simp_rw [intervalIntegral.integral_const_mul]
  ring

lemma cutIntegral_congr (θ δ : ℝ) (f g : ℝ → ℝ) (_hθ : 0 < θ) (_hπ : θ < Real.pi)
    (_hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ)
    (he : ∀ t ∈ excludedCell θ δ, f t=g t) : cutIntegral θ δ f=cutIntegral θ δ g := by
  unfold cutIntegral
  have hl : (∫ t in (-Real.pi)..(-θ-δ), f t)=(∫ t in (-Real.pi)..(-θ-δ),g t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    exact he t (Or.inl (Or.inl ht))
  have hm : (∫ t in (-θ+δ)..(θ-δ), f t)=(∫ t in (-θ+δ)..(θ-δ),g t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    exact he t (Or.inl (Or.inr ht))
  have hr : (∫ t in (θ+δ)..Real.pi, f t)=(∫ t in (θ+δ)..Real.pi,g t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    exact he t (Or.inr ht)
  rw [hl,hm,hr]

lemma cutIntegral_add (θ δ : ℝ) (f g : ℝ → ℝ) (_hθ : 0 < θ) (_hπ : θ < Real.pi)
    (_hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ)
    (hf : ContinuousOn f (excludedCell θ δ)) (hg : ContinuousOn g (excludedCell θ δ)) :
    cutIntegral θ δ (fun t => f t+g t)=cutIntegral θ δ f+cutIntegral θ δ g := by
  have hleft : uIcc (-Real.pi) (-θ-δ) ⊆ excludedCell θ δ := by
    rw [uIcc_of_le (by linarith)]; exact fun t ht => Or.inl (Or.inl ht)
  have hmid : uIcc (-θ+δ) (θ-δ) ⊆ excludedCell θ δ := by
    rw [uIcc_of_le (by linarith)]; exact fun t ht => Or.inl (Or.inr ht)
  have hright : uIcc (θ+δ) Real.pi ⊆ excludedCell θ δ := by
    rw [uIcc_of_le (by linarith)]; exact fun t ht => Or.inr ht
  unfold cutIntegral
  rw [intervalIntegral.integral_add (hf.mono hleft).intervalIntegrable (hg.mono hleft).intervalIntegrable,
    intervalIntegral.integral_add (hf.mono hmid).intervalIntegrable (hg.mono hmid).intervalIntegrable,
    intervalIntegral.integral_add (hf.mono hright).intervalIntegrable (hg.mono hright).intervalIntegrable]
  ring

lemma integrable_cut_tendsto (f : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hi : IntegrableOn f (Icc (-Real.pi) Real.pi)) :
    Tendsto (fun δ => cutIntegral θ δ f) (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in (-Real.pi)..Real.pi,f t)) := by
  let A : ℝ → ℝ := fun t => ∫ x in (-Real.pi)..t, f x
  have hriu : IntegrableOn f (uIcc (-Real.pi) Real.pi) := by rw [uIcc_of_le (by linarith [Real.pi_pos])]; exact hi
  have hc := intervalIntegral.continuousOn_primitive_interval hriu
  have hcneg : ContinuousAt A (-θ) := hc.continuousAt (by
    rw [uIcc_of_le (by linarith [Real.pi_pos])]
    apply Icc_mem_nhds <;> linarith [Real.pi_pos])
  have hcpos : ContinuousAt A θ := hc.continuousAt (by
    rw [uIcc_of_le (by linarith [Real.pi_pos])]
    apply Icc_mem_nhds <;> linarith [Real.pi_pos])
  have he (δ : ℝ) (hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ) :
      cutIntegral θ δ f=A (-θ-δ)+A (θ-δ)-A (-θ+δ)+A Real.pi-A (θ+δ) := by
    have hI (u v : ℝ) (hu : -Real.pi ≤ u) (hv : v ≤ Real.pi) (huv : u ≤ v) :
        IntervalIntegrable f volume u v := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
      exact hi.mono_set (fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    have hM := intervalIntegral.integral_add_adjacent_intervals
      (hI (-Real.pi) (-θ+δ) le_rfl (by linarith) (by linarith))
      (hI (-θ+δ) (θ-δ) (by linarith) (by linarith) (by linarith))
    have hR := intervalIntegral.integral_add_adjacent_intervals
      (hI (-Real.pi) (θ+δ) le_rfl (by linarith) (by linarith))
      (hI (θ+δ) Real.pi (by linarith) le_rfl (by linarith))
    unfold cutIntegral A
    linarith
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hNminus := hcneg.tendsto.comp (show Tendsto (fun δ : ℝ => -θ-δ) (𝓝[>] (0 : ℝ)) (𝓝 (-θ)) from by
    simpa using (tendsto_const_nhds (x := -θ)).sub hid)
  have hNplus := hcneg.tendsto.comp (show Tendsto (fun δ : ℝ => -θ+δ) (𝓝[>] (0 : ℝ)) (𝓝 (-θ)) from by
    simpa using (tendsto_const_nhds (x := -θ)).add hid)
  have hPminus := hcpos.tendsto.comp (show Tendsto (fun δ : ℝ => θ-δ) (𝓝[>] (0 : ℝ)) (𝓝 θ) from by
    simpa using (tendsto_const_nhds (x := θ)).sub hid)
  have hPplus := hcpos.tendsto.comp (show Tendsto (fun δ : ℝ => θ+δ) (𝓝[>] (0 : ℝ)) (𝓝 θ) from by
    simpa using (tendsto_const_nhds (x := θ)).add hid)
  have h := (((hNminus.add hPminus).sub hNplus).add (tendsto_const_nhds (x := A Real.pi))).sub hPplus
  have hval : A (-θ)+A θ-A (-θ)+A Real.pi-A θ=A Real.pi := by ring
  rw [hval] at h
  apply h.congr'
  have hltθ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < θ := (eventually_lt_nhds hθ).filter_mono nhdsWithin_le_nhds
  have hltπ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi-θ :=
    (eventually_lt_nhds (sub_pos.mpr hπ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hltθ,hltπ] with δ hδ hδθ hδπ
  exact (he δ hδ hδθ hδπ).symm

lemma periodWeight_continuousOn (a : ℝ) (ha : 0 < a) :
    ContinuousOn (periodWeight a) (Icc (-Real.pi) Real.pi) := by
  unfold periodWeight
  apply (PeriodicPoleTask.periodizedWeight_continuousOn (4*a) (by positivity)).comp (by fun_prop)
  intro t ht
  constructor <;> linarith [ht.1,ht.2]

lemma excludedCell_subset (θ δ : ℝ) (hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ) :
    excludedCell θ δ ⊆ Icc (-Real.pi) Real.pi := by
  intro t ht
  rcases ht with (ht | ht) | ht
  all_goals constructor <;> linarith [ht.1,ht.2,Real.pi_pos]

lemma outerValue_decomposition (a θ δ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ) :
    outerValue a θ δ=periodWeight a θ*cutIntegral θ δ (fun t => 1/(Real.cos t-Real.cos θ)^2)-
      (periodDerivative a θ/Real.sin θ)*cutIntegral θ δ (fun t => 1/(Real.cos t-Real.cos θ))+
      cutIntegral θ δ (remainder a θ) := by
  have hW := (periodWeight_continuousOn a ha).mono (excludedCell_subset θ δ hδ hδθ hδπ)
  have hK1 : ContinuousOn (fun t : ℝ => 1/(Real.cos t-Real.cos θ)) (excludedCell θ δ) :=
    ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => cut_cos_ne θ δ t hθ hπ hδ ht)
  have hK2 : ContinuousOn (fun t : ℝ => 1/(Real.cos t-Real.cos θ)^2) (excludedCell θ δ) :=
    ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => pow_ne_zero 2 (cut_cos_ne θ δ t hθ hπ hδ ht))
  have hR : ContinuousOn (remainder a θ) (excludedCell θ δ) := by
    unfold remainder interpolationNumerator
    apply ContinuousOn.div (hW.sub continuousOn_const |>.add (by fun_prop)) (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (cut_cos_ne θ δ t hθ hπ hδ ht)
  rw [outerValue_periodized a θ δ ha hθ hπ hδ hδθ hδπ]
  have he := cutIntegral_congr θ δ (fun t => periodWeight a t/(Real.cos t-Real.cos θ)^2)
    (fun t => periodWeight a θ*(1/(Real.cos t-Real.cos θ)^2)+
      (-(periodDerivative a θ/Real.sin θ))*(1/(Real.cos t-Real.cos θ))+remainder a θ t)
    hθ hπ hδ hδθ hδπ (fun t ht => by
      unfold remainder interpolationNumerator
      field_simp [cut_cos_ne θ δ t hθ hπ hδ ht]
      ring)
  rw [he,cutIntegral_add θ δ
      (fun t => periodWeight a θ*(1/(Real.cos t-Real.cos θ)^2)+
        (-(periodDerivative a θ/Real.sin θ))*(1/(Real.cos t-Real.cos θ))) (remainder a θ) hθ hπ hδ hδθ hδπ
      ((continuousOn_const.mul hK2).add (continuousOn_const.mul hK1)) hR,
    cutIntegral_add θ δ
      (fun t => periodWeight a θ*(1/(Real.cos t-Real.cos θ)^2))
      (fun t => (-(periodDerivative a θ/Real.sin θ))*(1/(Real.cos t-Real.cos θ))) hθ hπ hδ hδθ hδπ (continuousOn_const.mul hK2) (continuousOn_const.mul hK1),
    cutIntegral_const_mul,cutIntegral_const_mul]
  ring

noncomputable def hadamardIntegralValue (a θ : ℝ) : ℝ := ∫ t in (-Real.pi)..Real.pi, remainder a θ t

lemma hadamard_tendsto_integral (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun δ => outerValue a θ δ-2*poleMass a θ/(Real.sin θ^2*δ)) (𝓝[>] (0 : ℝ))
      (𝓝 (hadamardIntegralValue a θ)) := by
  have hR := integrable_cut_tendsto (remainder a θ) θ hθ hπ (remainder_integrableOn a θ ha hθ hπ)
  have h := (((double_cut_subtraction_tendsto θ hθ hπ).const_mul (periodWeight a θ)).add
    ((simple_cut_tendsto θ hθ hπ).const_mul (-(periodDerivative a θ/Real.sin θ)))).add hR
  simp only [mul_zero,zero_add] at h
  apply h.congr'
  have hltθ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < θ := (eventually_lt_nhds hθ).filter_mono nhdsWithin_le_nhds
  have hltπ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < Real.pi-θ :=
    (eventually_lt_nhds (sub_pos.mpr hπ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hltθ,hltπ] with δ hδ hδθ hδπ
  rw [outerValue_decomposition a θ δ ha hθ hπ hδ hδθ hδπ,poleMass_eq a θ ha hθ hπ]
  unfold periodWeight
  ring

end ShiftedCosineTask
