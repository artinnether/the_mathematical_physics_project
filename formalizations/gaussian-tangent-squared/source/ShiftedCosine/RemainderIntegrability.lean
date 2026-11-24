import ShiftedCosine.CosineBounds

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

lemma periodWeight_even (a t : ℝ) : periodWeight a (-t)=periodWeight a t := by
  unfold periodWeight
  rw [neg_div,PeriodicPoleTask.periodizedWeight_even]

lemma periodWeight_norm_bound (a t : ℝ) (ha : 0 < a) (ht : |t| ≤ Real.pi) :
    ‖periodWeight a t‖ ≤ ∑' k : ℤ, PeriodicPoleTask.latticeMajorant (4*a) k := by
  have ht2 : |t/2| ≤ Real.pi/2 := by rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]; linarith
  have hb (k : ℤ) : ‖PeriodicPoleTask.weight (4*a) (t/2+k*Real.pi)‖ ≤
      PeriodicPoleTask.latticeMajorant (4*a) k := by
    rw [Real.norm_eq_abs,abs_of_pos (show 0 < PeriodicPoleTask.weight (4*a) (t/2+k*Real.pi) from Real.exp_pos _)]
    exact PeriodicPoleTask.shifted_weight_bound (4*a) (t/2) k (by positivity) ht2
  have hM := PeriodicPoleTask.latticeMajorant_summable (4*a) (by positivity)
  have hn := hM.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hb hM)

lemma interpolation_even (a θ t : ℝ) : interpolationNumerator a θ (-t)=interpolationNumerator a θ t := by
  simp only [interpolationNumerator,periodWeight_even,Real.cos_neg]

lemma remainder_even (a θ t : ℝ) : remainder a θ (-t)=remainder a θ t := by
  simp only [remainder,interpolation_even,Real.cos_neg]

lemma interpolation_global_bound (a θ t : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (ht : |t| ≤ Real.pi) :
    ‖interpolationNumerator a θ t‖ ≤
      2*(∑' k : ℤ, PeriodicPoleTask.latticeMajorant (4*a) k)+2*‖periodDerivative a θ/Real.sin θ‖ := by
  have hW := periodWeight_norm_bound a t ha ht
  have hV := periodWeight_norm_bound a θ ha (by rw [abs_of_pos hθ]; exact hπ.le)
  have hcos : ‖Real.cos t-Real.cos θ‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have h1 := Real.abs_cos_le_one t
      have h2 := Real.abs_cos_le_one θ
      rw [Real.norm_eq_abs,Real.norm_eq_abs]
      linarith)
  have hprod := mul_le_mul_of_nonneg_left hcos (norm_nonneg (periodDerivative a θ/Real.sin θ))
  unfold interpolationNumerator
  have h := (norm_add_le (periodWeight a t-periodWeight a θ)
    ((periodDerivative a θ/Real.sin θ)*(Real.cos t-Real.cos θ))).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  rw [norm_mul] at h
  linarith

lemma remainder_measurable (a θ : ℝ) : Measurable (remainder a θ) := by
  have hW : Measurable (periodWeight a) :=
    (PeriodicPoleTask.periodizedWeight_measurable (4*a)).comp (by fun_prop)
  unfold remainder interpolationNumerator
  fun_prop

lemma remainder_bounded (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (-Real.pi) Real.pi, ‖remainder a θ t‖ ≤ C := by
  let ρ := min θ (Real.pi-θ)/4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρθ : 2*ρ ≤ θ := by have h := min_le_left θ (Real.pi-θ); dsimp [ρ]; linarith
  have hρπ : 2*ρ ≤ Real.pi-θ := by have h := min_le_right θ (Real.pi-θ); dsimp [ρ]; linarith
  obtain ⟨C,hC,hbound⟩ := cut_kernel_bounded θ ρ hθ hπ hρ
  let L := (secondBound a+‖periodDerivative a θ/Real.sin θ‖)*Real.pi^4/(16*ρ^2)
  let G := 2*(∑' k : ℤ, PeriodicPoleTask.latticeMajorant (4*a) k)+2*‖periodDerivative a θ/Real.sin θ‖
  have hL : 0 ≤ L := by
    apply div_nonneg (mul_nonneg (add_nonneg (secondBound_nonneg a ha) (norm_nonneg _)) (by positivity)) (by positivity)
  have hG : 0 ≤ G := by
    have hm : 0 ≤ ∑' k : ℤ, PeriodicPoleTask.latticeMajorant (4*a) k :=
      tsum_nonneg (fun k => by unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity)
    dsimp only [G]
    positivity
  refine ⟨max L (G*C),le_trans hL (le_max_left _ _),?_⟩
  intro t ht
  by_cases hnear : |t-θ| ≤ ρ
  · exact (remainder_local_bound a θ t ρ ha hθ hπ hρ hρθ hρπ hnear).trans (le_max_left _ _)
  by_cases hnegative : |-t-θ| ≤ ρ
  · rw [← remainder_even a θ t]
    exact (remainder_local_bound a θ (-t) ρ ha hθ hπ hρ hρθ hρπ hnegative).trans (le_max_left _ _)
  have he : t ∈ excludedCell θ ρ := by
    have h1 : ρ < |t-θ| := lt_of_not_ge hnear
    have h2 : ρ < |t+θ| := by
      have h := lt_of_not_ge hnegative
      rw [show -t-θ=-(t+θ) by ring,abs_neg] at h
      exact h
    by_cases hl : t ≤ -θ-ρ
    · exact Or.inl (Or.inl ⟨ht.1,hl⟩)
    by_cases hr : θ+ρ ≤ t
    · exact Or.inr ⟨hr,ht.2⟩
    apply Or.inl ∘ Or.inr
    constructor
    · rcases lt_abs.mp h2 with h | h <;> linarith
    · rcases lt_abs.mp h1 with h | h <;> linarith
  have hn := interpolation_global_bound a θ t ha hθ hπ (abs_le.mpr ht)
  have hk := hbound t he
  unfold remainder
  rw [div_eq_mul_one_div,norm_mul]
  exact (mul_le_mul hn hk (norm_nonneg _) hG).trans (le_max_right _ _)

lemma remainder_integrableOn (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    IntegrableOn (remainder a θ) (Icc (-Real.pi) Real.pi) := by
  obtain ⟨C,hC,hbound⟩ := remainder_bounded a θ ha hθ hπ
  apply (integrable_const C (μ := volume.restrict (Icc (-Real.pi) Real.pi))).mono'
    (remainder_measurable a θ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hbound t ht

lemma remainder_intervalIntegrable (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    IntervalIntegrable (remainder a θ) volume (-Real.pi) Real.pi := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos]) ]
  exact (remainder_integrableOn a θ ha hθ hπ).mono_set Ioc_subset_Icc_self

end ShiftedCosineTask
