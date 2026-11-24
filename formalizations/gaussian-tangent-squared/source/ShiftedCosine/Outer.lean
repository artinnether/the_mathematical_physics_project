import ShiftedCosine.Series

open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def excludedCell (θ δ : ℝ) : Set ℝ :=
  Icc (-Real.pi) (-θ-δ) ∪ Icc (-θ+δ) (θ-δ) ∪ Icc (θ+δ) Real.pi

lemma excludedCell_compact (θ δ : ℝ) : IsCompact (excludedCell θ δ) :=
  (isCompact_Icc.union isCompact_Icc).union isCompact_Icc

lemma cut_cos_ne (θ δ t : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (hδ : 0 < δ)
    (ht : t ∈ excludedCell θ δ) : Real.cos t-Real.cos θ ≠ 0 := by
  have hab : |t| ≤ Real.pi := by
    rcases ht with (ht | ht) | ht
    all_goals apply abs_le.mpr; constructor <;> linarith [ht.1,ht.2]
  have hc : Real.cos |t| = Real.cos t := by
    by_cases h : 0 ≤ t
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h),Real.cos_neg]
  intro he
  have he := sub_eq_zero.mp he
  have htθ : |t|=θ := Real.injOn_cos ⟨abs_nonneg _,hab⟩ ⟨hθ.le,hπ.le⟩ (hc.trans he)
  rcases ht with (ht | ht) | ht
  · rw [abs_of_neg (by linarith [ht.2])] at htθ
    linarith [ht.2]
  · have hbound : |t| ≤ θ-δ := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
    linarith
  · rw [abs_of_pos (by linarith [ht.1])] at htθ
    linarith [ht.1]

lemma cut_kernel_bounded (θ δ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ excludedCell θ δ, ‖1/(Real.cos t-Real.cos θ)^2‖ ≤ C := by
  have hc : ContinuousOn (fun t : ℝ => 1/(Real.cos t-Real.cos θ)^2) (excludedCell θ δ) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (cut_cos_ne θ δ t hθ hπ hδ ht)
  obtain ⟨C,hC⟩ := (excludedCell_compact θ δ).exists_bound_of_continuousOn hc
  exact ⟨max C 0,le_max_right _ _,fun t ht => (hC t ht).trans (le_max_left _ _)⟩

lemma weight_cell_bound (a t : ℝ) (k : ℤ) (ha : 0 < a) (ht : |t| ≤ Real.pi) :
    weight a (2*k*Real.pi+t) ≤ PeriodicPoleTask.latticeMajorant (4*a) k := by
  rw [show 2*(k : ℝ)*Real.pi+t=2*k*Real.pi+t by rfl,shifted_weight]
  apply PeriodicPoleTask.shifted_weight_bound (4*a) (t/2) k (by positivity)
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  linarith

lemma interval_cell_bound (a θ δ u v C : ℝ) (k : ℤ) (ha : 0 < a) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ excludedCell θ δ, ‖1/(Real.cos t-Real.cos θ)^2‖ ≤ C)
    (hu : -Real.pi ≤ u) (hv : v ≤ Real.pi) (huv : u ≤ v)
    (hsubset : Icc u v ⊆ excludedCell θ δ) :
    ‖∫ t in u..v, weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2‖ ≤
      2*Real.pi*C*PeriodicPoleTask.latticeMajorant (4*a) k := by
  have hm : 0 ≤ PeriodicPoleTask.latticeMajorant (4*a) k := by
    unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := C*PeriodicPoleTask.latticeMajorant (4*a) k)
    (f := fun t : ℝ => weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2) ?_
  · rw [abs_of_nonneg (sub_nonneg.mpr huv)] at h
    have hlen : v-u ≤ 2*Real.pi := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlen (mul_nonneg hC hm)]
  · intro t ht
    rw [uIoc_of_le huv] at ht
    have he := hsubset ⟨ht.1.le,ht.2⟩
    have hw := weight_cell_bound a t k ha (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    have hn : ‖weight a (2*k*Real.pi+t)‖=weight a (2*k*Real.pi+t) := by
      rw [Real.norm_eq_abs,abs_of_pos (show 0 < weight a (2*k*Real.pi+t) from Real.exp_pos _)]
    rw [div_eq_mul_one_div,norm_mul,hn]
    exact (mul_le_mul hw (hbound t he) (norm_nonneg _) hm).trans (by ring_nf; rfl)

lemma cell_summable (a θ δ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ) : Summable (cell a θ δ) := by
  obtain ⟨C,hC,hbound⟩ := cut_kernel_bounded θ δ hθ hπ hδ
  have hB (k : ℤ) : ‖cell a θ δ k‖ ≤ 6*Real.pi*C*PeriodicPoleTask.latticeMajorant (4*a) k := by
    have hleft := interval_cell_bound a θ δ (-Real.pi) (-θ-δ) C k ha hC hbound
      (by rfl) (by linarith) (by linarith) (fun t ht => Or.inl (Or.inl ht))
    have hmid := interval_cell_bound a θ δ (-θ+δ) (θ-δ) C k ha hC hbound
      (by linarith) (by linarith) (by linarith) (fun t ht => Or.inl (Or.inr ht))
    have hright := interval_cell_bound a θ δ (θ+δ) Real.pi C k ha hC hbound
      (by linarith) (by rfl) (by linarith) (fun t ht => Or.inr ht)
    unfold cell
    calc
      _ ≤ ‖∫ t in (-Real.pi)..(-θ-δ), weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2‖ +
        ‖∫ t in (-θ+δ)..(θ-δ), weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2‖ +
        ‖∫ t in (θ+δ)..Real.pi, weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  exact ((PeriodicPoleTask.latticeMajorant_summable (4*a) (by positivity)).mul_left
    (6*Real.pi*C)).of_norm_bounded hB

noncomputable def outerValue (a θ δ : ℝ) : ℝ := ∑' k : ℤ, cell a θ δ k

lemma truncation_tendsto (a θ δ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ) :
    Tendsto (truncation a θ δ) atTop (𝓝 (outerValue a θ δ)) :=
  (cell_summable a θ δ ha hθ hπ hδ hδθ hδπ).hasSum.comp (Finset.tendsto_Icc_neg (R := ℤ))

end ShiftedCosineTask
