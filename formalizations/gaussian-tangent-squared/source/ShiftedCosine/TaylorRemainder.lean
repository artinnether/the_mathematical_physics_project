import ShiftedCosine.CutPrimitives
import TuringTask.HadamardRemainder

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def periodWeight (a t : ℝ) : ℝ := PeriodicPoleTask.periodizedWeight (4*a) (t/2)
noncomputable def periodDerivative (a t : ℝ) : ℝ := PeriodicPoleTask.periodizedDerivative (4*a) (t/2)/2
noncomputable def periodSecond (a t : ℝ) : ℝ := PeriodicPoleTask.periodizedSecondDerivative (4*a) (t/2)/4
noncomputable def secondBound (a : ℝ) : ℝ := (∑' k : ℤ, PeriodicPoleTask.latticeSecondMajorant (4*a) k)/4
noncomputable def interpolationNumerator (a θ t : ℝ) : ℝ :=
  periodWeight a t-periodWeight a θ+(periodDerivative a θ/Real.sin θ)*(Real.cos t-Real.cos θ)
noncomputable def interpolationDerivative (a θ t : ℝ) : ℝ :=
  periodDerivative a t-(periodDerivative a θ/Real.sin θ)*Real.sin t
noncomputable def remainder (a θ t : ℝ) : ℝ := interpolationNumerator a θ t/(Real.cos t-Real.cos θ)^2

lemma periodWeight_hasDerivAt (a t : ℝ) (ha : 0 < a) (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    HasDerivAt (periodWeight a) (periodDerivative a t) t := by
  have h := (PeriodicPoleTask.periodizedWeight_hasDerivAt (4*a) (t/2) (by positivity)
    ⟨by linarith [ht.1],by linarith [ht.2]⟩).comp t ((hasDerivAt_id t).div_const 2)
  apply h.congr_deriv
  unfold periodDerivative
  ring

lemma periodDerivative_hasDerivAt (a t : ℝ) (ha : 0 < a) (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    HasDerivAt (periodDerivative a) (periodSecond a t) t := by
  have h := ((PeriodicPoleTask.periodizedDerivative_hasDerivAt (4*a) (t/2) (by positivity)
    ⟨by linarith [ht.1],by linarith [ht.2]⟩).comp t ((hasDerivAt_id t).div_const 2)).div_const 2
  apply h.congr_deriv
  unfold periodSecond
  ring

lemma secondBound_nonneg (a : ℝ) (ha : 0 < a) : 0 ≤ secondBound a := by
  unfold secondBound
  apply div_nonneg
  · apply tsum_nonneg
    intro k
    unfold PeriodicPoleTask.latticeSecondMajorant PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight
    positivity
  · norm_num

lemma periodSecond_bound (a t : ℝ) (ha : 0 < a) (ht : |t| ≤ Real.pi) :
    ‖periodSecond a t‖ ≤ secondBound a := by
  unfold periodSecond secondBound
  rw [norm_div,show ‖(4 : ℝ)‖=4 by norm_num]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply PeriodicPoleTask.periodizedSecondDerivative_bound (4*a) (t/2) (by positivity)
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  linarith

lemma interpolation_hasDerivAt (a θ t : ℝ) (ha : 0 < a) (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    HasDerivAt (interpolationNumerator a θ) (interpolationDerivative a θ t) t := by
  have h := ((periodWeight_hasDerivAt a t ha ht).sub_const (periodWeight a θ)).add
    (((Real.hasDerivAt_cos t).sub_const (Real.cos θ)).const_mul (periodDerivative a θ/Real.sin θ))
  apply h.congr_deriv
  unfold interpolationDerivative
  ring

lemma interpolationDerivative_hasDerivAt (a θ t : ℝ) (ha : 0 < a) (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    HasDerivAt (interpolationDerivative a θ)
      (periodSecond a t-(periodDerivative a θ/Real.sin θ)*Real.cos t) t :=
  (periodDerivative_hasDerivAt a t ha ht).sub ((Real.hasDerivAt_sin t).const_mul _)

lemma interpolation_second_bound (a θ t : ℝ) (ha : 0 < a) (ht : |t| ≤ Real.pi) :
    ‖periodSecond a t-(periodDerivative a θ/Real.sin θ)*Real.cos t‖ ≤
      secondBound a+‖periodDerivative a θ/Real.sin θ‖ := by
  apply (norm_sub_le _ _).trans
  apply add_le_add (periodSecond_bound a t ha ht)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one t)

lemma interpolation_quadratic_bound (a θ t ρ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hρ : 0 < ρ) (hρθ : ρ < θ) (hρπ : ρ < Real.pi-θ) (ht : |t-θ| ≤ ρ) :
    ‖interpolationNumerator a θ t‖ ≤
      (secondBound a+‖periodDerivative a θ/Real.sin θ‖)*(t-θ)^2 := by
  let B := secondBound a+‖periodDerivative a θ/Real.sin θ‖
  have hB : 0 ≤ B := add_nonneg (secondBound_nonneg a ha) (norm_nonneg _)
  let S := Icc (θ-|t-θ|) (θ+|t-θ|)
  have hsub : S ⊆ Ioo (-Real.pi) Real.pi := by
    intro y hy
    constructor <;> dsimp only [S] at hy <;> linarith [hy.1,hy.2,Real.pi_pos]
  have hθS : θ ∈ S := ⟨by linarith [abs_nonneg (t-θ)],by linarith [abs_nonneg (t-θ)]⟩
  have htS : t ∈ S := by
    have h := abs_le.mp (le_refl |t-θ|)
    constructor <;> linarith [h.1,h.2]
  have hs := (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne'
  have hd0 : interpolationDerivative a θ θ=0 := by unfold interpolationDerivative; field_simp [hs]; ring
  have hn0 : interpolationNumerator a θ θ=0 := by simp [interpolationNumerator]
  have hD (y : ℝ) (hy : y ∈ S) : ‖interpolationDerivative a θ y‖ ≤ B*|t-θ| := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (interpolationDerivative_hasDerivAt a θ z ha (hsub hz)).hasDerivWithinAt)
      (fun z hz => interpolation_second_bound a θ z ha
        (abs_le.mpr ⟨(hsub hz).1.le,(hsub hz).2.le⟩)) (convex_Icc _ _) hθS hy
    rw [hd0,sub_zero,Real.norm_eq_abs] at h
    have hdist : |y-θ| ≤ |t-θ| := by
      apply abs_le.mpr
      dsimp only [S] at hy
      constructor <;> linarith [hy.1,hy.2]
    exact h.trans (mul_le_mul_of_nonneg_left hdist hB)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (interpolation_hasDerivAt a θ z ha (hsub hz)).hasDerivWithinAt)
    hD (convex_Icc _ _) hθS htS
  rw [hn0,sub_zero,Real.norm_eq_abs] at h
  rw [Real.norm_eq_abs] at h ⊢
  calc
    _ ≤ B*|t-θ| * |t-θ| := h
    _ = _ := by rw [mul_assoc,← pow_two,sq_abs]

end ShiftedCosineTask
