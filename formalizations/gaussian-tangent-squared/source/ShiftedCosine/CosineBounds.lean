import ShiftedCosine.TaylorRemainder

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

lemma sine_margin_bound (x ρ : ℝ) (hρ : 0 < ρ) (hx : ρ ≤ x) (hxπ : x ≤ Real.pi-ρ) :
    2*ρ ≤ Real.pi*|Real.sin x| := by
  by_cases hhalf : x ≤ Real.pi/2
  · have hb := Real.mul_abs_le_abs_sin (abs_le.mpr ⟨by linarith [Real.pi_pos],hhalf⟩)
    have hb := mul_le_mul_of_nonneg_left hb Real.pi_pos.le
    rw [abs_of_pos (by linarith : 0 < x)] at hb
    field_simp at hb
    linarith
  · have hmir : 0 < Real.pi-x := by linarith
    have hb := Real.mul_abs_le_abs_sin (abs_le.mpr
      ⟨by linarith [Real.pi_pos],by linarith⟩ : |Real.pi-x| ≤ Real.pi/2)
    rw [Real.sin_pi_sub,abs_of_pos hmir] at hb
    have hb := mul_le_mul_of_nonneg_left hb Real.pi_pos.le
    field_simp at hb
    linarith

lemma cosine_local_bound (θ t ρ : ℝ) (hρ : 0 < ρ) (hρθ : 2*ρ ≤ θ)
    (hρπ : 2*ρ ≤ Real.pi-θ) (ht : |t-θ| ≤ ρ) :
    4*ρ*|t-θ| ≤ Real.pi^2*|Real.cos t-Real.cos θ| := by
  have hab := abs_le.mp ht
  have hA := sine_margin_bound ((t+θ)/2) ρ hρ (by linarith [hab.1]) (by linarith [hab.2])
  have hρp : ρ ≤ Real.pi := by linarith
  have hB := Real.mul_abs_le_abs_sin (show |(t-θ)/2| ≤ Real.pi/2 by
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]; linarith)
  have hB := mul_le_mul_of_nonneg_left hB Real.pi_pos.le
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hB
  field_simp at hB
  have hp := mul_le_mul hA hB (abs_nonneg _) (by positivity : 0 ≤ Real.pi*|Real.sin ((t+θ)/2)|)
  rw [Real.cos_sub_cos,abs_mul,abs_mul,abs_of_neg (by norm_num : (-2 : ℝ)<0)]
  nlinarith [hp]

lemma remainder_local_bound (a θ t ρ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hρ : 0 < ρ) (hρθ : 2*ρ ≤ θ) (hρπ : 2*ρ ≤ Real.pi-θ) (ht : |t-θ| ≤ ρ) :
    ‖remainder a θ t‖ ≤ (secondBound a+‖periodDerivative a θ/Real.sin θ‖)*Real.pi^4/(16*ρ^2) := by
  let B := secondBound a+‖periodDerivative a θ/Real.sin θ‖
  have hB : 0 ≤ B := add_nonneg (secondBound_nonneg a ha) (norm_nonneg _)
  have hb := cosine_local_bound θ t ρ hρ hρθ hρπ ht
  have hn := interpolation_quadratic_bound a θ t ρ ha hθ hπ hρ (by linarith) (by linarith) ht
  by_cases he : t=θ
  · subst t
    simp only [remainder,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),div_zero,norm_zero]
    positivity
  have hd : Real.cos t-Real.cos θ ≠ 0 := by
    intro hd
    rw [hd,abs_zero,mul_zero] at hb
    have hp : 0 < 4*ρ*|t-θ| := by
      apply mul_pos (by positivity) (abs_pos.mpr (sub_ne_zero.mpr he))
    linarith
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 4*ρ*|t-θ|) hb 2
  have hsquare : 16*ρ^2*(t-θ)^2 ≤ Real.pi^4*(Real.cos t-Real.cos θ)^2 := by
    calc
      _ = (4*ρ*|t-θ|)^2 := by simp only [mul_pow,sq_abs]; ring
      _ ≤ (Real.pi^2*|Real.cos t-Real.cos θ|)^2 := hsquare
      _ = _ := by simp only [mul_pow,sq_abs]; ring
  unfold remainder
  rw [norm_div,Real.norm_eq_abs (r := (Real.cos t-Real.cos θ)^2),abs_of_pos (sq_pos_of_ne_zero hd)]
  apply (div_le_iff₀ (sq_pos_of_ne_zero hd)).2
  have hm := mul_le_mul_of_nonneg_left hsquare hB
  have hmul := mul_le_mul_of_nonneg_left hn (show 0 ≤ 16*ρ^2 by positivity)
  change ‖interpolationNumerator a θ t‖ ≤ B*Real.pi^4/(16*ρ^2)*(Real.cos t-Real.cos θ)^2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 16*ρ^2 by positivity)).2
  nlinarith [hm,hmul]

end ShiftedCosineTask
