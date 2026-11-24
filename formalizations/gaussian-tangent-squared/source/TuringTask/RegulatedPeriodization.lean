import TuringTask.FeynmanEvaluation
import TuringTask.PeriodizedTruncation

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set TopologicalSpace
namespace PeriodicPoleTask

lemma integral_eq_tsum_pi_cells (f : ℝ → ℝ) (hf : Integrable f) :
    (∫ x : ℝ, f x) = ∑' k : ℤ, ∫ t in (-Real.pi/2)..(Real.pi/2), f (t+(k : ℝ)*Real.pi) := by
  let g : ℝ → ℝ := fun x => f (Real.pi*x-Real.pi/2)
  have hg : Integrable g := by
    simpa only [g,sub_eq_add_neg,neg_div] using (hf.comp_add_right (-Real.pi/2)).comp_mul_left' Real.pi_ne_zero
  have hs := hg.hasSum_intervalIntegral_comp_add_int.mul_left Real.pi
  have he (k : ℤ) : Real.pi*(∫ x in (0 : ℝ)..1, g (x+k)) =
      ∫ t in (-Real.pi/2)..(Real.pi/2), f (t+(k : ℝ)*Real.pi) := by
    dsimp [g]
    have hp : (fun x : ℝ => f (Real.pi*(x+k)-Real.pi/2)) =
        (fun x : ℝ => f ((Real.pi*x-Real.pi/2)+(k : ℝ)*Real.pi)) := by
      funext x; congr 1; ring
    rw [hp]
    have hi := intervalIntegral.smul_integral_comp_mul_add
      (fun t => f (t+(k : ℝ)*Real.pi)) (a := (0 : ℝ)) (b := 1) Real.pi (-Real.pi/2)
    simpa only [sub_eq_add_neg,neg_div,smul_eq_mul,mul_zero,zero_add,mul_one,show Real.pi+-(Real.pi/2)=Real.pi/2 by ring] using hi
  have hi : Real.pi*(∫ x : ℝ, g x) = ∫ x : ℝ, f x := by
    have hscale := Measure.integral_comp_mul_left (fun y : ℝ => f (y+-(Real.pi/2))) Real.pi
    have ht : (∫ x : ℝ, g x) = Real.pi⁻¹*(∫ x : ℝ, f x) := by
      simpa only [g,sub_eq_add_neg,neg_div,integral_add_right_eq_self,abs_of_pos (inv_pos.mpr Real.pi_pos),smul_eq_mul] using hscale
    rw [ht]
    exact mul_inv_cancel_left₀ Real.pi_ne_zero _
  simp_rw [he] at hs
  rw [hi] at hs
  exact hs.tsum_eq.symm

lemma regulatedRealKernel_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (regulatedRealKernel ε) := by
  unfold regulatedRealKernel
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact pow_ne_zero 2 (ne_of_gt (by positivity : 0 < Real.sin t^2+ε^2))

lemma regulatedRealKernel_bound (ε t : ℝ) (hε : 0 < ε) :
    ‖regulatedRealKernel ε t‖ ≤ 1/ε^2 := by
  have hd : 0 < Real.sin t^2+ε^2 := by positivity
  have hn : |Real.sin t^2-ε^2| ≤ Real.sin t^2+ε^2 := abs_le.mpr ⟨by nlinarith [sq_nonneg (Real.sin t)],by nlinarith [sq_nonneg ε]⟩
  unfold regulatedRealKernel
  rw [norm_div,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (sq_pos_of_pos hd)]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  nlinarith [sq_nonneg (Real.sin t),mul_nonneg (sq_nonneg (Real.sin t)) (sq_nonneg ε),mul_le_mul_of_nonneg_right hn (sq_nonneg ε)]

lemma feynmanIntegral_re_periodized (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    (feynmanIntegral α ε).re =
      ∫ t in (-Real.pi/2)..(Real.pi/2), periodizedWeight α t*regulatedRealKernel ε t := by
  have hf : Integrable (fun x => weight α x*regulatedRealKernel ε x) := by
    have h := (feynman_integrable α ε hα hε).re
    change Integrable (fun x => (feynmanIntegrand α ε x).re) at h
    simpa only [feynmanIntegrand_re] using h
  have hre : (feynmanIntegral α ε).re = ∫ x : ℝ, weight α x*regulatedRealKernel ε x := by
    have hir : (∫ x : ℝ, (feynmanIntegrand α ε x).re) = (feynmanIntegral α ε).re :=
      integral_re (feynman_integrable α ε hα hε)
    rw [← hir]
    simp_rw [feynmanIntegrand_re]
  rw [hre,integral_eq_tsum_pi_cells _ hf]
  have hp (t : ℝ) (k : ℤ) : regulatedRealKernel ε (t+(k : ℝ)*Real.pi) = regulatedRealKernel ε t := by
    unfold regulatedRealKernel; rw [sin_sq_shift]
  simp_rw [hp]
  let f : ℤ → C(ℝ,ℝ) := fun k => ⟨fun t => weight α (t+(k : ℝ)*Real.pi)*regulatedRealKernel ε t,
    (by apply Continuous.mul (by unfold weight; fun_prop) (regulatedRealKernel_continuous ε hε))⟩
  have hn : Summable (fun k : ℤ => ‖(f k).restrict (⟨uIcc (-Real.pi/2) (Real.pi/2),isCompact_uIcc⟩ : Compacts ℝ)‖) := by
    apply ((latticeMajorant_summable α hα).div_const (ε^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    apply (ContinuousMap.norm_le _ (by unfold latticeMajorant weight; positivity)).mpr
    intro t
    have ht : (t : ℝ) ∈ uIcc (-Real.pi/2) (Real.pi/2) := t.property
    have ht' : (t : ℝ) ∈ Icc (-Real.pi/2) (Real.pi/2) := Eq.mp
      (congrArg (fun s : Set ℝ => (t : ℝ) ∈ s) (uIcc_of_le (by linarith [Real.pi_pos]))) ht
    change ‖weight α (t+(k : ℝ)*Real.pi)*regulatedRealKernel ε t‖ ≤ _
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (weight_pos _ _)]
    exact (mul_le_mul (shifted_weight_bound α t k hα (abs_le.mpr ⟨by linarith [ht'.1],ht'.2⟩))
      (regulatedRealKernel_bound ε t hε) (norm_nonneg _) (by unfold latticeMajorant weight; positivity)).trans_eq (by ring)
  change (∑' k : ℤ, ∫ t in (-Real.pi/2)..(Real.pi/2), f k t) = _
  rw [intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hn]
  apply intervalIntegral.integral_congr
  intro t ht
  change (∑' k : ℤ, weight α (t+(k : ℝ)*Real.pi)*regulatedRealKernel ε t) = _
  exact tsum_mul_right

end PeriodicPoleTask
