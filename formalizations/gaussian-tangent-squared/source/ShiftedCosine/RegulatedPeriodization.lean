import ShiftedCosine.HadamardConstruction
import ShiftedCosine.RegulatedCells

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology
namespace ShiftedCosineTask

lemma integral_eq_tsum_cells (f : ℝ → ℂ) (hf : Integrable f) (T : ℝ) (hT : 0 < T) :
    (∫ x : ℝ,f x)=∑' k : ℤ,∫ t in (-T/2)..(T/2),f (t+k*T) := by
  let g : ℝ → ℂ := fun x => f (T*x-T/2)
  have hg : Integrable g := by
    simpa only [g,sub_eq_add_neg,neg_div] using (hf.comp_add_right (-T/2)).comp_mul_left' hT.ne'
  have hs := hg.hasSum_intervalIntegral_comp_add_int.const_smul T
  have he (k : ℤ) : T • (∫ x in (0 : ℝ)..1,g (x+k))=
      ∫ t in (-T/2)..(T/2),f (t+k*T) := by
    dsimp only [g]
    have hp : (fun x : ℝ => f (T*(x+k)-T/2))=(fun x : ℝ => f ((T*x-T/2)+k*T)) := by
      funext x; congr 1; ring
    rw [hp]
    have hi := intervalIntegral.smul_integral_comp_mul_add (fun t => f (t+k*T))
      (a := (0 : ℝ)) (b := 1) T (-T/2)
    simpa only [sub_eq_add_neg,neg_div,mul_zero,zero_add,mul_one,show T+-(T/2)=T/2 by ring] using hi
  have hi : T • (∫ x : ℝ,g x)=∫ x : ℝ,f x := by
    have hscale := Measure.integral_comp_mul_left (fun y : ℝ => f (y+-(T/2))) T
    have ht : (∫ x : ℝ,g x)=T⁻¹ • (∫ x : ℝ,f x) := by
      simpa only [g,sub_eq_add_neg,neg_div,integral_add_right_eq_self,abs_of_pos (inv_pos.mpr hT)] using hscale
    rw [ht,smul_smul,mul_inv_cancel₀ hT.ne',one_smul]
  simp_rw [he] at hs
  rw [hi] at hs
  exact hs.tsum_eq.symm

noncomputable def complexKernel (θ ε t : ℝ) : ℂ := 1/((Real.cos t : ℂ)-regulatorZ θ ε)^2

lemma complexKernel_continuous (θ ε : ℝ) (hε : 0 < ε) : Continuous (complexKernel θ ε) := by
  unfold complexKernel regulatorZ
  apply Continuous.div continuous_const (by fun_prop)
  intro t
  apply pow_ne_zero
  have he : (Real.cos t : ℂ)-((Real.cos θ : ℂ)-Complex.I*(ε : ℂ))=
      (((Real.cos t-Real.cos θ : ℝ) : ℂ)+Complex.I*(ε : ℂ)) := by push_cast; ring
  rw [he]
  exact feynman_denominator_ne_zero θ ε t hε

lemma complexKernel_bound (θ ε t : ℝ) (hε : 0 < ε) : ‖complexKernel θ ε t‖ ≤ 1/ε^2 := by
  have hd : ε ≤ ‖(Real.cos t : ℂ)-regulatorZ θ ε‖ := by
    have h := Complex.abs_im_le_norm ((Real.cos t : ℂ)-regulatorZ θ ε)
    simpa [regulatorZ,abs_of_pos hε] using h
  unfold complexKernel
  rw [norm_div,norm_one,norm_pow]
  exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hε) (pow_le_pow_left₀ hε.le hd 2)

lemma complexKernel_shift (θ ε t : ℝ) (k : ℤ) : complexKernel θ ε (t+k*(2*Real.pi))=complexKernel θ ε t := by
  unfold complexKernel
  rw [Real.cos_add_int_mul_two_pi]

lemma feynmanIntegral_periodized (a θ ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    feynmanIntegral a θ ε=∫ t in (-Real.pi)..Real.pi,(periodWeight a t : ℂ)*complexKernel θ ε t := by
  have hp (x : ℝ) : feynmanIntegrand a θ ε x=(weight a x : ℂ)*complexKernel θ ε x := by
    unfold feynmanIntegrand complexKernel regulatorZ
    push_cast
    ring
  unfold feynmanIntegral
  rw [integral_eq_tsum_cells _ (feynman_integrable a θ ε ha hε) (2*Real.pi) (by positivity)]
  simp_rw [hp,complexKernel_shift]
  have he1 : -(2*Real.pi)/2=-Real.pi := by ring
  have he2 : (2*Real.pi)/2=Real.pi := by ring
  rw [he1,he2]
  let f : ℤ → C(ℝ,ℂ) := fun k => ⟨fun t => (weight a (t+k*(2*Real.pi)) : ℂ)*complexKernel θ ε t,
    (by apply Continuous.mul (by unfold weight; fun_prop) (complexKernel_continuous θ ε hε))⟩
  have hn : Summable (fun k : ℤ => ‖(f k).restrict (⟨uIcc (-Real.pi) Real.pi,isCompact_uIcc⟩ : Compacts ℝ)‖) := by
    apply ((PeriodicPoleTask.latticeMajorant_summable (4*a) (by positivity)).div_const (ε^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    apply (ContinuousMap.norm_le _ (by unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity)).2
    intro t
    have ht0 : (t : ℝ) ∈ uIcc (-Real.pi) Real.pi := t.property
    have ht : (t : ℝ) ∈ Icc (-Real.pi) Real.pi :=
      Eq.mp (congrArg (fun s : Set ℝ => (t : ℝ) ∈ s) (uIcc_of_le (by linarith [Real.pi_pos]))) ht0
    change ‖(weight a ((t : ℝ)+k*(2*Real.pi)) : ℂ)*complexKernel θ ε t‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0 < weight a ((t : ℝ)+k*(2*Real.pi)) from Real.exp_pos _)]
    have hw := weight_cell_bound a t k ha (abs_le.mpr ht)
    rw [show 2*(k : ℝ)*Real.pi+(t : ℝ)=(t : ℝ)+k*(2*Real.pi) by ring] at hw
    exact (mul_le_mul hw (complexKernel_bound θ ε t hε) (norm_nonneg _)
      (by unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity)).trans_eq (by ring)
  change (∑' k : ℤ,∫ t in (-Real.pi)..Real.pi,f k t)=_
  rw [intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hn]
  apply intervalIntegral.integral_congr
  intro t ht
  change (∑' k : ℤ,(weight a (t+k*(2*Real.pi)) : ℂ)*complexKernel θ ε t)=_
  rw [tsum_mul_right,← Complex.ofReal_tsum]
  congr 1
  rw [periodWeight_tsum]
  apply congrArg Complex.ofReal
  apply tsum_congr
  intro k
  congr 1
  ring

end ShiftedCosineTask
