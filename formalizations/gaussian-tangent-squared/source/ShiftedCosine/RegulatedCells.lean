import ShiftedCosine.FeynmanLimit

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology
namespace ShiftedCosineTask

lemma harmonic_cell_integral (n : ℕ) : (∫ t in (-Real.pi)..Real.pi,Real.cos ((n+1 : ℝ)*t))=0 := by
  let c : ℝ := n+1
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => Real.sin (c*x)/c) (Real.cos (c*t)) t := by
    convert ((Real.hasDerivAt_sin (c*t)).comp t ((hasDerivAt_id t).const_mul c)).div_const c using 1 <;>
      (try rfl); field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (by apply Continuous.intervalIntegrable; fun_prop)]
  have hr : c*Real.pi=((n+1 : ℕ) : ℝ)*Real.pi := by dsimp [c]; push_cast; rfl
  have hl : c*(-Real.pi)=-(((n+1 : ℕ) : ℝ)*Real.pi) := by dsimp [c]; push_cast; ring
  rw [hr,hl,Real.sin_neg,Real.sin_nat_mul_pi]
  simp

lemma complexSeries_cell_integral (b : ℕ → ℂ) (hb : Summable b) :
    (∫ t in (-Real.pi)..Real.pi,complexCosineSeries b t)=0 := by
  let f : ℕ → C(ℝ,ℂ) := fun n => ⟨fun t => b n*(Real.cos ((n+1 : ℝ)*t) : ℂ),by fun_prop⟩
  have hn : Summable (fun n => ‖(f n).restrict (⟨uIcc (-Real.pi) Real.pi,isCompact_uIcc⟩ : Compacts ℝ)‖) := by
    apply hb.norm.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro t
    exact complexSeries_bound b n t
  change (∫ t in (-Real.pi)..Real.pi,∑' n,f n t)=_
  rw [← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hn]
  have he (n : ℕ) : (∫ t in (-Real.pi)..Real.pi,f n t)=0 := by
    change (∫ t in (-Real.pi)..Real.pi,b n*(Real.cos ((n+1 : ℝ)*t) : ℂ))=0
    rw [intervalIntegral.integral_const_mul]
    have hreal := harmonic_cell_integral n
    have hcast : (∫ t in (-Real.pi)..Real.pi,(Real.cos ((n+1 : ℝ)*t) : ℂ))=
        ((∫ t in (-Real.pi)..Real.pi,Real.cos ((n+1 : ℝ)*t) : ℝ) : ℂ) := by
      have hi : IntervalIntegrable (fun t : ℝ => Real.cos ((n+1 : ℝ)*t)) volume (-Real.pi) Real.pi :=
        (show Continuous (fun t : ℝ => Real.cos ((n+1 : ℝ)*t)) by fun_prop).intervalIntegrable _ _
      exact Complex.ofRealCLM.intervalIntegral_comp_comm hi
    rw [hcast,hreal,Complex.ofReal_zero,mul_zero]
  simp_rw [he]
  exact tsum_zero

lemma simple_kernel_fourier (θ ε x : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (hε : 0 < ε) :
    1/((Real.cos x : ℂ)-regulatorZ θ ε)=
      -(1/regulatorD θ ε)*(1+2*complexCosineSeries (fun n => regulatorQ θ ε^(n+1)) x) := by
  let q := regulatorQ θ ε
  have hq : ‖q‖ < 1 := regulatorQ_norm_lt_one θ ε hθ hπ hε
  have hq0 : q ≠ 0 := regulatorQ_ne_zero θ ε hθ hπ
  have hD := complex_geometricDenominator_ne q x hq
  rw [complex_geometric_tsum q x hq,regulatorZ_of_Q θ ε hθ hπ,regulatorD_of_Q θ ε hθ hπ]
  change 1/((Real.cos x : ℂ)-(1+q^2)/(2*q))=-(1/((1-q^2)/(2*q)))*((1-q^2)/(1-2*q*(Real.cos x : ℂ)+q^2))
  have hs : 1-q^2 ≠ 0 := by
    intro h
    have hn := congrArg norm ((sub_eq_zero.mp h).symm : q^2=1)
    rw [norm_pow,norm_one] at hn
    nlinarith [norm_nonneg q]
  have he : (Real.cos x : ℂ)-(1+q^2)/(2*q)=-(1-2*q*(Real.cos x : ℂ)+q^2)/(2*q) := by
    field_simp [hq0]
    ring
  rw [he]
  field_simp [hq0,hs,hD]

lemma regulated_simple_cell (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (hε : 0 < ε) :
    (∫ t in (-Real.pi)..Real.pi,1/((Real.cos t : ℂ)-regulatorZ θ ε)) =
      -(2*Real.pi : ℂ)/regulatorD θ ε := by
  have hq := regulatorQ_norm_lt_one θ ε hθ hπ hε
  have hb := complex_geometric_summable (regulatorQ θ ε) hq
  simp_rw [simple_kernel_fourier θ ε _ hθ hπ hε]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
    (continuous_const.intervalIntegrable _ _) (((complexSeries_continuous _ hb).intervalIntegrable _ _).const_mul 2),
    intervalIntegral.integral_const_mul,complexSeries_cell_integral _ hb,intervalIntegral.integral_const]
  simp only [mul_zero,add_zero,Complex.real_smul]
  push_cast
  ring

lemma regulated_double_cell (θ ε : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (hε : 0 < ε) :
    (∫ t in (-Real.pi)..Real.pi,1/((Real.cos t : ℂ)-regulatorZ θ ε)^2) =
      (2*Real.pi : ℂ)*regulatorZ θ ε/regulatorD θ ε^3 := by
  have hq := regulatorQ_norm_lt_one θ ε hθ hπ hε
  have hb := complex_geometric_summable (regulatorQ θ ε) hq
  have hc := complex_weighted_geometric_summable (regulatorQ θ ε) hq
  simp_rw [feynman_kernel_fourier θ ε _ hθ hπ hε]
  have hL : IntervalIntegrable (fun t : ℝ => regulatorZ θ ε/regulatorD θ ε^3*
      (1+2*complexCosineSeries (fun n => regulatorQ θ ε^(n+1)) t)) volume (-Real.pi) Real.pi := by
    exact (((continuous_const.add ((complexSeries_continuous _ hb).const_mul 2)).intervalIntegrable _ _).const_mul _)
  have hR : IntervalIntegrable (fun t : ℝ => 2/regulatorD θ ε^2*
      complexCosineSeries (fun n => (n+1 : ℂ)*regulatorQ θ ε^(n+1)) t) volume (-Real.pi) Real.pi :=
    ((complexSeries_continuous _ hc).intervalIntegrable _ _).const_mul _
  rw [intervalIntegral.integral_add hL hR,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
      (((complexSeries_continuous _ hb).intervalIntegrable _ _).const_mul 2),
    intervalIntegral.integral_const_mul,complexSeries_cell_integral _ hb,complexSeries_cell_integral _ hc,
    intervalIntegral.integral_const]
  simp only [mul_zero,add_zero,Complex.real_smul]
  push_cast
  ring

end ShiftedCosineTask
