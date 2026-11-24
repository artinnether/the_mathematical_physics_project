import ShiftedCosine.RegulatorParameters

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

lemma feynman_kernel_fourier (θ ε x : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (hε : 0 < ε) :
    1/((Real.cos x : ℂ)-regulatorZ θ ε)^2 =
      regulatorZ θ ε/regulatorD θ ε^3*
        (1+2*complexCosineSeries (fun n => regulatorQ θ ε^(n+1)) x)+
      2/regulatorD θ ε^2*
        complexCosineSeries (fun n => (n+1 : ℂ)*regulatorQ θ ε^(n+1)) x := by
  have h := complex_kernel_fourier (regulatorQ θ ε) x
    (regulatorQ_norm_lt_one θ ε hθ hπ hε) (regulatorQ_ne_zero θ ε hθ hπ)
  rw [← regulatorZ_of_Q θ ε hθ hπ,← regulatorD_of_Q θ ε hθ hπ] at h
  exact h

lemma complex_geometric_summable (q : ℂ) (hq : ‖q‖ < 1) : Summable (fun n : ℕ => q^(n+1)) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_norm_lt_one hq)

lemma complex_weighted_geometric_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => (n+1 : ℂ)*q^(n+1)) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hq).summable
  have h := (summable_nat_add_iff 1).mpr h
  simpa only [Nat.cast_add,Nat.cast_one] using h

noncomputable def regulatedSpectralValue (a θ ε : ℝ) : ℂ :=
  (Real.sqrt (Real.pi/a) : ℂ)*
    (regulatorZ θ ε/regulatorD θ ε^3*
      (1+2*∑' n : ℕ, regulatorQ θ ε^(n+1)*(gaussianTerm a n : ℂ))+
    2/regulatorD θ ε^2*
      ∑' n : ℕ, (n+1 : ℂ)*regulatorQ θ ε^(n+1)*(gaussianTerm a n : ℂ))

lemma feynmanIntegral_eq (a θ ε : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hε : 0 < ε) : feynmanIntegral a θ ε=regulatedSpectralValue a θ ε := by
  let q := regulatorQ θ ε
  let b : ℕ → ℂ := fun n => q^(n+1)
  let c : ℕ → ℂ := fun n => (n+1 : ℂ)*q^(n+1)
  have hq := regulatorQ_norm_lt_one θ ε hθ hπ hε
  have hb : Summable b := complex_geometric_summable q hq
  have hc : Summable c := complex_weighted_geometric_summable q hq
  have hw : Integrable (fun x : ℝ => (weight a x : ℂ)) := (integrable_exp_neg_mul_sq ha).ofReal
  have hB := gaussian_complexSeries_integrable a ha b hb
  have hC := gaussian_complexSeries_integrable a ha c hc
  have hpoint (x : ℝ) : feynmanIntegrand a θ ε x =
      (regulatorZ θ ε/regulatorD θ ε^3)*
        ((weight a x : ℂ)+2*((weight a x : ℂ)*complexCosineSeries b x))+
      (2/regulatorD θ ε^2)*((weight a x : ℂ)*complexCosineSeries c x) := by
    have he : (((Real.cos x-Real.cos θ : ℝ) : ℂ)+Complex.I*(ε : ℂ)) =
      (Real.cos x : ℂ)-regulatorZ θ ε := by unfold regulatorZ; push_cast; ring
    unfold feynmanIntegrand
    rw [he,div_eq_mul_one_div,feynman_kernel_fourier θ ε x hθ hπ hε]
    dsimp only [b,c,q]
    ring
  unfold feynmanIntegral
  simp_rw [hpoint]
  have hleft := (hw.add (hB.const_mul 2)).const_mul (regulatorZ θ ε/regulatorD θ ε^3)
  dsimp only [Pi.add_apply] at hleft
  rw [integral_add hleft (hC.const_mul (2/regulatorD θ ε^2)),integral_const_mul,integral_const_mul,
    integral_add hw (hB.const_mul (2 : ℂ)),integral_const_mul,
    gaussian_complexSeries_integral a ha b hb,gaussian_complexSeries_integral a ha c hc,
    integral_complex_ofReal]
  have hg : (∫ x : ℝ, weight a x)=Real.sqrt (Real.pi/a) := integral_gaussian a
  rw [hg]
  unfold regulatedSpectralValue
  dsimp only [b,c,q]
  ring

end ShiftedCosineTask
