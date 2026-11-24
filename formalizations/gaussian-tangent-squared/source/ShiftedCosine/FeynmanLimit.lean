import ShiftedCosine.FeynmanEvaluation

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def unitPhase (θ : ℝ) : ℂ := (Real.cos θ : ℂ)+Complex.I*(Real.sin θ : ℂ)

lemma unitPhase_eq_exp (θ : ℝ) : unitPhase θ=Complex.exp ((θ : ℂ)*Complex.I) := by
  apply Complex.ext <;> simp only [unitPhase,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im] <;> ring

lemma unitPhase_pow (θ : ℝ) (n : ℕ) : unitPhase θ^n=unitPhase ((n : ℝ)*θ) := by
  rw [unitPhase_eq_exp,unitPhase_eq_exp,← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma unitPhase_norm (θ : ℝ) : ‖unitPhase θ‖=1 := by
  rw [unitPhase_eq_exp,Complex.norm_exp_ofReal_mul_I]

lemma phase_gaussian_summable (a θ : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => unitPhase θ^(n+1)*(gaussianTerm a n : ℂ)) := by
  apply (gaussianTerm_summable a ha).of_norm_bounded
  intro n
  rw [norm_mul,norm_pow,unitPhase_norm,one_pow,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0 < gaussianTerm a n from Real.exp_pos _)]

lemma weighted_phase_gaussian_summable (a θ : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => (n+1 : ℂ)*unitPhase θ^(n+1)*(gaussianTerm a n : ℂ)) := by
  apply (weightedTerm_summable a ha).of_norm_bounded
  intro n
  rw [norm_mul,norm_mul,norm_pow,unitPhase_norm,one_pow,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0 < gaussianTerm a n from Real.exp_pos _)]
  norm_cast

lemma regulated_geometric_tendsto (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun ε : ℝ => ∑' n : ℕ, regulatorQ θ ε^(n+1)*(gaussianTerm a n : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (∑' n : ℕ, unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))) := by
  apply tendsto_tsum_of_dominated_convergence (gaussianTerm_summable a ha)
  · intro n
    exact ((regulatorQ_tendsto θ hθ hπ).pow (n+1)).mul_const _
  · filter_upwards [self_mem_nhdsWithin] with ε hε n
    have hq := (regulatorQ_norm_lt_one θ ε hθ hπ hε).le
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0 < gaussianTerm a n from Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (pow_le_one₀ (norm_nonneg _) hq)

lemma regulated_weighted_tendsto (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun ε : ℝ => ∑' n : ℕ, (n+1 : ℂ)*regulatorQ θ ε^(n+1)*(gaussianTerm a n : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (∑' n : ℕ, (n+1 : ℂ)*unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))) := by
  apply tendsto_tsum_of_dominated_convergence (weightedTerm_summable a ha)
  · intro n
    exact ((regulatorQ_tendsto θ hθ hπ).pow (n+1)).const_mul _ |>.mul_const _
  · filter_upwards [self_mem_nhdsWithin] with ε hε n
    have hq := (regulatorQ_norm_lt_one θ ε hθ hπ hε).le
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0 < gaussianTerm a n from Real.exp_pos _)]
    have hn : ‖(n+1 : ℂ)‖=(n+1 : ℝ) := by norm_cast
    rw [hn]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show ‖regulatorQ θ ε‖^(n+1) ≤ 1 from
        pow_le_one₀ (norm_nonneg _) hq) (by positivity))
      (show 0 ≤ gaussianTerm a n from (Real.exp_pos _).le)).trans_eq (by ring)

noncomputable def complexBoundaryValue (a θ : ℝ) : ℂ :=
  (Real.sqrt (Real.pi/a) : ℂ)*
    ((Real.cos θ : ℂ)/(-Complex.I*(Real.sin θ : ℂ))^3*
      (1+2*∑' n : ℕ, unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))+
    2/(-Complex.I*(Real.sin θ : ℂ))^2*
      ∑' n : ℕ, (n+1 : ℂ)*unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))

lemma feynmanIntegral_tendsto_boundary (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (feynmanIntegral a θ) (𝓝[>] (0 : ℝ)) (𝓝 (complexBoundaryValue a θ)) := by
  have hz : Tendsto (regulatorZ θ) (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos θ : ℂ)) := by
    have hc : ContinuousAt (regulatorZ θ) 0 := by unfold regulatorZ; fun_prop
    simpa [regulatorZ] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hd := regulatorD_tendsto θ hθ hπ
  have hd0 : -Complex.I*(Real.sin θ : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne')
  have hG := regulated_geometric_tendsto a θ ha hθ hπ
  have hW := regulated_weighted_tendsto a θ ha hθ hπ
  have h := (tendsto_const_nhds (x := (Real.sqrt (Real.pi/a) : ℂ))).mul
    (((hz.div (hd.pow 3) (pow_ne_zero 3 hd0)).mul
      ((tendsto_const_nhds (x := (1 : ℂ))).add (hG.const_mul 2))).add
      (((tendsto_const_nhds (x := (2 : ℂ))).div (hd.pow 2) (pow_ne_zero 2 hd0)).mul hW))
  change Tendsto (regulatedSpectralValue a θ) _ (𝓝 (complexBoundaryValue a θ)) at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (feynmanIntegral_eq a θ ε ha hθ hπ hε).symm

lemma boundary_constants (θ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    (Real.cos θ : ℂ)/(-Complex.I*(Real.sin θ : ℂ))^3 =
      ((-Real.cos θ/Real.sin θ^3 : ℝ) : ℂ)*Complex.I ∧
    2/(-Complex.I*(Real.sin θ : ℂ))^2 = ((-2/Real.sin θ^2 : ℝ) : ℂ) := by
  have hs : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne'
  constructor
  · push_cast
    field_simp [hs]
    ring_nf
    simp
  · push_cast
    field_simp [hs]
    ring_nf
    simp [Complex.I_sq]

lemma complexBoundaryValue_eq (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    complexBoundaryValue a θ = (finitePartValue a θ : ℂ)+Complex.I*(imaginaryValue a θ : ℂ) := by
  have hU := phase_gaussian_summable a θ ha
  have hV := weighted_phase_gaussian_summable a θ ha
  have hR : Summable (fun n : ℕ => ((realCoefficient θ n*gaussianTerm a n : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr (real_spectral_summable a θ ha hθ hπ)
  have hI : Summable (fun n : ℕ => ((imaginaryCoefficient θ n*gaussianTerm a n : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr (imaginary_spectral_summable a θ ha hθ hπ)
  let A : ℂ := ((-Real.cos θ/Real.sin θ^3 : ℝ) : ℂ)*Complex.I
  let B : ℂ := ((-2/Real.sin θ^2 : ℝ) : ℂ)
  have hpoint (n : ℕ) :
      (2*A)*(unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))+
      B*((n+1 : ℂ)*unitPhase θ^(n+1)*(gaussianTerm a n : ℂ)) =
      2*((realCoefficient θ n*gaussianTerm a n : ℝ) : ℂ)+
        2*Complex.I*((imaginaryCoefficient θ n*gaussianTerm a n : ℝ) : ℂ) := by
    rw [unitPhase_pow]
    unfold A B unitPhase realCoefficient imaginaryCoefficient
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hsum : (2*A)*(∑' n : ℕ, unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))+
      B*(∑' n : ℕ, (n+1 : ℂ)*unitPhase θ^(n+1)*(gaussianTerm a n : ℂ)) =
      2*((∑' n : ℕ, realCoefficient θ n*gaussianTerm a n : ℝ) : ℂ)+
        2*Complex.I*((∑' n : ℕ, imaginaryCoefficient θ n*gaussianTerm a n : ℝ) : ℂ) := by
    rw [← tsum_mul_left,← tsum_mul_left,← (hU.mul_left (2*A)).tsum_add (hV.mul_left B)]
    simp_rw [hpoint]
    rw [(hR.mul_left 2).tsum_add (hI.mul_left (2*Complex.I)),tsum_mul_left,tsum_mul_left,
      ← Complex.ofReal_tsum,← Complex.ofReal_tsum]
  unfold complexBoundaryValue
  rw [(boundary_constants θ hθ hπ).1,(boundary_constants θ hθ hπ).2]
  change (Real.sqrt (Real.pi/a) : ℂ)*(A*(1+2*∑' n : ℕ, unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))+
    B*(∑' n : ℕ, (n+1 : ℂ)*unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))) = _
  rw [show A*(1+2*∑' n : ℕ, unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))+
      B*(∑' n : ℕ, (n+1 : ℂ)*unitPhase θ^(n+1)*(gaussianTerm a n : ℂ)) =
      A+((2*A)*(∑' n : ℕ, unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))+
        B*(∑' n : ℕ, (n+1 : ℂ)*unitPhase θ^(n+1)*(gaussianTerm a n : ℂ))) by ring,hsum]
  unfold A finitePartValue imaginaryValue
  push_cast
  ring

lemma feynmanIntegral_tendsto (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (feynmanIntegral a θ) (𝓝[>] (0 : ℝ))
      (𝓝 ((finitePartValue a θ : ℂ)+Complex.I*(imaginaryValue a θ : ℂ))) := by
  rw [← complexBoundaryValue_eq a θ ha hθ hπ]
  exact feynmanIntegral_tendsto_boundary a θ ha hθ hπ

end ShiftedCosineTask
