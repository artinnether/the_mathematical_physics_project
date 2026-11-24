import ShiftedCosine.Poisson

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def massCosineSum (a θ : ℝ) : ℝ :=
  ∑' n : ℕ, gaussianTerm a n*Real.cos ((n+1 : ℝ)*θ)
noncomputable def massSineSum (a θ : ℝ) : ℝ :=
  ∑' n : ℕ, (n+1 : ℝ)*gaussianTerm a n*Real.sin ((n+1 : ℝ)*θ)

lemma massCosine_summable (a θ : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => gaussianTerm a n*Real.cos ((n+1 : ℝ)*θ)) := by
  apply (gaussianTerm_summable a ha).of_norm_bounded
  intro n
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (show 0 < gaussianTerm a n from Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)

lemma massSine_summable (a θ : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => (n+1 : ℝ)*gaussianTerm a n*Real.sin ((n+1 : ℝ)*θ)) := by
  apply (weightedTerm_summable a ha).of_norm_bounded
  intro n
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (show 0 ≤ gaussianTerm a n from (Real.exp_pos _).le) : 0 ≤ (n+1 : ℝ)*gaussianTerm a n)]
  exact mul_le_of_le_one_right (mul_nonneg (by positivity) (show 0 ≤ gaussianTerm a n from (Real.exp_pos _).le)) (by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one _)

lemma massCosine_hasDerivAt (a θ : ℝ) (ha : 0 < a) :
    HasDerivAt (massCosineSum a) (-massSineSum a θ) θ := by
  have h := hasDerivAt_tsum_of_isPreconnected (weightedTerm_summable a ha) isOpen_univ
    isPreconnected_univ
    (g := fun (n : ℕ) (t : ℝ) => gaussianTerm a n*Real.cos ((n+1 : ℝ)*t))
    (g' := fun (n : ℕ) (t : ℝ) => -(n+1 : ℝ)*gaussianTerm a n*Real.sin ((n+1 : ℝ)*t))
    (y₀ := (0 : ℝ)) (y := θ) ?_ ?_ (mem_univ _) (massCosine_summable a 0 ha) (mem_univ _)
  · change HasDerivAt (massCosineSum a)
      (∑' n : ℕ, -(n+1 : ℝ)*gaussianTerm a n*Real.sin ((n+1 : ℝ)*θ)) θ at h
    have he : (∑' n : ℕ, -(n+1 : ℝ)*gaussianTerm a n*Real.sin ((n+1 : ℝ)*θ)) = -massSineSum a θ := by
      unfold massSineSum
      rw [← tsum_neg]
      apply tsum_congr
      intro n
      ring
    rw [he] at h
    exact h
  · intro n t ht
    have hd := ((Real.hasDerivAt_cos ((n+1 : ℝ)*t)).comp t
      ((hasDerivAt_id t).const_mul (n+1 : ℝ))).const_mul (gaussianTerm a n)
    apply hd.congr_deriv
    ring
  · intro n t ht
    rw [show -(n+1 : ℝ)*gaussianTerm a n*Real.sin ((n+1 : ℝ)*t)=
      -((n+1 : ℝ)*gaussianTerm a n*Real.sin ((n+1 : ℝ)*t)) by ring,norm_neg,norm_mul,
      Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (show 0 ≤ gaussianTerm a n from (Real.exp_pos _).le) : 0 ≤ (n+1 : ℝ)*gaussianTerm a n)]
    exact mul_le_of_le_one_right (mul_nonneg (by positivity) (show 0 ≤ gaussianTerm a n from (Real.exp_pos _).le)) (by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one _)

lemma poleMass_fourier_hasDerivAt (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    HasDerivAt (poleMass a) (-2*Real.sqrt (Real.pi/a)/Real.pi*massSineSum a θ) θ := by
  have h := (((massCosine_hasDerivAt a θ ha).const_mul 2).const_add 1).const_mul
    (Real.sqrt (Real.pi/a)/Real.pi)
  have he : poleMass a =ᶠ[𝓝 θ] (fun t => Real.sqrt (Real.pi/a)/Real.pi*(1+2*massCosineSum a t)) := by
    filter_upwards [eventually_gt_nhds hθ,eventually_lt_nhds hπ] with t ht0 htπ
    exact poleMass_fourier a t ha ht0 htπ
  have h := h.congr_of_eventuallyEq he
  apply h.congr_deriv
  ring

lemma imaginaryValue_mass_sums (a θ : ℝ) (ha : 0 < a) :
    imaginaryValue a θ = Real.sqrt (Real.pi/a)*
      (-Real.cos θ/Real.sin θ^3-2*massSineSum a θ/Real.sin θ^2-
        2*Real.cos θ*massCosineSum a θ/Real.sin θ^3) := by
  have hD := massSine_summable a θ ha
  have hC := massCosine_summable a θ ha
  have he (n : ℕ) : imaginaryCoefficient θ n*gaussianTerm a n =
      -((n+1 : ℝ)*gaussianTerm a n*Real.sin ((n+1 : ℝ)*θ)/Real.sin θ^2)+
        (-Real.cos θ/Real.sin θ^3)*(gaussianTerm a n*Real.cos ((n+1 : ℝ)*θ)) := by
    unfold imaginaryCoefficient
    ring
  unfold imaginaryValue
  simp_rw [he]
  rw [((hD.div_const (Real.sin θ^2)).neg).tsum_add (hC.mul_left _),
    tsum_neg,tsum_div_const,tsum_mul_left]
  unfold massSineSum massCosineSum
  ring

lemma imaginaryValue_mass_derivative (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    HasDerivAt (fun t => poleMass a t/Real.sin t)
      (imaginaryValue a θ*Real.sin θ/Real.pi) θ := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne'
  have hd := (poleMass_fourier_hasDerivAt a θ ha hθ hπ).div (Real.hasDerivAt_sin θ) hs
  apply hd.congr_deriv
  rw [poleMass_fourier a θ ha hθ hπ,imaginaryValue_mass_sums a θ ha]
  change _ = Real.sqrt (Real.pi/a)*
    (-Real.cos θ/Real.sin θ^3-2*massSineSum a θ/Real.sin θ^2-
      2*Real.cos θ*massCosineSum a θ/Real.sin θ^3)*Real.sin θ/Real.pi
  unfold massCosineSum
  field_simp [hs,Real.pi_ne_zero]
  ring_nf
  simp_rw [show ∀ n : ℝ, θ+θ*n=n*θ+θ from fun n => by ring]
  ring

end ShiftedCosineTask
