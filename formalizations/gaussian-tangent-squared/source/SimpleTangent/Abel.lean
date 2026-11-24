import SimpleTangent.Series

open Filter MeasureTheory
open scoped Topology
namespace TangentShiftTask

noncomputable def abelTerm (b r : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  r^(n+1)*Real.sin (2*(n+1 : ℝ)*angle b)*Real.cos (2*(n+1 : ℝ)*x)
noncomputable def abelSum (b r x : ℝ) : ℝ := ∑' n : ℕ, abelTerm b r n x

lemma geometric_summable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => r^(n+1)) := by
  exact (summable_nat_add_iff 1).mpr
    (summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1))

lemma abelTerm_bound (b r : ℝ) (hr : 0 ≤ r) (n : ℕ) (x : ℝ) :
    ‖abelTerm b r n x‖ ≤ r^(n+1) := by
  unfold abelTerm
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr _)]
  have hs : ‖Real.sin (2*(n+1 : ℝ)*angle b)‖ ≤ 1 := Real.abs_sin_le_one _
  have hc : ‖Real.cos (2*(n+1 : ℝ)*x)‖ ≤ 1 := Real.abs_cos_le_one _
  exact (mul_le_of_le_one_right (mul_nonneg (pow_nonneg hr _) (norm_nonneg _)) hc).trans
    (mul_le_of_le_one_right (pow_nonneg hr _) hs)

lemma abelSum_continuous (b r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (abelSum b r) :=
  continuous_tsum (fun n => by unfold abelTerm; fun_prop)
    (geometric_summable r hr hr1) (abelTerm_bound b r hr)

lemma abelSum_bound (b r x : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖abelSum b r x‖ ≤ ∑' n : ℕ, r^(n+1) := by
  have hn := (geometric_summable r hr hr1).of_nonneg_of_le
    (fun n => norm_nonneg (abelTerm b r n x)) (fun n => abelTerm_bound b r hr n x)
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun n => abelTerm_bound b r hr n x) (geometric_summable r hr hr1))

lemma weighted_abelSum_integrable (α b r : ℝ) (hα : 0 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    Integrable (fun x => weight α x*abelSum b r x) :=
  (integrable_exp_neg_mul_sq hα).mul_bdd
    (abelSum_continuous b r hr hr1).aestronglyMeasurable
    (Eventually.of_forall (fun x => abelSum_bound b r x hr hr1))

lemma abel_integrable (α b r : ℝ) (hα : 0 < α) (hr : 0 < r) (hr1 : r < 1) :
    Integrable (fun x => weight α x*abelKernel b r x) := by
  have h := ((integrable_exp_neg_mul_sq hα).mul_const (-1/(1+b^2))).sub
    ((weighted_abelSum_integrable α b r hα hr.le hr1).mul_const (2/(b*(1+b^2))))
  convert h using 1
  funext x
  change weight α x*abelKernel b r x =
    weight α x*(-1/(1+b^2))-weight α x*abelSum b r x*(2/(b*(1+b^2)))
  change weight α x*(-1/(1+b^2)-2/(b*(1+b^2))*abelSum b r x) = _
  ring

lemma weighted_abelSum_integral (α b r : ℝ) (hα : 0 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ x : ℝ, weight α x*abelSum b r x) =
      Real.sqrt (Real.pi/α)*∑' n : ℕ, spectralTerm α b n*r^(n+1) := by
  let F : ℕ → ℝ → ℝ := fun n x => weight α x*abelTerm b r n x
  have hw : Integrable (weight α) := integrable_exp_neg_mul_sq hα
  have hF (n : ℕ) : Integrable (F n) := hw.mul_bdd
    (by unfold abelTerm; fun_prop)
    (Eventually.of_forall (abelTerm_bound b r hr n))
  have hbound (n : ℕ) (x : ℝ) : ‖F n x‖ ≤ weight α x*r^(n+1) := by
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (show 0 < weight α x from Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abelTerm_bound b r hr n x) (Real.exp_pos _).le
  have hsum : Summable (fun n : ℕ => ∫ x : ℝ, ‖F n x‖) := by
    apply ((geometric_summable r hr hr1).mul_left (∫ x : ℝ, weight α x)).of_nonneg_of_le
      (fun n => integral_nonneg (fun x => norm_nonneg _))
    intro n
    calc
      _ ≤ ∫ x : ℝ, weight α x*r^(n+1) :=
        integral_mono (hF n).norm (hw.mul_const _) (hbound n)
      _ = _ := integral_mul_const _ _
  have hi := integral_tsum_of_summable_integral_norm hF hsum
  unfold abelSum
  simp_rw [← tsum_mul_left]
  rw [← hi]
  apply tsum_congr
  intro n
  have heq (x : ℝ) : F n x =
      (r^(n+1)*Real.sin (2*(n+1 : ℝ)*angle b))*
        (PeriodicPoleTask.weight α x*Real.cos ((2*(n+1 : ℝ))*x)) := by
    dsimp [F, abelTerm, weight, PeriodicPoleTask.weight]
    ring
  simp_rw [heq]
  rw [integral_const_mul, PeriodicPoleTask.gaussian_cosine_integral α _ hα]
  have he : -(2*(n+1 : ℝ))^2/(4*α) = -((n+1 : ℝ)^2)/α := by ring
  rw [he]
  unfold spectralTerm
  ring

lemma abelIntegral_eq (α b r : ℝ) (hα : 0 < α) (hr : 0 < r) (hr1 : r < 1) :
    abelIntegral α b r = abelSeriesValue α b r := by
  have hw : Integrable (weight α) := integrable_exp_neg_mul_sq hα
  have hs := weighted_abelSum_integrable α b r hα hr.le hr1
  have he (x : ℝ) : weight α x*abelKernel b r x =
      weight α x*(-1/(1+b^2))-(weight α x*abelSum b r x)*(2/(b*(1+b^2))) := by
    change weight α x*(-1/(1+b^2)-2/(b*(1+b^2))*abelSum b r x) = _
    ring
  unfold abelIntegral
  simp_rw [he]
  rw [integral_sub (hw.mul_const _) (hs.mul_const _), integral_mul_const,
    integral_mul_const, weighted_abelSum_integral α b r hα hr.le hr1]
  have hg : (∫ x : ℝ, weight α x) = Real.sqrt (Real.pi/α) := integral_gaussian α
  rw [hg]
  unfold abelSeriesValue
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma abel_tendsto (α b : ℝ) (hα : 0 < α) :
    Tendsto (abelIntegral α b) (𝓝[<] (1 : ℝ)) (𝓝 (principalValue α b)) := by
  apply (abelSeries_tendsto α b hα).congr'
  have hr0 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hr0, self_mem_nhdsWithin] with r hr hr1
  exact (abelIntegral_eq α b r hα hr hr1).symm

end TangentShiftTask
