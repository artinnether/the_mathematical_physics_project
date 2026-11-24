import ShiftedCosine.Series

open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def signedCosineSeries (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, b n*Real.cos ((n+1 : ℝ)*x)

lemma signedSeries_bound (b : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    ‖b n*Real.cos ((n+1 : ℝ)*x)‖ ≤ ‖b n‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ((n+1 : ℝ)*x))

lemma signedSeries_continuous (b : ℕ → ℝ) (hb : Summable b) :
    Continuous (signedCosineSeries b) :=
  continuous_tsum (fun n => by fun_prop) hb.norm (fun n x => signedSeries_bound b n x)

lemma signedSeries_norm_bound (b : ℕ → ℝ) (hb : Summable b) (x : ℝ) :
    ‖signedCosineSeries b x‖ ≤ ∑' n, ‖b n‖ := by
  have hn := hb.norm.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => signedSeries_bound b n x)
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun n => signedSeries_bound b n x) hb.norm)

lemma gaussian_signedSeries_integrable (a : ℝ) (ha : 0 < a) (b : ℕ → ℝ) (hb : Summable b) :
    Integrable (fun x : ℝ => weight a x*signedCosineSeries b x) :=
  (integrable_exp_neg_mul_sq ha).mul_bdd
    (signedSeries_continuous b hb).aestronglyMeasurable
    (Eventually.of_forall (signedSeries_norm_bound b hb))

lemma gaussian_signedSeries_integral (a : ℝ) (ha : 0 < a) (b : ℕ → ℝ) (hb : Summable b) :
    (∫ x : ℝ, weight a x*signedCosineSeries b x) =
      Real.sqrt (Real.pi/a)*∑' n : ℕ, b n*gaussianTerm a n := by
  let F : ℕ → ℝ → ℝ := fun n x => weight a x*(b n*Real.cos ((n+1 : ℝ)*x))
  have hw : Integrable (weight a) := integrable_exp_neg_mul_sq ha
  have hF (n : ℕ) : Integrable (F n) := hw.mul_bdd (by fun_prop)
    (Eventually.of_forall (signedSeries_bound b n))
  have hbound (n : ℕ) (x : ℝ) : ‖F n x‖ ≤ weight a x*‖b n‖ := by
    dsimp only [F]
    rw [norm_mul, show ‖weight a x‖=weight a x from
      by rw [Real.norm_eq_abs,abs_of_pos (show 0 < weight a x from Real.exp_pos _)]]
    exact mul_le_mul_of_nonneg_left (signedSeries_bound b n x) (Real.exp_pos _).le
  have hsum : Summable (fun n : ℕ => ∫ x : ℝ, ‖F n x‖) := by
    apply (hb.norm.mul_left (∫ x : ℝ, weight a x)).of_nonneg_of_le
      (fun n => integral_nonneg (fun x => norm_nonneg _))
    intro n
    calc
      _ ≤ ∫ x : ℝ, weight a x*‖b n‖ :=
        integral_mono (hF n).norm (hw.mul_const _) (hbound n)
      _ = _ := integral_mul_const _ _
  have hi := integral_tsum_of_summable_integral_norm hF hsum
  unfold signedCosineSeries
  simp_rw [← tsum_mul_left]
  rw [← hi]
  apply tsum_congr
  intro n
  have heq (x : ℝ) : F n x = b n*(PeriodicPoleTask.weight a x*Real.cos ((n+1 : ℝ)*x)) := by
    dsimp only [F]; unfold weight PeriodicPoleTask.weight; ring
  simp_rw [heq]
  rw [integral_const_mul,PeriodicPoleTask.gaussian_cosine_integral a _ ha]
  unfold gaussianTerm
  ring

lemma weighted_geometric_summable (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n+1 : ℝ)*r^(n+1)) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := r) 1
    (by simpa [Real.norm_eq_abs,abs_of_pos hr] using hr1)
  have h := (summable_nat_add_iff 1).mpr h
  simpa only [pow_one,Nat.cast_add,Nat.cast_one] using h

lemma coefficient_geometric_summable (θ r : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hr : 0 < r) (hr1 : r < 1) : Summable (fun n : ℕ => realCoefficient θ n*r^(n+1)) := by
  have hg := (summable_geometric_of_abs_lt_one (by rw [abs_of_pos hr]; exact hr1))
  have hg := (summable_nat_add_iff 1).mpr hg
  have hm := ((weighted_geometric_summable r hr hr1).div_const (Real.sin θ^2)).add
    (hg.mul_left (1/Real.sin θ^3))
  have hm : Summable (fun n : ℕ => ((n+1 : ℝ)/Real.sin θ^2+1/Real.sin θ^3)*r^(n+1)) := by
    apply hm.congr
    intro n; ring
  apply Summable.of_norm_bounded hm
  intro n
  rw [norm_mul,show ‖r^(n+1)‖=r^(n+1) from
    by rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr.le _)]]
  exact mul_le_mul_of_nonneg_right (coefficient_bound θ hθ hπ n).1 (pow_nonneg hr.le _)

lemma abel_integrable (a θ r : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hr : 0 < r) (hr1 : r < 1) : Integrable (fun x => weight a x*abelKernel θ r x) := by
  have h := (gaussian_signedSeries_integrable a ha (fun n => realCoefficient θ n*r^(n+1))
    (coefficient_geometric_summable θ r hθ hπ hr hr1)).const_mul 2
  convert h using 1
  ext x
  unfold abelKernel signedCosineSeries
  ring

lemma abelIntegral_eq (a θ r : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hr : 0 < r) (hr1 : r < 1) :
    abelIntegral a θ r = 2*Real.sqrt (Real.pi/a)*
      ∑' n : ℕ, realCoefficient θ n*gaussianTerm a n*r^(n+1) := by
  unfold abelIntegral abelKernel
  have he (x : ℝ) : weight a x*(2*∑' n : ℕ, realCoefficient θ n*r^(n+1)*Real.cos ((n+1 : ℝ)*x)) =
    2*(weight a x*signedCosineSeries (fun n => realCoefficient θ n*r^(n+1)) x) := by
    unfold signedCosineSeries; ring
  simp_rw [he]
  rw [integral_const_mul,gaussian_signedSeries_integral a ha _
    (coefficient_geometric_summable θ r hθ hπ hr hr1)]
  have ht : (∑' n : ℕ, realCoefficient θ n*r^(n+1)*gaussianTerm a n) =
      ∑' n : ℕ, realCoefficient θ n*gaussianTerm a n*r^(n+1) := by
    apply tsum_congr; intro n; ring
  rw [ht]
  ring

lemma abelIntegral_tendsto (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (abelIntegral a θ) (𝓝[<] (1 : ℝ)) (𝓝 (finitePartValue a θ)) := by
  have ht : Tendsto (fun r : ℝ => ∑' n : ℕ, realCoefficient θ n*gaussianTerm a n*r^(n+1))
      (𝓝[<] (1 : ℝ)) (𝓝 (∑' n : ℕ, realCoefficient θ n*gaussianTerm a n)) := by
    apply tendsto_tsum_of_dominated_convergence (spectral_majorant_summable a θ ha)
    · intro n
      simpa using tendsto_const_nhds.mul
        ((show Tendsto (fun r : ℝ => r) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) from
          tendsto_id.mono_left nhdsWithin_le_nhds).pow (n+1))
    · have hr0 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
      filter_upwards [hr0,self_mem_nhdsWithin] with r hr hr1 n
      rw [norm_mul, show ‖r^(n+1)‖=r^(n+1) from
        by rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr.le _)]]
      have hb : ‖realCoefficient θ n*gaussianTerm a n‖ ≤
          ((n+1 : ℝ)/Real.sin θ^2+1/Real.sin θ^3)*gaussianTerm a n := by
        rw [norm_mul,show ‖gaussianTerm a n‖=gaussianTerm a n from
          by rw [Real.norm_eq_abs,abs_of_pos (show 0 < gaussianTerm a n from Real.exp_pos _)]]
        exact mul_le_mul_of_nonneg_right (coefficient_bound θ hθ hπ n).1 (Real.exp_pos _).le
      exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hr.le hr1.le)).trans hb
  have h := (tendsto_const_nhds (x := 2*Real.sqrt (Real.pi/a))).mul ht
  change Tendsto (fun r : ℝ => 2*Real.sqrt (Real.pi/a)*
    ∑' n : ℕ, realCoefficient θ n*gaussianTerm a n*r^(n+1)) _ (𝓝 (finitePartValue a θ)) at h
  apply h.congr'
  have hr0 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hr0,self_mem_nhdsWithin] with r hr hr1
  exact (abelIntegral_eq a θ r ha hθ hπ hr hr1).symm

end ShiftedCosineTask
