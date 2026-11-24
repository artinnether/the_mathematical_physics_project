import ShiftedCosine.Abel

open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

noncomputable def complexCosineSeries (b : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, b n*(Real.cos ((n+1 : ℝ)*x) : ℂ)

lemma complexSeries_bound (b : ℕ → ℂ) (n : ℕ) (x : ℝ) :
    ‖b n*(Real.cos ((n+1 : ℝ)*x) : ℂ)‖ ≤ ‖b n‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)

lemma complexSeries_continuous (b : ℕ → ℂ) (hb : Summable b) :
    Continuous (complexCosineSeries b) :=
  continuous_tsum (fun n => by fun_prop) hb.norm (fun n x => complexSeries_bound b n x)

lemma complexSeries_norm_bound (b : ℕ → ℂ) (hb : Summable b) (x : ℝ) :
    ‖complexCosineSeries b x‖ ≤ ∑' n, ‖b n‖ := by
  have hn := hb.norm.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => complexSeries_bound b n x)
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun n => complexSeries_bound b n x) hb.norm)

lemma gaussian_complexSeries_integrable (a : ℝ) (ha : 0 < a) (b : ℕ → ℂ) (hb : Summable b) :
    Integrable (fun x : ℝ => (weight a x : ℂ)*complexCosineSeries b x) :=
  (integrable_exp_neg_mul_sq ha).ofReal.mul_bdd
    (complexSeries_continuous b hb).aestronglyMeasurable
    (Eventually.of_forall (complexSeries_norm_bound b hb))

lemma gaussian_complexSeries_integral (a : ℝ) (ha : 0 < a) (b : ℕ → ℂ) (hb : Summable b) :
    (∫ x : ℝ, (weight a x : ℂ)*complexCosineSeries b x) =
      (Real.sqrt (Real.pi/a) : ℂ)*∑' n : ℕ, b n*(gaussianTerm a n : ℂ) := by
  let F : ℕ → ℝ → ℂ := fun n x => (weight a x : ℂ)*(b n*(Real.cos ((n+1 : ℝ)*x) : ℂ))
  have hw : Integrable (weight a) := integrable_exp_neg_mul_sq ha
  have hF (n : ℕ) : Integrable (F n) := hw.ofReal.mul_bdd (by fun_prop)
    (Eventually.of_forall (complexSeries_bound b n))
  have hbound (n : ℕ) (x : ℝ) : ‖F n x‖ ≤ weight a x*‖b n‖ := by
    dsimp only [F]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0 < weight a x from Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (complexSeries_bound b n x) (Real.exp_pos _).le
  have hsum : Summable (fun n : ℕ => ∫ x : ℝ, ‖F n x‖) := by
    apply (hb.norm.mul_left (∫ x : ℝ, weight a x)).of_nonneg_of_le
      (fun n => integral_nonneg (fun x => norm_nonneg _))
    intro n
    calc
      _ ≤ ∫ x : ℝ, weight a x*‖b n‖ :=
        integral_mono (hF n).norm (hw.mul_const _) (hbound n)
      _ = _ := integral_mul_const _ _
  have hi := integral_tsum_of_summable_integral_norm hF hsum
  unfold complexCosineSeries
  simp_rw [← tsum_mul_left]
  rw [← hi]
  apply tsum_congr
  intro n
  have heq (x : ℝ) : F n x = b n*((PeriodicPoleTask.weight a x*Real.cos ((n+1 : ℝ)*x) : ℝ) : ℂ) := by
    dsimp only [F]; unfold weight PeriodicPoleTask.weight; push_cast; ring
  simp_rw [heq]
  rw [integral_const_mul,integral_complex_ofReal,PeriodicPoleTask.gaussian_cosine_integral a _ ha]
  unfold gaussianTerm
  push_cast
  ring

end ShiftedCosineTask
