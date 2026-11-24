import TuringTask.GaussianFourier
import TuringTask.GeometricFourier

open MeasureTheory Filter
namespace PeriodicPoleTask

noncomputable def cosineSeries (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, b n * Real.cos ((n+1 : ℝ)*(2*x))

lemma cosineSeries_bound (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (n : ℕ) (x : ℝ) :
    ‖b n * Real.cos ((n+1 : ℝ)*(2*x))‖ ≤ b n := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hb0 n)]
  exact mul_le_of_le_one_right (hb0 n)
    (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ((n+1 : ℝ)*(2*x)))

lemma cosineSeries_continuous (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) :
    Continuous (cosineSeries b) :=
  continuous_tsum (fun n => by fun_prop) hb (fun n x => cosineSeries_bound b hb0 n x)

lemma cosineSeries_norm_bound (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (x : ℝ) :
    ‖cosineSeries b x‖ ≤ ∑' n : ℕ, b n := by
  have hn : Summable (fun n => ‖b n * Real.cos ((n+1 : ℝ)*(2*x))‖) :=
    hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => cosineSeries_bound b hb0 n x)
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun n => cosineSeries_bound b hb0 n x) hb)

lemma gaussian_cosineSeries_integrable (α : ℝ) (hα : 0 < α) (b : ℕ → ℝ)
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) :
    Integrable (fun x : ℝ => weight α x * cosineSeries b x) :=
  (integrable_exp_neg_mul_sq hα).mul_bdd
    (cosineSeries_continuous b hb hb0).aestronglyMeasurable
    (Eventually.of_forall (cosineSeries_norm_bound b hb hb0))

lemma gaussian_cosineSeries_integral (α : ℝ) (hα : 0 < α) (b : ℕ → ℝ)
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) :
    (∫ x : ℝ, weight α x * cosineSeries b x) =
      Real.sqrt (Real.pi/α) * ∑' n : ℕ, b n * Real.exp (-((n+1 : ℝ)^2)/α) := by
  let F : ℕ → ℝ → ℝ := fun n x => weight α x * (b n * Real.cos ((n+1 : ℝ)*(2*x)))
  have hw : Integrable (weight α) := integrable_exp_neg_mul_sq hα
  have hF (n : ℕ) : Integrable (F n) := hw.mul_bdd (by fun_prop)
    (Eventually.of_forall (cosineSeries_bound b hb0 n))
  have hbound (n : ℕ) (x : ℝ) : ‖F n x‖ ≤ weight α x * b n := by
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (weight_pos α x)]
    exact mul_le_mul_of_nonneg_left (cosineSeries_bound b hb0 n x) (weight_pos α x).le
  have hsum : Summable (fun n : ℕ => ∫ x : ℝ, ‖F n x‖) := by
    apply (hb.mul_left (∫ x : ℝ, weight α x)).of_nonneg_of_le
      (fun n => integral_nonneg (fun x => norm_nonneg _))
    intro n
    calc
      _ ≤ ∫ x : ℝ, weight α x * b n :=
        integral_mono (hF n).norm (hw.mul_const _) (hbound n)
      _ = _ := integral_mul_const _ _
  have hi := integral_tsum_of_summable_integral_norm hF hsum
  unfold cosineSeries
  simp_rw [← tsum_mul_left]
  rw [← hi]
  apply tsum_congr
  intro n
  have heq (x : ℝ) : F n x = b n * (weight α x * Real.cos ((2*(n+1 : ℝ))*x)) := by
    dsimp only [F]; ring
  simp_rw [heq]
  rw [integral_const_mul, gaussian_cosine_integral α _ hα]
  have he : -(2*(n+1 : ℝ))^2/(4*α) = -((n+1 : ℝ)^2)/α := by ring
  rw [he]
  ring

end PeriodicPoleTask
