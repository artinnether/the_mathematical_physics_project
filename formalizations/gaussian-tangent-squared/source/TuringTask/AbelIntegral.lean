import TuringTask.AbelSeries
import TuringTask.GaussianFourier
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology
namespace PeriodicPoleTask

noncomputable def abelCoefficient (r : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * r ^ (n + 1)

lemma abelCoefficient_summable (r : ℝ) (hr : ‖r‖ < 1) :
    Summable (abelCoefficient r) := by
  unfold abelCoefficient
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  simpa [abelCoefficient, pow_one, Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr h

lemma abelTerm_bound (r x : ℝ) (n : ℕ) (hr : 0 ≤ r) :
    ‖abelCoefficient r n * Real.cos (2 * (n+1 : ℝ) * x)‖ ≤ abelCoefficient r n := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by unfold abelCoefficient; positivity)]
  exact mul_le_of_le_one_right (by unfold abelCoefficient; positivity)
    (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * (n+1 : ℝ) * x))

lemma abelKernel_continuous (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (abelKernel r) := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hc := continuous_tsum
    (f := fun n : ℕ => fun x : ℝ => abelCoefficient r n * Real.cos (2 * (n+1 : ℝ) * x))
    (fun n => by fun_prop) (abelCoefficient_summable r hr)
    (fun n x => abelTerm_bound r x n hr0)
  unfold abelKernel
  exact hc.const_mul (-4)

lemma abelKernel_bound (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖abelKernel r x‖ ≤ 4 * ∑' n : ℕ, abelCoefficient r n := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hn : Summable (fun n : ℕ => ‖abelCoefficient r n * Real.cos (2 * (n+1 : ℝ) * x)‖) :=
    (abelCoefficient_summable r hr).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => abelTerm_bound r x n hr0)
  have h := norm_tsum_le_tsum_norm hn
  have hb := hn.tsum_le_tsum (fun n => abelTerm_bound r x n hr0)
    (abelCoefficient_summable r hr)
  unfold abelKernel
  rw [norm_mul]
  rw [show ‖(-4 : ℝ)‖ = 4 by norm_num]
  exact mul_le_mul_of_nonneg_left (h.trans hb) (by norm_num : (0 : ℝ) ≤ 4)

lemma abel_integrable (α r : ℝ) (hα : 0 < α) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Integrable (fun x : ℝ => weight α x * abelKernel r x) := by
  exact (integrable_exp_neg_mul_sq hα).mul_bdd
    (abelKernel_continuous r hr0 hr1).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => abelKernel_bound r x hr0 hr1))

lemma abelIntegral_series (α r : ℝ) (hα : 0 < α) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    abelIntegral α r = -4 * ∑' n : ℕ, abelCoefficient r n *
      (∫ x : ℝ, weight α x * Real.cos (2 * (n+1 : ℝ) * x)) := by
  let F : ℕ → ℝ → ℝ := fun n x =>
    weight α x * (abelCoefficient r n * Real.cos (2 * (n+1 : ℝ) * x))
  have hw : Integrable (weight α) := integrable_exp_neg_mul_sq hα
  have hF (n : ℕ) : Integrable (F n) := by
    exact hw.mul_bdd (by fun_prop)
      (Filter.Eventually.of_forall (fun x => abelTerm_bound r x n hr0))
  have hbound (n : ℕ) (x : ℝ) : ‖F n x‖ ≤ weight α x * abelCoefficient r n := by
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (weight_pos α x)]
    exact mul_le_mul_of_nonneg_left (abelTerm_bound r x n hr0) (weight_pos α x).le
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hsum : Summable (fun n : ℕ => ∫ x : ℝ, ‖F n x‖) := by
    apply ((abelCoefficient_summable r hr).mul_left (∫ x : ℝ, weight α x)).of_nonneg_of_le
      (fun n => integral_nonneg (fun x => norm_nonneg _))
    intro n
    calc
      _ ≤ ∫ x : ℝ, weight α x * abelCoefficient r n :=
        integral_mono (hF n).norm (hw.mul_const _) (hbound n)
      _ = (∫ x : ℝ, weight α x) * abelCoefficient r n := integral_mul_const _ _
  have hi := integral_tsum_of_summable_integral_norm hF hsum
  have heq (x : ℝ) : weight α x * abelKernel r x = -4 * ∑' n : ℕ, F n x := by
    unfold abelKernel
    rw [mul_left_comm, ← tsum_mul_left]
    rfl
  unfold abelIntegral
  simp_rw [heq]
  rw [integral_const_mul, ← hi]
  congr 1
  apply tsum_congr
  intro n
  calc
    (∫ x : ℝ, F n x) = ∫ x : ℝ, abelCoefficient r n *
      (weight α x * Real.cos (2 * (n+1 : ℝ) * x)) := by
        congr 1; ext x; dsimp [F]; ring
    _ = _ := integral_const_mul _ _

lemma abelIntegral_eq_seriesValue (α r : ℝ) (hα : 0 < α) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    abelIntegral α r = abelSeriesValue α r := by
  rw [abelIntegral_series α r hα hr0 hr1]
  simp_rw [gaussian_cosine_integral α _ hα]
  unfold abelSeriesValue
  rw [mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : -(2 * (n+1 : ℝ))^2 / (4*α) = -((n+1 : ℝ)^2)/α := by ring
  rw [he]
  unfold abelCoefficient spectralTerm
  ring

lemma abelIntegral_tendsto (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto (abelIntegral α) (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (finitePartValue α)) := by
  apply (abelSeries_tendsto α hα).congr'
  have hr0 : ∀ᶠ r : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1), 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hr1 : ∀ᶠ r : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1), r < 1 := self_mem_nhdsWithin
  filter_upwards [hr0, hr1] with r h0 h1
  exact (abelIntegral_eq_seriesValue α r hα h0.le h1).symm

end PeriodicPoleTask
