import TuringTask.RegulatorKernel
import TuringTask.CosineSeriesIntegral
import TuringTask.Symmetry

open MeasureTheory Filter
open scoped Topology
namespace PeriodicPoleTask

lemma feynmanIntegrand_re (α ε x : ℝ) :
    (feynmanIntegrand α ε x).re = weight α x * regulatedRealKernel ε x := by
  unfold feynmanIntegrand regulatedRealKernel
  rw [Complex.div_re, pow_two, Complex.normSq_mul]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, zero_add, add_zero, Complex.normSq_apply]
  ring

lemma geometricShift_summable (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => q^(n+1)) := by
  exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq1)

lemma gaussian_damped_summable (α : ℝ) (hα : 0 < α) (b : ℕ → ℝ)
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) :
    Summable (fun n : ℕ => b n * Real.exp (-((n+1 : ℝ)^2)/α)) := by
  apply hb.of_nonneg_of_le (fun n => mul_nonneg (hb0 n) (Real.exp_pos _).le)
  intro n
  apply mul_le_of_le_one_right (hb0 n)
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hα.le

lemma feynmanIntegral_eq_series (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    feynmanIntegral α ε = (regulatorSeriesValue α ε : ℂ) := by
  have hq := regulatorRatio_strict ε hε
  let q := regulatorRatio ε
  let b : ℕ → ℝ := fun n => q^(n+1)
  let c := abelCoefficient q
  have hb : Summable b := geometricShift_summable q hq.1.le hq.2
  have hc : Summable c := abelCoefficient_summable q (by change ‖regulatorRatio ε‖ < 1; simpa [Real.norm_eq_abs, abs_of_pos hq.1] using hq.2)
  have hb0 (n : ℕ) : 0 ≤ b n := pow_nonneg hq.1.le _
  have hc0 (n : ℕ) : 0 ≤ c n := by
    dsimp [c, abelCoefficient]
    exact mul_nonneg (by positivity) (pow_nonneg hq.1.le _)
  have hB := gaussian_cosineSeries_integrable α hα b hb hb0
  have hC := gaussian_cosineSeries_integrable α hα c hc hc0
  have hw : Integrable (weight α) := integrable_exp_neg_mul_sq hα
  have hpoint (x : ℝ) : weight α x * regulatedRealKernel ε x =
      (-ε/regulatorScale ε^3) * (weight α x + 2*(weight α x * cosineSeries b x)) -
      (4/regulatorScale ε^2) * (weight α x * cosineSeries c x) := by
    rw [regulatedRealKernel_fourier ε x hε]
    dsimp [cosineSeries, b, c, abelCoefficient, q]
    ring
  have hre : (feynmanIntegral α ε).re =
      (-ε/regulatorScale ε^3) * ((∫ x : ℝ, weight α x) +
        2*(∫ x : ℝ, weight α x * cosineSeries b x)) -
      (4/regulatorScale ε^2) * (∫ x : ℝ, weight α x * cosineSeries c x) := by
    have hir : (∫ x : ℝ, (feynmanIntegrand α ε x).re) = (feynmanIntegral α ε).re :=
      integral_re (feynman_integrable α ε hα hε)
    rw [← hir]
    simp_rw [feynmanIntegrand_re, hpoint]
    have hadd : Integrable (fun x : ℝ => weight α x + 2*(weight α x * cosineSeries b x)) :=
      hw.add (hB.const_mul 2)
    have hleft : Integrable (fun x : ℝ => (-ε/regulatorScale ε^3) *
        (weight α x + 2*(weight α x * cosineSeries b x))) := hadd.const_mul _
    rw [integral_sub hleft (hC.const_mul _), integral_const_mul,
      integral_add hw (hB.const_mul 2), integral_const_mul, integral_const_mul]
  rw [gaussian_cosineSeries_integral α hα b hb hb0,
    gaussian_cosineSeries_integral α hα c hc hc0] at hre
  have hg : (∫ x : ℝ, weight α x) = Real.sqrt (Real.pi/α) := integral_gaussian α
  rw [hg] at hre
  have hbs := gaussian_damped_summable α hα b hb hb0
  have hcs := gaussian_damped_summable α hα c hc hc0
  have hsplit : (∑' n : ℕ, regulatorTerm α ε n) =
      (2*ε/regulatorScale ε^3) * (∑' n : ℕ, b n * Real.exp (-((n+1 : ℝ)^2)/α)) +
      (4/regulatorScale ε^2) * (∑' n : ℕ, c n * Real.exp (-((n+1 : ℝ)^2)/α)) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add
      (hbs.mul_left _) (hcs.mul_left _)]
    apply tsum_congr
    intro n
    dsimp [regulatorTerm, b, c, q, abelCoefficient]
    ring
  have hvalue : (feynmanIntegral α ε).re = regulatorSeriesValue α ε := by
    rw [hre]
    unfold regulatorSeriesValue
    rw [hsplit]
    ring
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using hvalue
  · simpa only [Complex.ofReal_im] using feynmanIntegral_im_zero α ε

lemma feynmanIntegral_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (feynmanIntegral α) (𝓝[>] (0 : ℝ)) (𝓝 (finitePartValue α : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (regulatorSeries_tendsto α hα)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (feynmanIntegral_eq_series α ε hα hε).symm

end PeriodicPoleTask
