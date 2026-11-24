import TangentSquared.FeynmanKernel
import TangentSquared.Series
import SimpleTangent.FeynmanLimit

set_option maxHeartbeats 2000000
open Filter MeasureTheory
open scoped Topology
namespace TangentSquaredTask

noncomputable def regulatedSeriesValue (α b ε : ℝ) : ℂ :=
  (Real.sqrt (Real.pi/α) : ℂ)*
    (regulatorA (TangentShiftTask.regulatorRoot b ε) +
      regulatorB (TangentShiftTask.regulatorRoot b ε)*
        ∑' n : ℕ,TangentShiftTask.regulatorRatio b ε^(n+1)*(Real.exp (-((n+1 : ℝ)^2)/α) : ℂ) +
      regulatorC (TangentShiftTask.regulatorRoot b ε)*
        ∑' n : ℕ,(n+1 : ℂ)*TangentShiftTask.regulatorRatio b ε^(n+1)*(Real.exp (-((n+1 : ℝ)^2)/α) : ℂ))

lemma feynmanIntegral_eq_series (α b ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    feynmanIntegral α b ε=regulatedSeriesValue α b ε := by
  let q := TangentShiftTask.regulatorRatio b ε
  have hq : ‖q‖ < 1 := TangentShiftTask.ratio_norm_lt_one b ε hε
  have h0 := ShiftedCosineTask.complex_geometric_summable q hq
  have h1 := ShiftedCosineTask.complex_weighted_geometric_summable q hq
  have hw : Integrable (fun x : ℝ => (weight α x : ℂ)) := (integrable_exp_neg_mul_sq hα).ofReal
  have hi0 : Integrable (fun x : ℝ => (weight α x : ℂ)*
      TangentShiftTask.complexCosineSeries (fun n => q^(n+1)) x) :=
    TangentShiftTask.gaussian_complexSeries_integrable α hα _ h0
  have hi1 : Integrable (fun x : ℝ => (weight α x : ℂ)*
      TangentShiftTask.complexCosineSeries (fun n => (n+1 : ℂ)*q^(n+1)) x) :=
    TangentShiftTask.gaussian_complexSeries_integrable α hα _ h1
  have he (x : ℝ) : feynmanIntegrand α b ε x=
      (weight α x : ℂ)*regulatorA (TangentShiftTask.regulatorRoot b ε) +
      ((weight α x : ℂ)*TangentShiftTask.complexCosineSeries (fun n => q^(n+1)) x)*
        regulatorB (TangentShiftTask.regulatorRoot b ε) +
      ((weight α x : ℂ)*TangentShiftTask.complexCosineSeries (fun n => (n+1 : ℂ)*q^(n+1)) x)*
        regulatorC (TangentShiftTask.regulatorRoot b ε) := by
    unfold feynmanIntegrand
    rw [mul_div_assoc,kernel_fourier b ε x hε]
    ring
  unfold feynmanIntegral
  simp_rw [he]
  have hsplit := integral_add
    ((hw.mul_const (regulatorA (TangentShiftTask.regulatorRoot b ε))).add
      (hi0.mul_const (regulatorB (TangentShiftTask.regulatorRoot b ε))))
    (hi1.mul_const (regulatorC (TangentShiftTask.regulatorRoot b ε)))
  simp only [Pi.add_apply] at hsplit
  rw [hsplit]
  have hsplit0 := integral_add (hw.mul_const (regulatorA (TangentShiftTask.regulatorRoot b ε)))
    (hi0.mul_const (regulatorB (TangentShiftTask.regulatorRoot b ε)))
  rw [hsplit0,integral_mul_const,integral_mul_const,integral_mul_const]
  have hg : (∫ x : ℝ,(weight α x : ℂ))=(Real.sqrt (Real.pi/α) : ℂ) := by
    rw [integral_complex_ofReal]
    congr 1
    exact integral_gaussian α
  rw [hg]
  have hg0 := TangentShiftTask.gaussian_complexSeries_integral α hα _ h0
  have hg1 := TangentShiftTask.gaussian_complexSeries_integral α hα _ h1
  change (∫ x : ℝ,(weight α x : ℂ)*TangentShiftTask.complexCosineSeries (fun n => q^(n+1)) x)=_ at hg0
  change (∫ x : ℝ,(weight α x : ℂ)*TangentShiftTask.complexCosineSeries (fun n => (n+1 : ℂ)*q^(n+1)) x)=_ at hg1
  rw [hg0,hg1]
  unfold regulatedSeriesValue
  dsimp only [q]
  ring

noncomputable def complexBoundaryValue (α b : ℝ) : ℂ :=
  (Real.sqrt (Real.pi/α) : ℂ)*
    (regulatorA (Complex.I*(b : ℂ)) + regulatorB (Complex.I*(b : ℂ))*
      (∑' n : ℕ,TangentShiftTask.boundaryRatio b^(n+1)*(Real.exp (-((n+1 : ℝ)^2)/α) : ℂ)) +
      regulatorC (Complex.I*(b : ℂ))*
      (∑' n : ℕ,(n+1 : ℂ)*TangentShiftTask.boundaryRatio b^(n+1)*(Real.exp (-((n+1 : ℝ)^2)/α) : ℂ)))

lemma weighted_gaussian_summable (α : ℝ) (hα : 0 < α) :
    Summable (fun n : ℕ => (n+1 : ℝ)*Real.exp (-((n+1 : ℝ)^2)/α)) :=
  PeriodicPoleTask.spectral_summable α hα

lemma regulated_weighted_series_tendsto (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Tendsto (fun ε : ℝ => ∑' n : ℕ,(n+1 : ℂ)*TangentShiftTask.regulatorRatio b ε^(n+1)*
      (Real.exp (-((n+1 : ℝ)^2)/α) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (∑' n : ℕ,(n+1 : ℂ)*TangentShiftTask.boundaryRatio b^(n+1)*
        (Real.exp (-((n+1 : ℝ)^2)/α) : ℂ))) := by
  apply tendsto_tsum_of_dominated_convergence (weighted_gaussian_summable α hα)
  · intro n
    exact ((TangentShiftTask.ratio_tendsto b hb).pow (n+1)).const_mul _ |>.mul_const _
  · filter_upwards [self_mem_nhdsWithin] with ε hε n
    have hq := (TangentShiftTask.ratio_norm_lt_one b ε hε).le
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have hn : ‖(n+1 : ℂ)‖=(n+1 : ℝ) := by norm_cast
    rw [hn]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show ‖TangentShiftTask.regulatorRatio b ε‖^(n+1) ≤ 1 from
        pow_le_one₀ (norm_nonneg _) hq) (by positivity)) (Real.exp_pos _).le).trans_eq (by ring)

lemma feynman_tendsto_boundary (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Tendsto (feynmanIntegral α b) (𝓝[>] (0 : ℝ)) (𝓝 (complexBoundaryValue α b)) := by
  have hs := TangentShiftTask.root_tendsto b hb
  have hz : Complex.I*(b : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne')
  have hp : 1+Complex.I*(b : ℂ) ≠ 0 := by
    rw [← TangentShiftTask.root_at_zero b hb]
    exact TangentShiftTask.one_add_root_ne b 0
  have hm : 1-(Complex.I*(b : ℂ))^2 ≠ 0 := by
    have he : 1-(Complex.I*(b : ℂ))^2=((1+b^2 : ℝ) : ℂ) := by
      rw [mul_pow,Complex.I_sq]
      push_cast
      ring
    rw [he]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hA : ContinuousAt regulatorA (Complex.I*(b : ℂ)) := by
    unfold regulatorA
    fun_prop (disch := aesop)
  have hB : ContinuousAt regulatorB (Complex.I*(b : ℂ)) := by
    unfold regulatorB
    fun_prop (disch := aesop)
  have hC : ContinuousAt regulatorC (Complex.I*(b : ℂ)) := by
    unfold regulatorC
    fun_prop (disch := aesop)
  have h0 := TangentShiftTask.regulated_gaussian_series_tendsto α b hα hb
  have h1 := regulated_weighted_series_tendsto α b hα hb
  have h := (((hA.tendsto.comp hs).add ((hB.tendsto.comp hs).mul h0)).add
    ((hC.tendsto.comp hs).mul h1)).const_mul (Real.sqrt (Real.pi/α) : ℂ)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (feynmanIntegral_eq_series α b ε hα hε).symm

end TangentSquaredTask
