import SimpleTangent.FeynmanSeries
import SimpleTangent.Series

open Filter MeasureTheory
open scoped Topology
namespace TangentShiftTask

noncomputable def boundaryRatio (b : ℝ) : ℂ :=
  (1-Complex.I*(b : ℂ))/(1+Complex.I*(b : ℂ))

noncomputable def feynmanBoundaryValue (α b : ℝ) : ℂ :=
  (Real.sqrt (Real.pi/α) : ℂ)*
    (1/((Complex.I*(b : ℂ))*(1+Complex.I*(b : ℂ)))+
      2/((Complex.I*(b : ℂ))*(1-(Complex.I*(b : ℂ))^2))*
        ∑' n : ℕ, boundaryRatio b^(n+1)*(Real.exp (-((n+1 : ℝ)^2)/α) : ℂ))

lemma regulated_gaussian_series_tendsto (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Tendsto (fun ε => ∑' n : ℕ, regulatorRatio b ε^(n+1)*
      (Real.exp (-((n+1 : ℝ)^2)/α) : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑' n : ℕ, boundaryRatio b^(n+1)*(Real.exp (-((n+1 : ℝ)^2)/α) : ℂ))) := by
  apply tendsto_tsum_of_dominated_convergence (gaussian_sequence_summable α hα)
  · intro n
    exact ((ratio_tendsto b hb).pow (n+1)).mul tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      (pow_le_one₀ (norm_nonneg _) (ratio_norm_lt_one b ε hε).le)

lemma feynman_tendsto_boundary (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Tendsto (feynmanIntegral α b) (𝓝[>] (0 : ℝ)) (𝓝 (feynmanBoundaryValue α b)) := by
  have hs := root_tendsto b hb
  have hz : Complex.I*(b : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne')
  have hp : 1+Complex.I*(b : ℂ) ≠ 0 := by
    rw [← root_at_zero b hb]
    exact one_add_root_ne b 0
  have hm : 1-(Complex.I*(b : ℂ))^2 ≠ 0 := by
    have he : 1-(Complex.I*(b : ℂ))^2=((1+b^2 : ℝ) : ℂ) := by
      rw [mul_pow,Complex.I_sq]
      push_cast
      ring
    rw [he]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have h : Tendsto (feynmanSeriesValue α b) (𝓝[>] (0 : ℝ)) (𝓝 (feynmanBoundaryValue α b)) :=
    tendsto_const_nhds.mul
      ((tendsto_const_nhds.div (hs.mul (tendsto_const_nhds.add hs)) (mul_ne_zero hz hp)).add
        ((tendsto_const_nhds.div (hs.mul (tendsto_const_nhds.sub (hs.pow 2)))
          (mul_ne_zero hz hm)).mul (regulated_gaussian_series_tendsto α b hα hb)))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (feynmanIntegral_eq α b ε hα hε).symm

end TangentShiftTask
