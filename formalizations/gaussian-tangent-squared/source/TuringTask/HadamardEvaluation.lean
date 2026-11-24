import TuringTask.HadamardLimit
import TuringTask.RegulatorCellIntegral

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology
namespace PeriodicPoleTask

lemma central_sin_ne_zero (t : ℝ) (ht : |t| ≤ Real.pi/2) (ht0 : t ≠ 0) : Real.sin t ≠ 0 := by
  have hj := Real.mul_abs_le_abs_sin ht
  have hp : 0 < 2/Real.pi*|t| := by positivity
  exact abs_pos.mp (lt_of_lt_of_le hp hj)

lemma remainder_kernel_bound (α ε t : ℝ) (ht : |t| ≤ Real.pi/2) :
    ‖(periodizedWeight α t-poleMass α)*regulatedRealKernel ε t‖ ≤ ‖hadamardRemainder α t‖ := by
  by_cases ht0 : t = 0
  · subst t; simp [periodizedWeight_at_zero,hadamardRemainder]
  have hs := central_sin_ne_zero t ht ht0
  have hs2 : 0 < Real.sin t^2 := sq_pos_of_ne_zero hs
  have hd : 0 < Real.sin t^2+ε^2 := by positivity
  have hn : |Real.sin t^2-ε^2| ≤ Real.sin t^2+ε^2 := abs_le.mpr ⟨by nlinarith [sq_nonneg (Real.sin t)],by nlinarith [sq_nonneg ε]⟩
  have hb : ‖regulatedRealKernel ε t‖ ≤ 1/Real.sin t^2 := by
    unfold regulatedRealKernel
    rw [norm_div,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (sq_pos_of_pos hd)]
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hs2).mpr
    nlinarith [sq_nonneg ε,mul_nonneg (sq_nonneg (Real.sin t)) (sq_nonneg ε),mul_le_mul_of_nonneg_right hn hs2.le]
  rw [norm_mul,hadamardRemainder,norm_div]
  simp only [Real.norm_eq_abs,abs_of_pos hs2]
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (by ring)

lemma remainder_kernel_tendsto (α t : ℝ) (ht : |t| ≤ Real.pi/2) :
    Tendsto (fun ε : ℝ => (periodizedWeight α t-poleMass α)*regulatedRealKernel ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (hadamardRemainder α t)) := by
  by_cases ht0 : t = 0
  · subst t; simpa [periodizedWeight_at_zero,hadamardRemainder] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))
  have hs := central_sin_ne_zero t ht ht0
  have hc : ContinuousAt (fun ε : ℝ => (periodizedWeight α t-poleMass α)*regulatedRealKernel ε t) 0 := by
    unfold regulatedRealKernel
    fun_prop (disch := simpa using pow_ne_zero 4 hs)
  have he : (periodizedWeight α t-poleMass α)*regulatedRealKernel 0 t = hadamardRemainder α t := by
    unfold regulatedRealKernel hadamardRemainder
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero,add_zero]
    field_simp
  rw [← he]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

lemma remainder_integral_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (fun ε : ℝ => ∫ t in (-Real.pi/2)..(Real.pi/2),
      (periodizedWeight α t-poleMass α)*regulatedRealKernel ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (hadamardIntegralValue α)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖hadamardRemainder α t‖)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hm : Measurable (fun t => (periodizedWeight α t-poleMass α)*regulatedRealKernel ε t) :=
      ((periodizedWeight_measurable α).sub_const _).mul (regulatedRealKernel_continuous ε hε).measurable
    exact hm.aestronglyMeasurable
  · apply Eventually.of_forall
    intro ε
    apply ae_of_all
    intro t ht
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at ht
    exact remainder_kernel_bound α ε t (abs_le.mpr ⟨by linarith [ht.1],ht.2⟩)
  · exact (hadamardRemainder_intervalIntegrable α hα).norm
  · apply ae_of_all
    intro t ht
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at ht
    exact remainder_kernel_tendsto α t (abs_le.mpr ⟨by linarith [ht.1],ht.2⟩)

lemma feynmanIntegral_re_tendsto_hadamard (α : ℝ) (hα : 0 < α) :
    Tendsto (fun ε => (feynmanIntegral α ε).re) (𝓝[>] (0 : ℝ)) (𝓝 (hadamardIntegralValue α)) := by
  have hc : ContinuousAt (fun ε : ℝ => poleMass α*(-Real.pi*ε/regulatorScale ε^3)) 0 := by
    unfold regulatorScale
    fun_prop (disch := norm_num)
  have hct : Tendsto (fun ε : ℝ => poleMass α*(-Real.pi*ε/regulatorScale ε^3))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := hct.add (remainder_integral_tendsto α hα)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [feynmanIntegral_re_periodized α ε hα hε]
  have hW : IntervalIntegrable (fun t => (periodizedWeight α t-poleMass α)*regulatedRealKernel ε t)
      volume (-Real.pi/2) (Real.pi/2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith [Real.pi_pos])]
    exact ((periodizedWeight_continuousOn α hα).sub continuousOn_const).mul (regulatedRealKernel_continuous ε hε).continuousOn
  have hK : IntervalIntegrable (fun t => poleMass α*regulatedRealKernel ε t) volume (-Real.pi/2) (Real.pi/2) :=
    ((regulatedRealKernel_continuous ε hε).intervalIntegrable _ _).const_mul _
  have hp (t : ℝ) : periodizedWeight α t*regulatedRealKernel ε t =
      poleMass α*regulatedRealKernel ε t+(periodizedWeight α t-poleMass α)*regulatedRealKernel ε t := by ring
  simp_rw [hp]
  rw [intervalIntegral.integral_add hK hW,intervalIntegral.integral_const_mul,regulatedRealKernel_cell_integral ε hε]

lemma hadamardIntegralValue_eq (α : ℝ) (hα : 0 < α) : hadamardIntegralValue α = finitePartValue α := by
  have hf : Tendsto (fun ε => (feynmanIntegral α ε).re) (𝓝[>] (0 : ℝ)) (𝓝 (finitePartValue α)) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp (feynmanIntegral_tendsto α hα) using 1 <;> rfl
  exact tendsto_nhds_unique (feynmanIntegral_re_tendsto_hadamard α hα) hf

end PeriodicPoleTask
