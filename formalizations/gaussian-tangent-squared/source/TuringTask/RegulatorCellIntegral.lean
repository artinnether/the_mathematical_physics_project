import TuringTask.RegulatedPeriodization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set TopologicalSpace
namespace PeriodicPoleTask

lemma cosine_harmonic_cell_integral (n : ℕ) :
    (∫ t in (-Real.pi/2)..(Real.pi/2), Real.cos ((n+1 : ℝ)*2*t)) = 0 := by
  let c : ℝ := (n+1 : ℝ)*2
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => Real.sin (c*x)/c) (Real.cos (c*t)) t := by
    convert ((Real.hasDerivAt_sin (c*t)).comp t ((hasDerivAt_id t).const_mul c)).div_const c using 1 <;>
      (try rfl) <;> (try simp only [id_eq,Pi.mul_apply]) <;> field_simp <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (by apply Continuous.intervalIntegrable; fun_prop)]
  have hr : c*(Real.pi/2) = ((n+1 : ℕ) : ℝ)*Real.pi := by dsimp [c]; push_cast; ring
  have hl : c*(-Real.pi/2) = -(((n+1 : ℕ) : ℝ)*Real.pi) := by dsimp [c]; push_cast; ring
  rw [hr,hl,Real.sin_neg,Real.sin_nat_mul_pi]
  simp

lemma cosineSeries_cell_integral (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) :
    (∫ t in (-Real.pi/2)..(Real.pi/2), cosineSeries b t) = 0 := by
  let f : ℕ → C(ℝ,ℝ) := fun n => ⟨fun t => b n*Real.cos ((n+1 : ℝ)*(2*t)),by fun_prop⟩
  have hn : Summable (fun n => ‖(f n).restrict (⟨uIcc (-Real.pi/2) (Real.pi/2),isCompact_uIcc⟩ : Compacts ℝ)‖) := by
    apply hb.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    apply (ContinuousMap.norm_le _ (hb0 n)).mpr
    intro t
    change ‖b n*Real.cos ((n+1 : ℝ)*(2*t))‖ ≤ b n
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hb0 n)]
    exact mul_le_of_le_one_right (hb0 n) (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  change (∫ t in (-Real.pi/2)..(Real.pi/2), ∑' n, f n t) = _
  rw [← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hn]
  have he (n : ℕ) : (∫ t in (-Real.pi/2)..(Real.pi/2), f n t) = 0 := by
    change (∫ t in (-Real.pi/2)..(Real.pi/2), b n*Real.cos ((n+1 : ℝ)*(2*t))) = _
    rw [intervalIntegral.integral_const_mul,show (∫ t in (-Real.pi/2)..(Real.pi/2), Real.cos ((n+1 : ℝ)*(2*t))) = 0 by simpa only [mul_assoc] using cosine_harmonic_cell_integral n,mul_zero]
  simp_rw [he]; exact tsum_zero

lemma regulatedRealKernel_cell_integral (ε : ℝ) (hε : 0 < ε) :
    (∫ t in (-Real.pi/2)..(Real.pi/2), regulatedRealKernel ε t) =
      -Real.pi*ε/regulatorScale ε^3 := by
  have hq := regulatorRatio_strict ε hε
  let q := regulatorRatio ε
  let b : ℕ → ℝ := fun n => q^(n+1)
  let c := abelCoefficient q
  have hb : Summable b := geometricShift_summable q hq.1.le hq.2
  have hc : Summable c := abelCoefficient_summable q (by change ‖regulatorRatio ε‖ < 1; simpa [Real.norm_eq_abs,abs_of_pos hq.1] using hq.2)
  have hb0 (n : ℕ) : 0 ≤ b n := pow_nonneg hq.1.le _
  have hc0 (n : ℕ) : 0 ≤ c n := by dsimp [c,abelCoefficient]; exact mul_nonneg (by positivity) (pow_nonneg hq.1.le _)
  have hB : IntervalIntegrable (cosineSeries b) volume (-Real.pi/2) (Real.pi/2) :=
    (cosineSeries_continuous b hb hb0).intervalIntegrable _ _
  have hC : IntervalIntegrable (cosineSeries c) volume (-Real.pi/2) (Real.pi/2) :=
    (cosineSeries_continuous c hc hc0).intervalIntegrable _ _
  have hp (t : ℝ) : regulatedRealKernel ε t = (-ε/regulatorScale ε^3)*(1+2*cosineSeries b t) -
      (4/regulatorScale ε^2)*cosineSeries c t := by
    rw [regulatedRealKernel_fourier ε t hε]; rfl
  simp_rw [hp]
  rw [intervalIntegral.integral_sub ((intervalIntegrable_const.add (hB.const_mul 2)).const_mul _) (hC.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_add intervalIntegrable_const (hB.const_mul 2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    cosineSeries_cell_integral b hb hb0,cosineSeries_cell_integral c hc hc0,intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

end PeriodicPoleTask
