import SimpleTangent.Basic
import Mathlib.Analysis.Normed.Group.Tannery

open Filter
open scoped Topology
namespace TangentShiftTask

lemma gaussian_sequence_summable (α : ℝ) (hα : 0 < α) :
    Summable (fun n : ℕ => Real.exp (-((n+1 : ℝ)^2)/α)) := by
  have h := PeriodicPoleTask.summable_gaussian_polynomial (1/α) (by positivity) 0
  have hs := (summable_nat_add_iff 1).mpr h
  apply hs.congr
  intro n
  simp only [Nat.cast_add, Nat.cast_one, pow_zero, one_mul]
  congr 1
  ring

lemma spectral_abs_bound (α b : ℝ) (n : ℕ) :
    ‖spectralTerm α b n‖ ≤ Real.exp (-((n+1 : ℝ)^2)/α) := by
  unfold spectralTerm
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_sin_le_one _)

lemma spectral_summable (α b : ℝ) (hα : 0 < α) :
    Summable (spectralTerm α b) := by
  exact Summable.of_norm_bounded (gaussian_sequence_summable α hα)
    (spectral_abs_bound α b)

noncomputable def abelSeriesValue (α b r : ℝ) : ℝ :=
  -Real.sqrt (Real.pi/α)/(1+b^2)*
    (1+2/b*∑' n : ℕ, spectralTerm α b n*r^(n+1))

lemma abelSeries_tendsto (α b : ℝ) (hα : 0 < α) :
    Tendsto (abelSeriesValue α b) (𝓝[<] (1 : ℝ)) (𝓝 (principalValue α b)) := by
  have ht : Tendsto (fun r : ℝ => ∑' n : ℕ, spectralTerm α b n*r^(n+1))
      (𝓝[<] (1 : ℝ)) (𝓝 (∑' n : ℕ, spectralTerm α b n)) := by
    apply tendsto_tsum_of_dominated_convergence (gaussian_sequence_summable α hα)
    · intro n
      simpa using tendsto_const_nhds.mul
        ((show Tendsto (fun r : ℝ => r) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) from
          tendsto_id.mono_left nhdsWithin_le_nhds).pow (n+1))
    · have hr0 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
      have hr1 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := self_mem_nhdsWithin
      filter_upwards [hr0, hr1] with r hr0 hr1 n
      rw [norm_mul]
      have hp : ‖r^(n+1)‖ ≤ (1 : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0.le _)]
        exact pow_le_one₀ hr0.le hr1.le
      exact (mul_le_of_le_one_right (norm_nonneg _) hp).trans (spectral_abs_bound α b n)
  exact tendsto_const_nhds.mul
    (tendsto_const_nhds.add (tendsto_const_nhds.mul ht))

end TangentShiftTask
