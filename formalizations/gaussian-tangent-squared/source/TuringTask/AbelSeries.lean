import TuringTask.Series
import Mathlib.Analysis.Normed.Group.Tannery

open Filter
open scoped Topology
namespace PeriodicPoleTask

noncomputable def abelSeriesValue (α r : ℝ) : ℝ :=
  -4 * Real.sqrt (Real.pi / α) * ∑' n : ℕ, spectralTerm α n * r ^ (n+1)

lemma abelSeries_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (abelSeriesValue α) (𝓝[<] (1 : ℝ)) (𝓝 (finitePartValue α)) := by
  have ht : Tendsto (fun r : ℝ => ∑' n : ℕ, spectralTerm α n * r^(n+1))
      (𝓝[<] (1 : ℝ)) (𝓝 (∑' n : ℕ, spectralTerm α n)) := by
    apply tendsto_tsum_of_dominated_convergence (spectral_summable α hα)
    · intro n
      simpa using tendsto_const_nhds.mul
        ((show Tendsto (fun r : ℝ => r) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) from tendsto_id.mono_left nhdsWithin_le_nhds).pow (n+1))
    · have hr0 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
      have hr1 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := self_mem_nhdsWithin
      filter_upwards [hr0, hr1] with r hr0 hr1 n
      have ht0 : 0 ≤ spectralTerm α n := by unfold spectralTerm; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 (pow_nonneg hr0.le _))]
      have hp : r^(n+1) ≤ (1 : ℝ) := pow_le_one₀ hr0.le hr1.le
      simpa using mul_le_mul_of_nonneg_left hp ht0
  exact tendsto_const_nhds.mul ht

end PeriodicPoleTask
