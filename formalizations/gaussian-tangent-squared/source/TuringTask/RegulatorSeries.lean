import TuringTask.Series
import Mathlib.Analysis.Normed.Group.Tannery

open Filter
open scoped Topology
namespace PeriodicPoleTask

noncomputable def regulatorScale (ε : ℝ) : ℝ := Real.sqrt (1 + ε^2)
noncomputable def regulatorRatio (ε : ℝ) : ℝ := (regulatorScale ε - ε)^2
noncomputable def regulatorTerm (α ε : ℝ) (n : ℕ) : ℝ :=
  (2*ε / regulatorScale ε ^ 3 + 4*(n+1 : ℝ) / regulatorScale ε ^ 2) *
    regulatorRatio ε ^ (n+1) * Real.exp (-((n+1 : ℝ)^2)/α)
noncomputable def regulatorSeriesValue (α ε : ℝ) : ℝ :=
  -Real.sqrt (Real.pi/α) *
    (ε / regulatorScale ε ^ 3 + ∑' n : ℕ, regulatorTerm α ε n)

lemma regulatorScale_sq (ε : ℝ) : regulatorScale ε ^ 2 = 1+ε^2 := by
  exact Real.sq_sqrt (by positivity)

lemma regulatorScale_ge_one (ε : ℝ) : 1 ≤ regulatorScale ε := by
  have h := regulatorScale_sq ε
  have hn : 0 ≤ regulatorScale ε := Real.sqrt_nonneg _
  nlinarith [sq_nonneg ε]

lemma regulatorRatio_bounds (ε : ℝ) (hε : 0 ≤ ε) :
    0 ≤ regulatorRatio ε ∧ regulatorRatio ε ≤ 1 := by
  have hs := regulatorScale_sq ε
  have hn : 0 ≤ regulatorScale ε := Real.sqrt_nonneg _
  have hlo : 0 ≤ regulatorScale ε - ε := by nlinarith
  have hhi : regulatorScale ε - ε ≤ 1 := by nlinarith
  unfold regulatorRatio
  exact ⟨sq_nonneg _, by nlinarith⟩

lemma regulatorTerm_bound (α ε : ℝ) (n : ℕ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖regulatorTerm α ε n‖ ≤
      (2+4*(n+1 : ℝ))*Real.exp (-((n+1 : ℝ)^2)/α) := by
  have hs := regulatorScale_ge_one ε
  have hs2 : 1 ≤ regulatorScale ε ^ 2 := by nlinarith
  have hs3 : 1 ≤ regulatorScale ε ^ 3 := by nlinarith [sq_nonneg (regulatorScale ε - 1)]
  have hr := regulatorRatio_bounds ε hε
  have hp : regulatorRatio ε ^ (n+1) ≤ 1 := pow_le_one₀ hr.1 hr.2
  have hpow : 0 ≤ regulatorRatio ε ^ (n+1) := pow_nonneg hr.1 _
  have ht : 0 ≤ regulatorTerm α ε n := by unfold regulatorTerm; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg ht]
  have ha : 2*ε / regulatorScale ε ^ 3 ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < regulatorScale ε ^ 3)).mpr
    nlinarith
  have hb : 4*(n+1 : ℝ) / regulatorScale ε ^ 2 ≤ 4*(n+1 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < regulatorScale ε ^ 2)).mpr
    have hm := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ 4*(n+1 : ℝ) by positivity)
    nlinarith
  unfold regulatorTerm
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    _ ≤ (2*ε / regulatorScale ε ^ 3 + 4*(n+1 : ℝ) / regulatorScale ε ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 2+4*(n+1 : ℝ) := by nlinarith

lemma regulatorTerm_tendsto (α : ℝ) (n : ℕ) :
    Tendsto (fun ε : ℝ => regulatorTerm α ε n) (𝓝[>] (0 : ℝ))
      (𝓝 (4 * spectralTerm α n)) := by
  have hc : ContinuousAt (fun ε : ℝ => regulatorTerm α ε n) 0 := by
    unfold regulatorTerm regulatorRatio regulatorScale
    fun_prop (disch := norm_num)
  have ht : Tendsto (fun ε : ℝ => regulatorTerm α ε n) (𝓝[>] (0 : ℝ))
      (𝓝 (regulatorTerm α 0 n)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  convert ht using 1 <;> simp [regulatorTerm, regulatorRatio, regulatorScale, spectralTerm] <;> ring

lemma gaussianShift_summable (α : ℝ) (hα : 0 < α) :
    Summable (fun n : ℕ => Real.exp (-((n+1 : ℝ)^2)/α)) := by
  have h := summable_gaussian_polynomial (1 / α) (by positivity) 0
  have hs := (summable_nat_add_iff 1).mpr h
  apply hs.congr
  intro n
  simp only [Nat.cast_add, Nat.cast_one, pow_zero, one_mul]
  congr 1
  ring

lemma regulatorMajorant_summable (α : ℝ) (hα : 0 < α) :
    Summable (fun n : ℕ => (2+4*(n+1 : ℝ))*Real.exp (-((n+1 : ℝ)^2)/α)) := by
  have h := ((gaussianShift_summable α hα).mul_left 2).add
    ((spectral_summable α hα).mul_left 4)
  apply h.congr
  intro n
  unfold spectralTerm
  ring

lemma regulatorSeries_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (regulatorSeriesValue α) (𝓝[>] (0 : ℝ)) (𝓝 (finitePartValue α)) := by
  have ht : Tendsto (fun ε : ℝ => ∑' n : ℕ, regulatorTerm α ε n)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑' n : ℕ, 4 * spectralTerm α n)) := by
    apply tendsto_tsum_of_dominated_convergence (regulatorMajorant_summable α hα)
      (regulatorTerm_tendsto α)
    have hε0 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    have hε1 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hε0, hε1] with ε h0 h1 n
    exact regulatorTerm_bound α ε n h0.le h1.le
  have hc : ContinuousAt (fun ε : ℝ => ε / regulatorScale ε ^ 3) 0 := by
    unfold regulatorScale
    fun_prop (disch := norm_num)
  have hz : Tendsto (fun ε : ℝ => ε / regulatorScale ε ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [regulatorScale] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := (hz.add ht).const_mul (-Real.sqrt (Real.pi/α))
  have heq : (-Real.sqrt (Real.pi / α)) * (0 + ∑' n : ℕ, 4 * spectralTerm α n) = finitePartValue α := by
    rw [tsum_mul_left]
    unfold finitePartValue
    ring
  rw [heq] at h
  exact h

end PeriodicPoleTask
