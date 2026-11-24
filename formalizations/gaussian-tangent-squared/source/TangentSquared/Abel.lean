import TangentSquared.Series
import SimpleTangent.Abel
import ShiftedCosine.Abel

open Filter MeasureTheory
open scoped Topology
namespace TangentSquaredTask

noncomputable def abelTerm (b r : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  coefficient b n*r^(n+1)*Real.cos (2*(n+1 : ℝ)*x)
noncomputable def abelSum (b r x : ℝ) : ℝ := ∑' n : ℕ, abelTerm b r n x
noncomputable def abelMajorant (b r : ℝ) (n : ℕ) : ℝ :=
  (|(1+3*b^2)/b^3| + |2/b^2| * (n+1 : ℝ))*r^(n+1)

lemma abel_majorant_summable (b r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (abelMajorant b r) := by
  have h0 := TangentShiftTask.geometric_summable r hr hr1
  have h1 : Summable (fun n : ℕ => (n+1 : ℝ)*r^(n+1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := r) 1
      (by simpa [Real.norm_eq_abs,abs_of_nonneg hr] using hr1)
    have h := (summable_nat_add_iff 1).mpr h
    simpa only [pow_one,Nat.cast_add,Nat.cast_one] using h
  apply ((h0.mul_left |(1+3*b^2)/b^3|).add (h1.mul_left |2/b^2|)).congr
  intro n
  unfold abelMajorant
  ring

lemma abelTerm_bound (b r : ℝ) (hr : 0 ≤ r) (n : ℕ) (x : ℝ) :
    ‖abelTerm b r n x‖ ≤ abelMajorant b r n := by
  unfold abelTerm abelMajorant
  rw [norm_mul,norm_mul,Real.norm_eq_abs (r^(n+1)),abs_of_nonneg (pow_nonneg hr _)]
  exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (pow_nonneg hr _))
    (Real.abs_cos_le_one _)).trans (mul_le_mul_of_nonneg_right (coefficient_bound b n) (pow_nonneg hr _))

lemma abelSum_continuous (b r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : Continuous (abelSum b r) :=
  continuous_tsum (fun n => by unfold abelTerm; fun_prop)
    (abel_majorant_summable b r hr hr1) (abelTerm_bound b r hr)

lemma abelSum_bound (b r x : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖abelSum b r x‖ ≤ ∑' n : ℕ, abelMajorant b r n := by
  have hs := abel_majorant_summable b r hr hr1
  have hn := hs.of_nonneg_of_le (fun n => norm_nonneg (abelTerm b r n x))
    (fun n => abelTerm_bound b r hr n x)
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun n => abelTerm_bound b r hr n x) hs)

lemma weighted_abelSum_integrable (α b r : ℝ) (hα : 0 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    Integrable (fun x => weight α x*abelSum b r x) :=
  (integrable_exp_neg_mul_sq hα).mul_bdd (abelSum_continuous b r hr hr1).aestronglyMeasurable
    (Eventually.of_forall (fun x => abelSum_bound b r x hr hr1))

lemma abel_integrable (α b r : ℝ) (hα : 0 < α) (hr : 0 < r) (hr1 : r < 1) :
    Integrable (fun x => weight α x*abelKernel b r x) := by
  have hw : Integrable (weight α) := integrable_exp_neg_mul_sq hα
  have h := (hw.add
    (weighted_abelSum_integrable α b r hα hr.le hr1)).div_const ((1+b^2)^2)
  convert h using 1
  funext x
  change weight α x*((1+abelSum b r x)/(1+b^2)^2) =
    (weight α x+weight α x*abelSum b r x)/(1+b^2)^2
  ring

lemma weighted_abelSum_integral (α b r : ℝ) (hα : 0 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ x : ℝ, weight α x*abelSum b r x) =
      Real.sqrt (Real.pi/α)*∑' n : ℕ, spectralTerm α b n*r^(n+1) := by
  let F : ℕ → ℝ → ℝ := fun n x => weight α x*abelTerm b r n x
  have hw : Integrable (weight α) := integrable_exp_neg_mul_sq hα
  have hF (n : ℕ) : Integrable (F n) := hw.mul_bdd
    (by unfold abelTerm; fun_prop)
    (Eventually.of_forall (abelTerm_bound b r hr n))
  have hbound (n : ℕ) (x : ℝ) : ‖F n x‖ ≤ weight α x*abelMajorant b r n := by
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (show 0 < weight α x from Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abelTerm_bound b r hr n x) (Real.exp_pos _).le
  have hsum : Summable (fun n : ℕ => ∫ x : ℝ, ‖F n x‖) := by
    apply ((abel_majorant_summable b r hr hr1).mul_left (∫ x : ℝ, weight α x)).of_nonneg_of_le
      (fun n => integral_nonneg (fun x => norm_nonneg _))
    intro n
    calc
      _ ≤ ∫ x : ℝ, weight α x*abelMajorant b r n :=
        integral_mono (hF n).norm (hw.mul_const _) (hbound n)
      _ = _ := integral_mul_const _ _
  have hi := integral_tsum_of_summable_integral_norm hF hsum
  unfold abelSum
  simp_rw [← tsum_mul_left]
  rw [← hi]
  apply tsum_congr
  intro n
  have heq (x : ℝ) : F n x =
      (coefficient b n*r^(n+1))*
        (PeriodicPoleTask.weight α x*Real.cos ((2*(n+1 : ℝ))*x)) := by
    dsimp [F, abelTerm, weight, PeriodicPoleTask.weight]
    ring
  simp_rw [heq]
  rw [integral_const_mul, PeriodicPoleTask.gaussian_cosine_integral α _ hα]
  have he : -(2*(n+1 : ℝ))^2/(4*α) = -((n+1 : ℝ)^2)/α := by ring
  rw [he]
  unfold spectralTerm
  ring

lemma abelIntegral_eq (α b r : ℝ) (hα : 0 < α) (hr : 0 < r) (hr1 : r < 1) :
    abelIntegral α b r=Real.sqrt (Real.pi/α)/(1+b^2)^2*
      (1+∑' n : ℕ, spectralTerm α b n*r^(n+1)) := by
  have he (x : ℝ) : weight α x*abelKernel b r x =
      (weight α x+weight α x*abelSum b r x)/(1+b^2)^2 := by
    change weight α x*((1+abelSum b r x)/(1+b^2)^2) = _
    ring
  unfold abelIntegral
  simp_rw [he]
  have hw : Integrable (weight α) := integrable_exp_neg_mul_sq hα
  rw [integral_div,integral_add hw
    (weighted_abelSum_integrable α b r hα hr.le hr1),
    weighted_abelSum_integral α b r hα hr.le hr1]
  have hg : (∫ x : ℝ, weight α x)=Real.sqrt (Real.pi/α) := integral_gaussian α
  rw [hg]
  ring

lemma abel_tendsto (α b : ℝ) (hα : 0 < α) :
    Tendsto (abelIntegral α b) (𝓝[<] (1 : ℝ)) (𝓝 (finitePartValue α b)) := by
  have ht : Tendsto (fun r : ℝ => ∑' n : ℕ, spectralTerm α b n*r^(n+1))
      (𝓝[<] (1 : ℝ)) (𝓝 (∑' n : ℕ, spectralTerm α b n)) := by
    apply tendsto_tsum_of_dominated_convergence (spectral_majorant_summable α b hα)
    · intro n
      simpa using tendsto_const_nhds.mul
        ((show Tendsto (fun r : ℝ => r) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) from
          tendsto_id.mono_left nhdsWithin_le_nhds).pow (n+1))
    · have hr0 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
      filter_upwards [hr0,self_mem_nhdsWithin] with r hr0 hr1 n
      rw [norm_mul]
      have hp : ‖r^(n+1)‖ ≤ (1 : ℝ) := by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr0.le _)]
        exact pow_le_one₀ hr0.le hr1.le
      apply (mul_le_of_le_one_right (norm_nonneg _) hp).trans
      unfold spectralTerm
      rw [norm_mul,show ‖Real.exp (-((n+1 : ℝ)^2)/α)‖ = Real.exp (-((n+1 : ℝ)^2)/α) by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]]
      exact mul_le_mul_of_nonneg_right (coefficient_bound b n) (Real.exp_pos _).le
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add ht).const_mul (Real.sqrt (Real.pi/α)/(1+b^2)^2)
  apply h.congr'
  have hr0 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hr0,self_mem_nhdsWithin] with r hr0 hr1
  exact (abelIntegral_eq α b r hα hr0 hr1).symm

end TangentSquaredTask
