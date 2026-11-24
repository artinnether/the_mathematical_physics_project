import TuringTask.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace PeriodicPoleTask

lemma cotangent_sub_inv_tendsto :
    Tendsto (fun δ : ℝ => Real.cos δ / Real.sin δ - 1/δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  have hp : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < Real.pi/2 :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < Real.pi/2)).filter_mono nhdsWithin_le_nhds
  have hc : ContinuousAt (fun x : ℝ => Real.sinc x + Real.cos x) 0 := by fun_prop
  have hsum : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < Real.sinc x + Real.cos x := by
    have h := hc.eventually (eventually_gt_nhds (show (0 : ℝ) < Real.sinc 0 + Real.cos 0 by norm_num [Real.sinc_zero]))
    exact h.filter_mono nhdsWithin_le_nhds
  have hf (x : ℝ) : HasDerivAt (fun y : ℝ => y*Real.cos y-Real.sin y) (-x*Real.sin x) x := by
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)).sub (Real.hasDerivAt_sin x) using 1 <;> (try rfl); (try simp only [id_eq]); ring
  have hg (x : ℝ) : HasDerivAt (fun y : ℝ => y*Real.sin y) (Real.sin x+x*Real.cos x) x := by
    convert (hasDerivAt_id x).mul (Real.hasDerivAt_sin x) using 1 <;> (try rfl); (try simp only [id_eq]); ring
  have hg0 : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), Real.sin x+x*Real.cos x ≠ 0 := by
    filter_upwards [hpos,hsum] with x hx hs
    have he : Real.sin x+x*Real.cos x = x*(Real.sinc x+Real.cos x) := by
      rw [Real.sinc_of_ne_zero hx.ne']; field_simp
    rw [he]
    exact mul_ne_zero hx.ne' hs.ne'
  have hfa : Tendsto (fun x : ℝ => x*Real.cos x-Real.sin x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : ContinuousAt (fun x : ℝ => x*Real.cos x-Real.sin x) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hga : Tendsto (fun x : ℝ => x*Real.sin x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : ContinuousAt (fun x : ℝ => x*Real.sin x) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun x : ℝ => (-x*Real.sin x)/(Real.sin x+x*Real.cos x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : ContinuousAt (fun x : ℝ => (-Real.sin x)/(Real.sinc x+Real.cos x)) 0 := by
      fun_prop (disch := norm_num [Real.sinc_zero])
    have ht : Tendsto (fun x : ℝ => (-Real.sin x)/(Real.sinc x+Real.cos x))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa [Real.sinc_zero] using h.tendsto.mono_left nhdsWithin_le_nhds
    apply ht.congr'
    filter_upwards [hpos,hsum,hg0] with x hx hs hgn
    rw [Real.sinc_of_ne_zero hx.ne']
    field_simp
  have h := HasDerivAt.lhopital_zero_nhdsGT (Eventually.of_forall hf) (Eventually.of_forall hg) hg0 hfa hga hdiv
  apply h.congr'
  filter_upwards [hpos,hp] with x hx hxp
  have hsin : Real.sin x ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])).ne'
  field_simp

end PeriodicPoleTask
