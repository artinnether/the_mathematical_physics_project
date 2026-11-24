import TuringTask.Periodization
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option maxHeartbeats 800000
open Set MeasureTheory TopologicalSpace
namespace PeriodicPoleTask

lemma sin_sq_shift (t : ℝ) (k : ℤ) :
    Real.sin (t+(k : ℝ)*Real.pi)^2 = Real.sin t^2 := by
  rw [← sq_abs,abs_sin_shift,sq_abs]

lemma cellTruncation_shift (α δ : ℝ) (k : ℤ) :
    cellTruncation α δ k =
      (∫ t in (-Real.pi/2)..(-δ), weight α (t+(k : ℝ)*Real.pi)/Real.sin t^2) +
      (∫ t in δ..(Real.pi/2), weight α (t+(k : ℝ)*Real.pi)/Real.sin t^2) := by
  have hp (t : ℝ) : poleIntegrand α (t+(k : ℝ)*Real.pi) = weight α (t+(k : ℝ)*Real.pi)/Real.sin t^2 := by
    unfold poleIntegrand; rw [sin_sq_shift]
  have hl := intervalIntegral.integral_comp_add_right (a := -Real.pi/2) (b := -δ)
    (poleIntegrand α) ((k : ℝ)*Real.pi)
  have hr := intervalIntegral.integral_comp_add_right (a := δ) (b := Real.pi/2)
    (poleIntegrand α) ((k : ℝ)*Real.pi)
  simp_rw [hp] at hl hr
  unfold cellTruncation
  rw [hl,hr]
  congr 2 <;> ring

noncomputable def clippedCell (α δ : ℝ) (k : ℤ) (t : ℝ) : ℝ :=
  weight α (t+(k : ℝ)*Real.pi) / max (Real.sin t^2) (Real.sin δ^2)

lemma clippedCell_continuous (α δ : ℝ) (k : ℤ) (hδ : 0 < δ) (hδp : δ < Real.pi/2) :
    Continuous (clippedCell α δ k) := by
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  unfold clippedCell weight
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact ne_of_gt (lt_of_lt_of_le (sq_pos_of_pos hsδ) (le_max_right _ _))

lemma clippedCell_bound (α δ t : ℝ) (k : ℤ) (hα : 0 < α)
    (hδ : 0 < δ) (hδp : δ < Real.pi/2) (ht : |t| ≤ Real.pi/2) :
    ‖clippedCell α δ k t‖ ≤ latticeMajorant α k / Real.sin δ^2 := by
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hd : 0 < max (Real.sin t^2) (Real.sin δ^2) := lt_of_lt_of_le (sq_pos_of_pos hsδ) (le_max_right _ _)
  unfold clippedCell
  rw [norm_div,Real.norm_eq_abs,abs_of_pos (weight_pos _ _),Real.norm_eq_abs,abs_of_pos hd]
  exact div_le_div₀ (by unfold latticeMajorant weight; positivity)
    (shifted_weight_bound α t k hα ht) (sq_pos_of_pos hsδ) (le_max_right _ _)

lemma clippedCell_eq (α δ t : ℝ) (k : ℤ) (hδ : 0 < δ) (hδp : δ < Real.pi/2)
    (ht : |t| ≤ Real.pi/2) (hcut : δ ≤ |t|) :
    clippedCell α δ k t = weight α (t+(k : ℝ)*Real.pi)/Real.sin t^2 := by
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hs := cut_sin_bound δ t hδ hδp ht hcut
  have hss : Real.sin δ^2 ≤ Real.sin t^2 := by nlinarith [abs_nonneg (Real.sin t),sq_abs (Real.sin t)]
  unfold clippedCell
  rw [max_eq_left hss]

lemma periodized_cut_integral (α δ a b : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hδp : δ < Real.pi/2)
    (hab : a ≤ b) (hcut : ∀ t ∈ Icc a b, |t| ≤ Real.pi/2 ∧ δ ≤ |t|) :
    (∑' k : ℤ, ∫ t in a..b, weight α (t+(k : ℝ)*Real.pi)/Real.sin t^2) =
      ∫ t in a..b, periodizedWeight α t / Real.sin t^2 := by
  let f : ℤ → C(ℝ, ℝ) := fun k => ⟨clippedCell α δ k,clippedCell_continuous α δ k hδ hδp⟩
  have hM : Summable (fun k : ℤ => latticeMajorant α k / Real.sin δ^2) :=
    (latticeMajorant_summable α hα).div_const _
  have hn : Summable (fun k : ℤ => ‖(f k).restrict (⟨uIcc a b,isCompact_uIcc⟩ : Compacts ℝ)‖) := by
    apply hM.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    apply (ContinuousMap.norm_le _ (by unfold latticeMajorant weight; positivity)).mpr
    intro t
    have ht : (t : ℝ) ∈ uIcc a b := t.property
    have ht' : (t : ℝ) ∈ Icc a b := Eq.mp (congrArg (fun s : Set ℝ => (t : ℝ) ∈ s) (uIcc_of_le hab)) ht
    exact clippedCell_bound α δ t k hα hδ hδp (hcut t ht').1
  have h := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hn
  calc
    _ = ∑' k : ℤ, ∫ t in a..b, f k t := by
      apply tsum_congr
      intro k
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact (clippedCell_eq α δ t k hδ hδp (hcut t ht).1 (hcut t ht).2).symm
    _ = ∫ t in a..b, ∑' k : ℤ, f k t := h
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      change (∑' k : ℤ, clippedCell α δ k t) = _
      have he (k : ℤ) := clippedCell_eq α δ t k hδ hδp (hcut t ht).1 (hcut t ht).2
      simp_rw [he]
      exact tsum_div_const

lemma outerValue_periodized (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hδp : δ < Real.pi/2) :
    outerValue α δ = (∫ t in (-Real.pi/2)..(-δ), periodizedWeight α t / Real.sin t^2) +
      (∫ t in δ..(Real.pi/2), periodizedWeight α t / Real.sin t^2) := by
  have hleft : ∀ t ∈ Icc (-Real.pi/2) (-δ), |t| ≤ Real.pi/2 ∧ δ ≤ |t| := by
    intro t ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    constructor <;> linarith [ht.1,ht.2]
  have hright : ∀ t ∈ Icc δ (Real.pi/2), |t| ≤ Real.pi/2 ∧ δ ≤ |t| := by
    intro t ht
    rw [abs_of_nonneg (by linarith [ht.1])]
    exact ⟨ht.2,ht.1⟩
  have hs (a b : ℝ) (hab : a ≤ b) (hcut : ∀ t ∈ Icc a b, |t| ≤ Real.pi/2 ∧ δ ≤ |t|) :
      Summable (fun k : ℤ => ∫ t in a..b, weight α (t+(k : ℝ)*Real.pi)/Real.sin t^2) := by
    apply (((latticeMajorant_summable α hα).div_const (Real.sin δ^2)).mul_left |b-a|).of_norm_bounded
    intro k
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := latticeMajorant α k / Real.sin δ^2)
      (f := fun t => weight α (t+(k : ℝ)*Real.pi)/Real.sin t^2) ?_
    · nlinarith
    · intro t ht
      rw [uIoc_of_le hab] at ht
      have htc := hcut t ⟨ht.1.le,ht.2⟩
      have hh := poleIntegrand_cell_bound α δ t k hα hδ hδp htc.1 htc.2
      simpa only [poleIntegrand,sin_sq_shift] using hh
  unfold outerValue
  simp_rw [cellTruncation_shift]
  rw [Summable.tsum_add (hs _ _ (by linarith) hleft) (hs _ _ hδp.le hright),
    periodized_cut_integral α δ _ _ hα hδ hδp (by linarith) hleft,
    periodized_cut_integral α δ _ _ hα hδ hδp hδp.le hright]

end PeriodicPoleTask
