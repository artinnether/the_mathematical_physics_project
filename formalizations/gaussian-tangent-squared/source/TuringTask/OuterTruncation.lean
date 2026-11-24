import TuringTask.Series
import Mathlib.Order.Filter.AtTopBot.Interval

open Filter MeasureTheory Set
open scoped Topology
namespace PeriodicPoleTask

noncomputable def latticeMajorant (α : ℝ) (k : ℤ) : ℝ :=
  Real.exp (α*Real.pi^2/4) * weight (α/2) ((k : ℝ)*Real.pi)

lemma shifted_weight_bound (α t : ℝ) (k : ℤ) (hα : 0 < α) (ht : |t| ≤ Real.pi/2) :
    weight α (t+(k : ℝ)*Real.pi) ≤ latticeMajorant α k := by
  unfold latticeMajorant weight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht2 : t^2 ≤ Real.pi^2/4 := by
    have h := abs_le.mp ht
    nlinarith [sq_nonneg (t+Real.pi/2), sq_nonneg (t-Real.pi/2)]
  have hsq : ((k : ℝ)*Real.pi)^2/2 - t^2 ≤ (t+(k : ℝ)*Real.pi)^2 := by
    nlinarith [sq_nonneg (2*t+(k : ℝ)*Real.pi)]
  nlinarith

lemma latticeMajorant_summable (α : ℝ) (hα : 0 < α) : Summable (latticeMajorant α) :=
  (poleMass_summable (α/2) (by positivity)).mul_left _

lemma abs_sin_shift (t : ℝ) (k : ℤ) :
    |Real.sin (t+(k : ℝ)*Real.pi)| = |Real.sin t| := by
  rw [Real.sin_add_int_mul_pi, abs_mul]
  simp

lemma cut_sin_bound (δ t : ℝ) (hδ : 0 < δ) (hδp : δ < Real.pi/2)
    (ht : |t| ≤ Real.pi/2) (hcut : δ ≤ |t|) :
    Real.sin δ ≤ |Real.sin t| := by
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos])]
  exact Real.strictMonoOn_sin.monotoneOn
    ⟨by linarith [Real.pi_pos], hδp.le⟩
    ⟨by linarith [abs_nonneg t, Real.pi_pos], ht⟩ hcut

lemma poleIntegrand_cell_bound (α δ t : ℝ) (k : ℤ) (hα : 0 < α)
    (hδ : 0 < δ) (hδp : δ < Real.pi/2) (ht : |t| ≤ Real.pi/2) (hcut : δ ≤ |t|) :
    ‖poleIntegrand α (t+(k : ℝ)*Real.pi)‖ ≤ latticeMajorant α k / Real.sin δ^2 := by
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hs := cut_sin_bound δ t hδ hδp ht hcut
  have hss : Real.sin δ^2 ≤ Real.sin (t+(k : ℝ)*Real.pi)^2 := by
    rw [← sq_abs (Real.sin (t+(k : ℝ)*Real.pi)), abs_sin_shift]
    nlinarith [abs_nonneg (Real.sin t)]
  have hden : 0 < Real.sin (t+(k : ℝ)*Real.pi)^2 := lt_of_lt_of_le (sq_pos_of_pos hsδ) hss
  unfold poleIntegrand
  rw [norm_div, Real.norm_eq_abs, abs_of_pos (weight_pos _ _),
    Real.norm_eq_abs, abs_of_pos hden]
  exact div_le_div₀ (by unfold latticeMajorant weight; positivity) (shifted_weight_bound α t k hα ht)
    (sq_pos_of_pos hsδ) hss

lemma cellTruncation_bound (α δ : ℝ) (k : ℤ) (hα : 0 < α)
    (hδ : 0 < δ) (hδp : δ < Real.pi/2) :
    ‖cellTruncation α δ k‖ ≤ Real.pi * latticeMajorant α k / Real.sin δ^2 := by
  have hl : (k : ℝ)*Real.pi-Real.pi/2 ≤ (k : ℝ)*Real.pi-δ := by linarith
  have hr : (k : ℝ)*Real.pi+δ ≤ (k : ℝ)*Real.pi+Real.pi/2 := by linarith
  have hleft : ‖∫ x in ((k : ℝ)*Real.pi-Real.pi/2)..((k : ℝ)*Real.pi-δ), poleIntegrand α x‖ ≤
      (latticeMajorant α k / Real.sin δ^2) * (Real.pi/2-δ) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (k : ℝ)*Real.pi-Real.pi/2) (b := (k : ℝ)*Real.pi-δ)
      (C := latticeMajorant α k / Real.sin δ^2) (f := poleIntegrand α) ?_
    · convert h using 1
      rw [abs_of_nonneg (by linarith : 0 ≤ ((k : ℝ)*Real.pi-δ)-((k : ℝ)*Real.pi-Real.pi/2))]
      ring
    · intro x hx
      rw [uIoc_of_le hl] at hx
      have ht : |x-(k : ℝ)*Real.pi| ≤ Real.pi/2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
      have hc : δ ≤ |x-(k : ℝ)*Real.pi| := by
        rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]
      convert poleIntegrand_cell_bound α δ (x-(k : ℝ)*Real.pi) k hα hδ hδp ht hc using 1; congr 1; ring
  have hright : ‖∫ x in ((k : ℝ)*Real.pi+δ)..((k : ℝ)*Real.pi+Real.pi/2), poleIntegrand α x‖ ≤
      (latticeMajorant α k / Real.sin δ^2) * (Real.pi/2-δ) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (k : ℝ)*Real.pi+δ) (b := (k : ℝ)*Real.pi+Real.pi/2)
      (C := latticeMajorant α k / Real.sin δ^2) (f := poleIntegrand α) ?_
    · convert h using 1
      rw [abs_of_nonneg (by linarith : 0 ≤ ((k : ℝ)*Real.pi+Real.pi/2)-((k : ℝ)*Real.pi+δ))]
      ring
    · intro x hx
      rw [uIoc_of_le hr] at hx
      have ht : |x-(k : ℝ)*Real.pi| ≤ Real.pi/2 := abs_le.mpr ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩
      have hc : δ ≤ |x-(k : ℝ)*Real.pi| := by
        rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1]
      convert poleIntegrand_cell_bound α δ (x-(k : ℝ)*Real.pi) k hα hδ hδp ht hc using 1; congr 1; ring
  unfold cellTruncation
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ 2*(latticeMajorant α k / Real.sin δ^2)*(Real.pi/2-δ) := by linarith
    _ ≤ Real.pi * latticeMajorant α k / Real.sin δ^2 := by
      have hm : 0 ≤ latticeMajorant α k / Real.sin δ^2 := by unfold latticeMajorant weight; positivity
      have he : Real.pi * latticeMajorant α k / Real.sin δ^2 = Real.pi * (latticeMajorant α k / Real.sin δ^2) := by ring
      rw [he]
      nlinarith

lemma cellTruncation_summable (α δ : ℝ) (hα : 0 < α)
    (hδ : 0 < δ) (hδp : δ < Real.pi/2) : Summable (cellTruncation α δ) := by
  exact (((latticeMajorant_summable α hα).mul_left Real.pi).div_const (Real.sin δ^2)).of_norm_bounded
    (fun k => cellTruncation_bound α δ k hα hδ hδp)

noncomputable def outerValue (α δ : ℝ) : ℝ := ∑' k : ℤ, cellTruncation α δ k

lemma truncation_tendsto (α δ : ℝ) (hα : 0 < α)
    (hδ : 0 < δ) (hδp : δ < Real.pi/2) :
    Tendsto (truncation α δ) atTop (𝓝 (outerValue α δ)) := by
  exact (cellTruncation_summable α δ hα hδ hδp).hasSum.comp
    (Finset.tendsto_Icc_neg (R := ℤ))

end PeriodicPoleTask
