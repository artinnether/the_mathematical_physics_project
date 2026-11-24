import TuringTask.Periodization
import TuringTask.PoleOrientation
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.MeanValue

set_option backward.isDefEq.respectTransparency false
open Set Filter
namespace PeriodicPoleTask

noncomputable def weightDerivative (α x : ℝ) : ℝ := -2*α*x*weight α x
noncomputable def weightSecondDerivative (α x : ℝ) : ℝ := (4*α^2*x^2-2*α)*weight α x
noncomputable def periodizedDerivative (α t : ℝ) : ℝ := ∑' k : ℤ, weightDerivative α (t+(k : ℝ)*Real.pi)
noncomputable def periodizedSecondDerivative (α t : ℝ) : ℝ := ∑' k : ℤ, weightSecondDerivative α (t+(k : ℝ)*Real.pi)
noncomputable def latticeFirstMajorant (α : ℝ) (k : ℤ) : ℝ :=
  2*α*Real.pi*(|(k : ℝ)|+1)*latticeMajorant α k
noncomputable def latticeSecondMajorant (α : ℝ) (k : ℤ) : ℝ :=
  (4*α^2*Real.pi^2*(|(k : ℝ)|+1)^2+2*α)*latticeMajorant α k

lemma weightDerivative_hasDerivAt (α x : ℝ) :
    HasDerivAt (weightDerivative α) (weightSecondDerivative α x) x := by
  have h := ((hasDerivAt_id x).const_mul (-2*α)).mul (weight_hasDerivAt α x)
  unfold weightDerivative weightSecondDerivative
  convert h using 1 <;> (try rfl); (try simp only [id_eq]); ring

lemma gaussianPolynomial_summable_int (α : ℝ) (hα : 0 < α) (m : ℕ) :
    Summable (fun k : ℤ => |(k : ℝ)|^m * weight α ((k : ℝ)*Real.pi)) := by
  have h := summable_gaussian_polynomial (α*Real.pi^2) (by positivity) m
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · apply h.congr
    intro n
    simp only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ n by positivity), weight, mul_pow]
    congr 1; congr 1; ring
  · apply h.congr
    intro n
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤ n by positivity), weight, neg_mul, neg_sq, mul_pow]
    congr 1; congr 1; ring

lemma latticeFirstMajorant_summable (α : ℝ) (hα : 0 < α) : Summable (latticeFirstMajorant α) := by
  have h := ((gaussianPolynomial_summable_int (α/2) (by positivity) 1).add
    (gaussianPolynomial_summable_int (α/2) (by positivity) 0)).mul_left
      (2*α*Real.pi*Real.exp (α*Real.pi^2/4))
  apply h.congr
  intro k
  unfold latticeFirstMajorant latticeMajorant
  simp only [pow_one,pow_zero,one_mul]
  ring

lemma latticeSecondMajorant_summable (α : ℝ) (hα : 0 < α) : Summable (latticeSecondMajorant α) := by
  have h0 := gaussianPolynomial_summable_int (α/2) (by positivity) 0
  have h1 := gaussianPolynomial_summable_int (α/2) (by positivity) 1
  have h2 := gaussianPolynomial_summable_int (α/2) (by positivity) 2
  have h := (((h2.add (h1.mul_left 2)).add h0).mul_left (4*α^2*Real.pi^2)).add (h0.mul_left (2*α))
  apply (h.mul_left (Real.exp (α*Real.pi^2/4))).congr
  intro k
  unfold latticeSecondMajorant latticeMajorant
  simp only [pow_one,pow_zero,one_mul]
  ring

lemma shifted_radius_bound (t : ℝ) (k : ℤ) (ht : |t| ≤ Real.pi/2) :
    |t+(k : ℝ)*Real.pi| ≤ Real.pi*(|(k : ℝ)|+1) := by
  calc
    _ ≤ |t|+|(k : ℝ)*Real.pi| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul,abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos]

lemma shifted_weightDerivative_bound (α t : ℝ) (k : ℤ) (hα : 0 < α) (ht : |t| ≤ Real.pi/2) :
    ‖weightDerivative α (t+(k : ℝ)*Real.pi)‖ ≤ latticeFirstMajorant α k := by
  unfold weightDerivative latticeFirstMajorant
  simp only [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_pos hα,
    abs_of_pos (weight_pos _ _)]
  norm_num
  have h := mul_le_mul (shifted_radius_bound t k ht) (shifted_weight_bound α t k hα ht)
    (weight_pos α _).le (by positivity : 0 ≤ Real.pi*(|(k : ℝ)|+1))
  nlinarith

lemma shifted_weightSecondDerivative_bound (α t : ℝ) (k : ℤ) (hα : 0 < α) (ht : |t| ≤ Real.pi/2) :
    ‖weightSecondDerivative α (t+(k : ℝ)*Real.pi)‖ ≤ latticeSecondMajorant α k := by
  have hr := shifted_radius_bound t k ht
  have hr2 : (t+(k : ℝ)*Real.pi)^2 ≤ Real.pi^2*(|(k : ℝ)|+1)^2 := by
    nlinarith [abs_nonneg (t+(k : ℝ)*Real.pi), sq_abs (t+(k : ℝ)*Real.pi)]
  have hc : |4*α^2*(t+(k : ℝ)*Real.pi)^2-2*α| ≤ 4*α^2*Real.pi^2*(|(k : ℝ)|+1)^2+2*α := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (t+(k : ℝ)*Real.pi), mul_le_mul_of_nonneg_left hr2 (show 0 ≤ 4*α^2 by positivity)]
  unfold weightSecondDerivative latticeSecondMajorant
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (weight_pos _ _)]
  exact mul_le_mul hc (shifted_weight_bound α t k hα ht) (weight_pos α _).le (by positivity)

lemma periodizedWeight_hasDerivAt (α t : ℝ) (hα : 0 < α) (ht : t ∈ Ioo (-Real.pi/2) (Real.pi/2)) :
    HasDerivAt (periodizedWeight α) (periodizedDerivative α t) t := by
  unfold periodizedWeight periodizedDerivative
  apply hasDerivAt_tsum_of_isPreconnected (latticeFirstMajorant_summable α hα)
    (g := fun k : ℤ => fun y : ℝ => weight α (y+(k : ℝ)*Real.pi))
    (t := Ioo (-Real.pi/2) (Real.pi/2))
    isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (g' := fun (k : ℤ) (y : ℝ) => weightDerivative α (y+(k : ℝ)*Real.pi))
    (y₀ := (0 : ℝ))
  · intro k y hy
    have h := (weight_hasDerivAt α (y+(k : ℝ)*Real.pi)).comp y ((hasDerivAt_id y).add_const ((k : ℝ)*Real.pi))
    simpa only [Function.comp_def, weightDerivative, mul_one, id_eq] using h
  · intro k y hy
    exact shifted_weightDerivative_bound α y k hα (abs_le.mpr ⟨by linarith [hy.1],hy.2.le⟩)
  · constructor <;> linarith [Real.pi_pos]
  · simpa only [zero_add] using poleMass_summable α hα
  · exact ht

lemma periodizedDerivative_hasDerivAt (α t : ℝ) (hα : 0 < α) (ht : t ∈ Ioo (-Real.pi/2) (Real.pi/2)) :
    HasDerivAt (periodizedDerivative α) (periodizedSecondDerivative α t) t := by
  unfold periodizedDerivative periodizedSecondDerivative
  apply hasDerivAt_tsum_of_isPreconnected (latticeSecondMajorant_summable α hα)
    (g := fun k : ℤ => fun y : ℝ => weightDerivative α (y+(k : ℝ)*Real.pi))
    (t := Ioo (-Real.pi/2) (Real.pi/2))
    isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (g' := fun (k : ℤ) (y : ℝ) => weightSecondDerivative α (y+(k : ℝ)*Real.pi))
    (y₀ := (0 : ℝ))
  · intro k y hy
    have h := (weightDerivative_hasDerivAt α (y+(k : ℝ)*Real.pi)).comp y ((hasDerivAt_id y).add_const ((k : ℝ)*Real.pi))
    simpa only [Function.comp_def,mul_one,id_eq] using h
  · intro k y hy
    exact shifted_weightSecondDerivative_bound α y k hα (abs_le.mpr ⟨by linarith [hy.1],hy.2.le⟩)
  · constructor <;> linarith [Real.pi_pos]
  · apply (latticeFirstMajorant_summable α hα).of_norm_bounded
    intro k
    exact shifted_weightDerivative_bound α 0 k hα (by simp; positivity)
  · exact ht

lemma periodizedDerivative_zero (α : ℝ) : periodizedDerivative α 0 = 0 := by
  let f : ℤ → ℝ := fun k => weightDerivative α ((k : ℝ)*Real.pi)
  have hodd (k : ℤ) : f (-k) = -f k := by
    dsimp [f,weightDerivative]
    simp only [Int.cast_neg,neg_mul,weight_even]
    ring
  have h := (Equiv.neg ℤ).tsum_eq f
  have he : (∑' k : ℤ, f (-k)) = -(∑' k : ℤ, f k) := by
    simp_rw [hodd]; exact tsum_neg
  have hh : (∑' k : ℤ, f (-k)) = ∑' k : ℤ, f k := h
  rw [he] at hh
  change (∑' k : ℤ, weightDerivative α (0+(k : ℝ)*Real.pi)) = 0
  simp only [zero_add]
  change (∑' k : ℤ, f k) = 0
  linarith

lemma periodizedSecondDerivative_bound (α t : ℝ) (hα : 0 < α) (ht : |t| ≤ Real.pi/2) :
    ‖periodizedSecondDerivative α t‖ ≤ ∑' k : ℤ, latticeSecondMajorant α k := by
  have hn : Summable (fun k : ℤ => ‖weightSecondDerivative α (t+(k : ℝ)*Real.pi)‖) :=
    (latticeSecondMajorant_summable α hα).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => shifted_weightSecondDerivative_bound α t k hα ht)
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun k => shifted_weightSecondDerivative_bound α t k hα ht)
      (latticeSecondMajorant_summable α hα))

lemma periodizedWeight_quadratic_bound (α t : ℝ) (hα : 0 < α) (ht : |t| < Real.pi/2) :
    ‖periodizedWeight α t - poleMass α‖ ≤ (∑' k : ℤ, latticeSecondMajorant α k) * t^2 := by
  let M := ∑' k : ℤ, latticeSecondMajorant α k
  have hM : 0 ≤ M := tsum_nonneg (fun k => by unfold latticeSecondMajorant latticeMajorant weight; positivity)
  have hs : Icc (-|t|) |t| ⊆ Ioo (-Real.pi/2) (Real.pi/2) := by
    intro y hy
    constructor <;> linarith [hy.1,hy.2,Real.pi_pos]
  have h0 : (0 : ℝ) ∈ Icc (-|t|) |t| := ⟨neg_nonpos.mpr (abs_nonneg t),abs_nonneg t⟩
  have hD (y : ℝ) (hy : y ∈ Icc (-|t|) |t|) : ‖periodizedDerivative α y‖ ≤ M*|t| := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (periodizedDerivative_hasDerivAt α z hα (hs hz)).hasDerivWithinAt)
      (fun z hz => periodizedSecondDerivative_bound α z hα
        (abs_le.mpr ⟨by linarith [(hs hz).1],(hs hz).2.le⟩))
      (convex_Icc (-|t|) |t|) h0 hy
    rw [periodizedDerivative_zero,sub_zero,sub_zero,Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hy) hM)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (periodizedWeight_hasDerivAt α z hα (hs hz)).hasDerivWithinAt)
    hD (convex_Icc (-|t|) |t|) h0 (abs_le.mp (le_refl |t|))
  rw [periodizedWeight_at_zero,sub_zero,Real.norm_eq_abs] at h
  convert h using 1 <;> dsimp [M]; nlinarith [sq_abs t]

end PeriodicPoleTask
