import TuringTask.Series

namespace PeriodicPoleTask

lemma weight_hasDerivAt (α x : ℝ) :
    HasDerivAt (weight α) (-2*α*x*weight α x) x := by
  have h := (((hasDerivAt_id x).pow 2).const_mul (-α)).exp
  unfold weight
  convert h using 1
  · ext y; simp
  · simp; ring

lemma pole_orientation (k : ℤ) : Real.cos ((k : ℝ)*Real.pi) = (-1 : ℝ)^k :=
  Real.cos_int_mul_pi k

lemma latticeDerivative_summable (α : ℝ) (hα : 0 < α) :
    Summable (fun k : ℤ => (-1 : ℝ)^k * (-2*α*((k : ℝ)*Real.pi)*weight α ((k : ℝ)*Real.pi))) := by
  have hg := summable_gaussian_polynomial (α*Real.pi^2) (by positivity) 1
  have hi : Summable (fun k : ℤ => |(k : ℝ)| * weight α ((k : ℝ)*Real.pi)) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor
    · apply hg.congr
      intro n
      simp only [weight, Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ n by positivity), pow_one]
      congr 1; congr 1; ring
    · apply hg.congr
      intro n
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ n by positivity),
        neg_mul, weight, pow_one]
      congr 1; congr 1; ring
  apply (hi.mul_left (2*α*Real.pi)).of_norm_bounded
  intro k
  simp only [norm_mul, Real.norm_eq_abs, abs_zpow, abs_neg, abs_one, one_zpow,
    abs_of_pos (weight_pos _ _), one_mul]
  norm_num only [abs_of_pos hα, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply le_of_eq
  ring

lemma latticeDerivative_sum_zero (α : ℝ) (_hα : 0 < α) :
    (∑' k : ℤ, (-1 : ℝ)^k * (-2*α*((k : ℝ)*Real.pi)*weight α ((k : ℝ)*Real.pi))) = 0 := by
  let f : ℤ → ℝ := fun k => (-1 : ℝ)^k * (-2*α*((k : ℝ)*Real.pi)*weight α ((k : ℝ)*Real.pi))
  have hodd (k : ℤ) : f (-k) = -f k := by
    have hs : (-1 : ℝ)^(-k) = (-1 : ℝ)^k := by
      rw [zpow_neg, ← inv_zpow]; norm_num
    dsimp [f]
    rw [hs]
    simp only [Int.cast_neg, neg_mul, weight_even]
    ring
  have h := Equiv.tsum_eq (Equiv.neg ℤ) f
  have he : (∑' k : ℤ, f (-k)) = -(∑' k : ℤ, f k) := by
    simp_rw [hodd]
    exact tsum_neg
  change (∑' k : ℤ, f k) = 0
  have hh : (∑' k : ℤ, f (-k)) = ∑' k : ℤ, f k := h
  rw [he] at hh
  linarith

end PeriodicPoleTask
