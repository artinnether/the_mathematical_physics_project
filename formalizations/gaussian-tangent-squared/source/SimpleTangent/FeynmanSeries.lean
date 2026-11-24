import SimpleTangent.Regulator
import SimpleTangent.ComplexSeries
import SimpleTangent.Series
import ShiftedCosine.FeynmanLimit

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace TangentShiftTask

lemma root_one_sub_sq_ne (b ε : ℝ) (hε : 0 < ε) : 1-regulatorRoot b ε^2 ≠ 0 := by
  rw [root_square b ε hε]
  intro h
  have hi := congrArg Complex.im h
  simp only [← Complex.ofReal_pow, Complex.sub_im,Complex.add_im,Complex.neg_im,
    Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.one_im,Complex.zero_im,zero_mul,one_mul,zero_add,neg_zero] at hi
  linarith

lemma kernel_fourier (b ε x : ℝ) (hε : 0 < ε) :
    (Real.cos x : ℂ)^2/regulatedDenominator b ε x =
      1/(regulatorRoot b ε*(1+regulatorRoot b ε))+
      2/(regulatorRoot b ε*(1-regulatorRoot b ε^2))*
        complexCosineSeries (fun n => regulatorRatio b ε^(n+1)) x := by
  let s := regulatorRoot b ε
  let q := regulatorRatio b ε
  have hs : s ≠ 0 := root_ne_zero b ε hε
  have hp : 1+s ≠ 0 := one_add_root_ne b ε
  have hm : 1-s^2 ≠ 0 := root_one_sub_sq_ne b ε hε
  have hD := regulatedDenominator_ne_zero b ε x hε
  have hq := ratio_norm_lt_one b ε hε
  have hgeo := ShiftedCosineTask.complex_geometric_tsum q (2*x) hq
  have he : ShiftedCosineTask.complexCosineSeries (fun n => q^(n+1)) (2*x)=
      complexCosineSeries (fun n => q^(n+1)) x := by
    unfold ShiftedCosineTask.complexCosineSeries complexCosineSeries
    apply tsum_congr
    intro n
    rw [show (n+1 : ℝ)*(2*x)=2*(n+1 : ℝ)*x by ring]
  rw [he] at hgeo
  have hc : (Real.cos (2*x) : ℂ)=2*(Real.cos x : ℂ)^2-1 := by
    rw [Real.cos_two_mul]; push_cast; ring
  rw [hc] at hgeo
  have hd : regulatedDenominator b ε x=(Real.sin x : ℂ)^2+s^2*(Real.cos x : ℂ)^2 := by
    dsimp only [s]
    rw [root_square b ε hε]
    unfold regulatedDenominator denominator
    push_cast
    ring
  have htrig : (Real.sin x : ℂ)^2+(Real.cos x : ℂ)^2=1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq x
  have hqd : 1-2*q*(2*(Real.cos x : ℂ)^2-1)+q^2 =
      4*regulatedDenominator b ε x/(1+s)^2 := by
    dsimp only [q,regulatorRatio]
    change 1-2*((1-s)/(1+s))*(2*(Real.cos x : ℂ)^2-1)+((1-s)/(1+s))^2 = _
    rw [hd]
    field_simp [hp]
    linear_combination -4*htrig
  have hqnum : 1-q^2=4*s/(1+s)^2 := by
    dsimp only [q,regulatorRatio]
    change 1-((1-s)/(1+s))^2=4*s/(1+s)^2
    field_simp [hp]
    ring
  rw [hqd,hqnum] at hgeo
  have hg : 1+2*complexCosineSeries (fun n => q^(n+1)) x=s/regulatedDenominator b ε x := by
    rw [hgeo]
    field_simp [hp,hD]
  change (Real.cos x : ℂ)^2/regulatedDenominator b ε x =
    1/(s*(1+s))+2/(s*(1-s^2))*complexCosineSeries (fun n => q^(n+1)) x
  have hsum : complexCosineSeries (fun n => q^(n+1)) x=(s/regulatedDenominator b ε x-1)/2 := by
    rw [← hg]
    ring
  have hsin : (Real.sin x : ℂ)^2=1-(Real.cos x : ℂ)^2 := by linear_combination htrig
  rw [hsum]
  field_simp [hs,hp,hm,hD]
  rw [hd,hsin]
  ring

lemma ratio_series_summable (b ε : ℝ) (hε : 0 < ε) :
    Summable (fun n : ℕ => regulatorRatio b ε^(n+1)) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_norm_lt_one (ratio_norm_lt_one b ε hε))

noncomputable def feynmanSeriesValue (α b ε : ℝ) : ℂ :=
  (Real.sqrt (Real.pi/α) : ℂ)*
    (1/(regulatorRoot b ε*(1+regulatorRoot b ε))+
      2/(regulatorRoot b ε*(1-regulatorRoot b ε^2))*
        ∑' n : ℕ, regulatorRatio b ε^(n+1)*(Real.exp (-((n+1 : ℝ)^2)/α) : ℂ))

lemma feynmanIntegral_eq (α b ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    feynmanIntegral α b ε=feynmanSeriesValue α b ε := by
  have hw : Integrable (weight α) := integrable_exp_neg_mul_sq hα
  have hs := gaussian_complexSeries_integrable α hα _ (ratio_series_summable b ε hε)
  have he (x : ℝ) : feynmanIntegrand α b ε x=
      (weight α x : ℂ)*(1/(regulatorRoot b ε*(1+regulatorRoot b ε)))+
      ((weight α x : ℂ)*complexCosineSeries (fun n => regulatorRatio b ε^(n+1)) x)*
        (2/(regulatorRoot b ε*(1-regulatorRoot b ε^2))) := by
    unfold feynmanIntegrand
    rw [mul_div_assoc,kernel_fourier b ε x hε]
    ring
  unfold feynmanIntegral
  simp_rw [he]
  have hadd := integral_add (hw.ofReal.mul_const (1/(regulatorRoot b ε*(1+regulatorRoot b ε)))) (hs.mul_const (2/(regulatorRoot b ε*(1-regulatorRoot b ε^2))))
  have hadd' : (∫ x : ℝ, (weight α x : ℂ)*(1/(regulatorRoot b ε*(1+regulatorRoot b ε)))+
      ((weight α x : ℂ)*complexCosineSeries (fun n => regulatorRatio b ε^(n+1)) x)*
        (2/(regulatorRoot b ε*(1-regulatorRoot b ε^2)))) = _ := hadd
  rw [hadd',integral_mul_const,integral_mul_const]
  have hwc : (∫ x : ℝ, (weight α x : ℂ))=((∫ x : ℝ, weight α x : ℝ) : ℂ) :=
    integral_complex_ofReal
  erw [hwc,gaussian_complexSeries_integral α hα _ (ratio_series_summable b ε hε)]
  have hg : (∫ x : ℝ, weight α x)=Real.sqrt (Real.pi/α) := integral_gaussian α
  rw [hg]
  unfold feynmanSeriesValue
  ring

end TangentShiftTask
