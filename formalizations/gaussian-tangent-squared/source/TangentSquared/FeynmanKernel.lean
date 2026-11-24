import TangentSquared.Basic
import SimpleTangent.FeynmanSeries

set_option maxHeartbeats 3000000
open Filter MeasureTheory Set
open scoped Topology
namespace TangentSquaredTask

noncomputable def regulatorA (s : ℂ) : ℂ := (1+2*s)/(2*s^3*(1+s)^2)
noncomputable def regulatorB (s : ℂ) : ℂ := (1-3*s^2)/(s^3*(1-s^2)^2)
noncomputable def regulatorC (s : ℂ) : ℂ := 2/(s^2*(1-s^2)^2)

lemma kernel_fourier (b ε x : ℝ) (hε : 0 < ε) :
    (Real.cos x : ℂ)^4/(regulatedDenominator b ε x)^2 =
      regulatorA (TangentShiftTask.regulatorRoot b ε) +
      regulatorB (TangentShiftTask.regulatorRoot b ε)*
        TangentShiftTask.complexCosineSeries (fun n => TangentShiftTask.regulatorRatio b ε^(n+1)) x +
      regulatorC (TangentShiftTask.regulatorRoot b ε)*
        TangentShiftTask.complexCosineSeries (fun n => (n+1 : ℂ)*TangentShiftTask.regulatorRatio b ε^(n+1)) x := by
  let s := TangentShiftTask.regulatorRoot b ε
  let q := TangentShiftTask.regulatorRatio b ε
  have hs : s ≠ 0 := TangentShiftTask.root_ne_zero b ε hε
  have hp : 1+s ≠ 0 := TangentShiftTask.one_add_root_ne b ε
  have hm : 1-s^2 ≠ 0 := TangentShiftTask.root_one_sub_sq_ne b ε hε
  have hD : regulatedDenominator b ε x ≠ 0 := TangentShiftTask.regulatedDenominator_ne_zero b ε x hε
  have hq := TangentShiftTask.ratio_norm_lt_one b ε hε
  have hgeo := ShiftedCosineTask.complex_geometric_tsum q (2*x) hq
  have hw := ShiftedCosineTask.complex_weighted_tsum q (2*x) hq
  have he (f : ℕ → ℂ) : ShiftedCosineTask.complexCosineSeries f (2*x)=
      TangentShiftTask.complexCosineSeries f x := by
    unfold ShiftedCosineTask.complexCosineSeries TangentShiftTask.complexCosineSeries
    apply tsum_congr
    intro n
    rw [show (n+1 : ℝ)*(2*x)=2*(n+1 : ℝ)*x by ring]
  rw [he] at hgeo hw
  have hc : (Real.cos (2*x) : ℂ)=2*(Real.cos x : ℂ)^2-1 := by
    rw [Real.cos_two_mul]
    push_cast
    ring
  rw [hc] at hgeo hw
  have hd : regulatedDenominator b ε x=1+(s^2-1)*(Real.cos x : ℂ)^2 := by
    dsimp only [s]
    rw [TangentShiftTask.root_square b ε hε]
    have ht : (Real.sin x : ℂ)^2+(Real.cos x : ℂ)^2=1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq x
    unfold regulatedDenominator denominator
    simp only [Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_mul]
    linear_combination ht
  have hqd : 1-2*q*(2*(Real.cos x : ℂ)^2-1)+q^2 =
      4*regulatedDenominator b ε x/(1+s)^2 := by
    dsimp only [q,TangentShiftTask.regulatorRatio]
    change 1-2*((1-s)/(1+s))*(2*(Real.cos x : ℂ)^2-1)+((1-s)/(1+s))^2 = _
    rw [hd]
    field_simp [hp]
    ring
  have hqnum : 1-q^2=4*s/(1+s)^2 := by
    dsimp only [q,TangentShiftTask.regulatorRatio]
    change 1-((1-s)/(1+s))^2=4*s/(1+s)^2
    field_simp [hp]
    ring
  rw [hqd,hqnum] at hgeo
  rw [hqd] at hw
  have hg : TangentShiftTask.complexCosineSeries (fun n => q^(n+1)) x=
      (s/regulatedDenominator b ε x-1)/2 := by
    have hg0 : 1+2*TangentShiftTask.complexCosineSeries (fun n => q^(n+1)) x=s/regulatedDenominator b ε x := by
      rw [hgeo]
      field_simp [hp,hD]
    calc
      _ = (1+2*TangentShiftTask.complexCosineSeries (fun n => q^(n+1)) x-1)/2 := by ring
      _ = _ := by rw [hg0]
  change (Real.cos x : ℂ)^4/(regulatedDenominator b ε x)^2 =
    regulatorA s+regulatorB s*TangentShiftTask.complexCosineSeries (fun n => q^(n+1)) x+
    regulatorC s*TangentShiftTask.complexCosineSeries (fun n => (n+1 : ℂ)*q^(n+1)) x
  rw [hg,hw]
  unfold regulatorA regulatorB regulatorC
  dsimp only [q,TangentShiftTask.regulatorRatio]
  change _ = (1+2*s)/(2*s^3*(1+s)^2)+(1-3*s^2)/(s^3*(1-s^2)^2)*
    ((s/regulatedDenominator b ε x-1)/2)+2/(s^2*(1-s^2)^2)*
    ((((1-s)/(1+s))*(1+((1-s)/(1+s))^2)*(2*(Real.cos x : ℂ)^2-1)-
      2*((1-s)/(1+s))^2)/(4*regulatedDenominator b ε x/(1+s)^2)^2)
  field_simp [hs,hp,hm,hD]
  rw [hd]
  ring

end TangentSquaredTask
