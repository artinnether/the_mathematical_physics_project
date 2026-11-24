import ShiftedCosine.Abel
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

lemma half_pi_odd_trig (n : ℕ) :
    Real.cos ((2*n+1 : ℕ)* (Real.pi/2)) = 0 ∧
    Real.sin ((2*n+1 : ℕ)* (Real.pi/2)) = (-1 : ℝ)^n := by
  have he : ((2*n+1 : ℕ) : ℝ)*(Real.pi/2) = (n : ℝ)*Real.pi+Real.pi/2 := by
    push_cast; ring
  rw [he,Real.cos_add_pi_div_two,Real.sin_add_pi_div_two,
    Real.sin_nat_mul_pi,Real.cos_nat_mul_pi]
  simp

lemma half_pi_even_trig (n : ℕ) :
    Real.cos ((2*n+2 : ℕ)* (Real.pi/2)) = (-1 : ℝ)^(n+1) ∧
    Real.sin ((2*n+2 : ℕ)* (Real.pi/2)) = 0 := by
  have he : ((2*n+2 : ℕ) : ℝ)*(Real.pi/2) = ((n+1 : ℕ) : ℝ)*Real.pi := by
    push_cast; ring
  rw [he,Real.cos_nat_mul_pi,Real.sin_nat_mul_pi]
  exact ⟨rfl,rfl⟩

lemma realCoefficient_half_pi_even (n : ℕ) : realCoefficient (Real.pi/2) (2*n) = 0 := by
  unfold realCoefficient
  have h := (half_pi_odd_trig n).1
  norm_cast at h
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] at h
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  rw [Real.sin_pi_div_two,Real.cos_pi_div_two,h]
  simp

lemma realCoefficient_half_pi_odd (n : ℕ) :
    realCoefficient (Real.pi/2) (2*n+1) = 2*(n+1 : ℝ)*(-1 : ℝ)^n := by
  unfold realCoefficient
  have h := (half_pi_even_trig n).1
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] at h
  rw [Real.sin_pi_div_two,Real.cos_pi_div_two]
  have he : ((2*n+1 : ℕ) : ℝ)+1=2*(n : ℝ)+2 := by push_cast; ring
  rw [he,h,pow_succ]
  push_cast
  ring

lemma imaginaryCoefficient_half_pi_even (n : ℕ) :
    imaginaryCoefficient (Real.pi/2) (2*n) = -(2*n+1 : ℝ)*(-1 : ℝ)^n := by
  unfold imaginaryCoefficient
  have h := (half_pi_odd_trig n).2
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] at h
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  rw [Real.sin_pi_div_two,Real.cos_pi_div_two,h]
  push_cast
  ring

lemma imaginaryCoefficient_half_pi_odd (n : ℕ) :
    imaginaryCoefficient (Real.pi/2) (2*n+1) = 0 := by
  unfold imaginaryCoefficient
  have h := (half_pi_even_trig n).2
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] at h
  rw [Real.sin_pi_div_two,Real.cos_pi_div_two]
  have he : ((2*n+1 : ℕ) : ℝ)+1=2*(n : ℝ)+2 := by push_cast; ring
  rw [he,h]
  simp

lemma finitePartValue_half_pi (a : ℝ) (ha : 0 < a) :
    finitePartValue a (Real.pi/2) =
      4*Real.sqrt (Real.pi/a)*∑' n : ℕ, (n+1 : ℝ)*(-1 : ℝ)^n*
        Real.exp (-((n+1 : ℝ)^2)/a) := by
  have hs := real_spectral_summable a (Real.pi/2) ha (by positivity) (by linarith [Real.pi_pos])
  have he := hs.comp_injective (i := fun n : ℕ => 2*n) (by intro n m h; dsimp at h; omega)
  have ho := hs.comp_injective (i := fun n : ℕ => 2*n+1) (by intro n m h; dsimp at h; omega)
  have hsplit := tsum_even_add_odd (f := fun n => realCoefficient (Real.pi/2) n*gaussianTerm a n) he ho
  simp only [realCoefficient_half_pi_even,zero_mul,tsum_zero,zero_add] at hsplit
  unfold finitePartValue
  rw [← hsplit]
  simp_rw [realCoefficient_half_pi_odd]
  have hg (n : ℕ) : gaussianTerm a (2*n+1)=Real.exp (-((n+1 : ℝ)^2)/a) := by
    unfold gaussianTerm
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [hg,show ∀ n : ℕ, 2*(n+1 : ℝ)*(-1 : ℝ)^n*Real.exp (-((n+1 : ℝ)^2)/a)=
      2*((n+1 : ℝ)*(-1 : ℝ)^n*Real.exp (-((n+1 : ℝ)^2)/a)) from fun n => by ring]
  rw [tsum_mul_left]
  ring

lemma imaginaryValue_half_pi (a : ℝ) (ha : 0 < a) :
    imaginaryValue a (Real.pi/2) =
      -2*Real.sqrt (Real.pi/a)*∑' n : ℕ, (2*n+1 : ℝ)*(-1 : ℝ)^n*
        Real.exp (-((2*n+1 : ℝ)^2)/(4*a)) := by
  have hs := imaginary_spectral_summable a (Real.pi/2) ha (by positivity) (by linarith [Real.pi_pos])
  have he := hs.comp_injective (i := fun n : ℕ => 2*n) (by intro n m h; dsimp at h; omega)
  have ho := hs.comp_injective (i := fun n : ℕ => 2*n+1) (by intro n m h; dsimp at h; omega)
  have hsplit := tsum_even_add_odd (f := fun n => imaginaryCoefficient (Real.pi/2) n*gaussianTerm a n) he ho
  simp only [imaginaryCoefficient_half_pi_odd,zero_mul,tsum_zero,add_zero] at hsplit
  unfold imaginaryValue
  rw [Real.sin_pi_div_two,Real.cos_pi_div_two,← hsplit]
  simp_rw [imaginaryCoefficient_half_pi_even]
  have hg (n : ℕ) : gaussianTerm a (2*n)=Real.exp (-((2*n+1 : ℝ)^2)/(4*a)) := by
    unfold gaussianTerm
    push_cast
    rfl
  simp_rw [hg,show ∀ n : ℕ, -(2*n+1 : ℝ)*(-1 : ℝ)^n*Real.exp (-((2*n+1 : ℝ)^2)/(4*a))=
      -((2*n+1 : ℝ)*(-1 : ℝ)^n*Real.exp (-((2*n+1 : ℝ)^2)/(4*a))) from fun n => by ring]
  rw [tsum_neg]
  norm_num
  ring

end ShiftedCosineTask
