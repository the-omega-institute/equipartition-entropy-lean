import DinovLean.Covariance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Moments.Covariance

/-! Exact moments of the nonuniform fourth-harmonic angular density. -/
noncomputable section
open Real MeasureTheory Set
namespace DinovLean.Fourth

abbrev angular : Measure ℝ := volume.restrict (Ioc (-π) π)
def phi (t : ℝ) : ℝ := (1 + cos (4 * t) / 2) / (2 * π)

@[fun_prop] theorem phi_continuous : Continuous phi := by unfold phi; fun_prop

theorem phi_pos (t : ℝ) : 0 < phi t := by
  unfold phi
  apply div_pos
  · linarith [neg_one_le_cos (4 * t)]
  · positivity

theorem phi_nonuniform : phi 0 ≠ phi (π / 4) := by
  unfold phi
  simp only [mul_zero, cos_zero]
  have he : (4 : ℝ) * (π / 4) = π := by ring
  rw [he, cos_pi]
  intro h
  have hpi : 2 * π ≠ 0 := by positivity
  have := (div_left_inj' hpi).mp h
  norm_num at this

theorem phi_polynomial (t : ℝ) :
    phi t = ((3/2 : ℝ) + 4 * cos t ^ 4 - 4 * cos t ^ 2) / (2 * π) := by
  unfold phi
  have he : (4 : ℝ) * t = 2 * (2 * t) := by ring
  rw [he, cos_two_mul, cos_two_mul]
  ring

private theorem cos_int_zero : (∫ t in (-π)..π, cos t) = 0 := by simp
private theorem cos_int_two : (∫ t in (-π)..π, cos t ^ 2) = π := by simp
private theorem cos_int_three : (∫ t in (-π)..π, cos t ^ 3) = 0 := by
  simp
private theorem cos_int_four : (∫ t in (-π)..π, cos t ^ 4) = 3 * π / 4 := by
  have h := integral_cos_pow (a := -π) (b := π) (n := 2)
  norm_num [cos_int_two] at h ⊢; linarith
private theorem cos_int_five : (∫ t in (-π)..π, cos t ^ 5) = 0 := by
  have h := integral_cos_pow (a := -π) (b := π) (n := 3)
  norm_num [cos_int_three] at h ⊢; exact h
private theorem cos_int_six : (∫ t in (-π)..π, cos t ^ 6) = 5 * π / 8 := by
  have h := integral_cos_pow (a := -π) (b := π) (n := 4)
  norm_num [cos_int_four] at h ⊢; linarith
private theorem sin_cos_int (n : ℕ) : (∫ t in (-π)..π, sin t * cos t ^ n) = 0 := by
  simpa using (integral_sin_pow_odd_mul_cos_pow (a := -π) (b := π) 0 n)

/-- Normalization against actual restricted angular Lebesgue measure. -/
theorem phi_mass : ∫ t, phi t ∂angular = 1 := by
  rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
  simp_rw [phi_polynomial]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_div, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul, cos_int_four, cos_int_two]
  field_simp; ring

theorem cos_mean : ∫ t, cos t * phi t ∂angular = 0 := by
  rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
  have he : (fun t => cos t * phi t) = fun t =>
      ((3/2 : ℝ) * cos t + 4 * cos t ^ 5 - 4 * cos t ^ 3) / (2 * π) := by
    funext t; rw [phi_polynomial]; ring
  rw [he]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_div, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    cos_int_five, cos_int_three, cos_int_zero]
  ring

theorem sin_mean : ∫ t, sin t * phi t ∂angular = 0 := by
  rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
  have he : (fun t => sin t * phi t) = fun t =>
      ((3/2 : ℝ) * sin t + 4 * (sin t * cos t ^ 4) - 4 * (sin t * cos t ^ 2)) / (2 * π) := by
    funext t; rw [phi_polynomial]; ring
  rw [he]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_div, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    sin_cos_int, integral_sin, cos_neg, sub_self]
  ring

theorem cos_sq : ∫ t, cos t ^ 2 * phi t ∂angular = 1/2 := by
  rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
  have he : (fun t => cos t ^ 2 * phi t) = fun t =>
      ((3/2 : ℝ) * cos t ^ 2 + 4 * cos t ^ 6 - 4 * cos t ^ 4) / (2 * π) := by
    funext t; rw [phi_polynomial]; ring
  rw [he]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_div, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    cos_int_six, cos_int_four, cos_int_two]
  field_simp; ring

theorem sin_sq : ∫ t, sin t ^ 2 * phi t ∂angular = 1/2 := by
  have he : (fun t => sin t ^ 2 * phi t) = fun t => phi t - cos t ^ 2 * phi t := by
    funext t
    have ht : sin t ^ 2 = 1 - cos t ^ 2 := by nlinarith [sin_sq_add_cos_sq t]
    rw [ht]; ring
  rw [he, integral_sub]
  · rw [phi_mass, cos_sq]; norm_num
  · exact phi_continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact (by fun_prop : Continuous (fun t => cos t ^ 2 * phi t)).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem sin_cos : ∫ t, sin t * cos t * phi t ∂angular = 0 := by
  rw [← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
  have he : (fun t => sin t * cos t * phi t) = fun t =>
      ((3/2 : ℝ) * (sin t * cos t ^ 1) + 4 * (sin t * cos t ^ 5) - 4 * (sin t * cos t ^ 3)) / (2 * π) := by
    funext t; rw [phi_polynomial]; ring
  rw [he]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_div, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_const_mul, sin_cos_int]
  ring

/-- Nonuniformity holds modulo null sets, as required for probability densities. -/
theorem phi_not_ae_uniform : ¬ (phi =ᵐ[angular] fun _ => 1 / (2 * π)) := by
  intro h
  have he := Measure.eqOn_Ioc_of_ae_eq volume h phi_continuous.continuousOn continuous_const.continuousOn
  have h0 := he (show (0 : ℝ) ∈ Ioc (-π) π by constructor <;> linarith [pi_pos])
  have h1 := he (show π / 4 ∈ Ioc (-π) π by constructor <;> linarith [pi_pos])
  exact phi_nonuniform (h0.trans h1.symm)

end DinovLean.Fourth
