import DinovLean.ScalarInverse
import Mathlib.Analysis.Real.Pi.Bounds

/-! Further realization certificates for the fourth harmonic: full action
fiber, finite nonnegative action-angle entropy, and the symplectic form. -/
noncomputable section
open Real MeasureTheory Set Matrix
open scoped ENNReal
namespace DinovLean.Fourth

abbrev fullBase : Measure TorusTwo := base.prod base
def jointDensity (z : TorusTwo) : ℝ := density z.1 * density z.2

theorem torusLaw_density :
    torusLaw = fullBase.withDensity (fun z => ENNReal.ofReal (jointDensity z)) := by
  unfold torusLaw oneLaw
  rw [prod_withDensity density_measurable.ennreal_ofReal density_measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  exact ae_of_all _ (fun z => (ENNReal.ofReal_mul (density_pos z.1).le).symm)

theorem joint_mass : ∫ z, jointDensity z ∂fullBase = 1 := by
  unfold jointDensity
  rw [integral_prod_mul (f := density) (g := density), density_mass, mul_one]

theorem joint_action_fiber (J₁ J₂ : ℝ) :
    (∫ ts : ℝ × ℝ, jointDensity ((ts.1,J₁),(ts.2,J₂)) ∂angular.prod angular) = exp (-(J₁ + J₂)) := by
  unfold jointDensity
  rw [integral_prod_mul (f := fun t => density (t,J₁)) (g := fun t => density (t,J₂)),
    action_fiber, action_fiber, ← exp_add]
  congr 1; ring

theorem phi_le_one (t : ℝ) : phi t ≤ 1 := by
  unfold phi
  rw [div_le_iff₀ (by positivity : 0 < 2 * π)]
  linarith [cos_le_one (4 * t), pi_gt_three]

theorem density_le_one {z : ℝ × ℝ} (hJ : 0 ≤ z.2) : density z ≤ 1 := by
  apply mul_le_one₀ (phi_le_one _) (exp_pos _).le
  exact exp_le_one_iff.mpr (by linarith)

theorem density_log_decomposition (z : ℝ × ℝ) :
    density z * log (density z) =
      (phi z.1 * log (phi z.1)) * exp (-z.2) - phi z.1 * (z.2 * exp (-z.2)) := by
  unfold density
  rw [log_mul (phi_pos _).ne' (exp_pos _).ne', log_exp]
  ring

theorem density_log_integrable : Integrable (fun z => density z * log (density z)) base := by
  have hp : Continuous (fun t => phi t * log (phi t)) :=
    phi_continuous.mul (phi_continuous.log (fun t => (phi_pos t).ne'))
  have h1 : Integrable (fun z : ℝ × ℝ => (phi z.1 * log (phi z.1)) * exp (-z.2)) base :=
    (hp.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mul_prod action_integrable
  have h2 : Integrable (fun z : ℝ × ℝ => phi z.1 * (z.2 * exp (-z.2))) base :=
    (phi_continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mul_prod action_first_integrable
  exact (h1.sub h2).congr (ae_of_all _ (fun z => (density_log_decomposition z).symm))

/-- Differential entropy with respect to angular Lebesgue × positive-action Lebesgue. -/
def actionAngleEntropy : ℝ := -(∫ z, jointDensity z * log (jointDensity z) ∂fullBase)

theorem joint_log_decomposition (z : TorusTwo) :
    jointDensity z * log (jointDensity z) =
      (density z.1 * log (density z.1)) * density z.2 +
      density z.1 * (density z.2 * log (density z.2)) := by
  unfold jointDensity
  rw [log_mul (density_pos _).ne' (density_pos _).ne']
  ring

theorem joint_log_integrable : Integrable (fun z => jointDensity z * log (jointDensity z)) fullBase := by
  exact ((density_log_integrable.mul_prod density_integrable).add
    (density_integrable.mul_prod density_log_integrable)).congr
      (ae_of_all _ (fun z => (joint_log_decomposition z).symm))

theorem actionAngleEntropy_nonneg : 0 ≤ actionAngleEntropy := by
  apply neg_nonneg.mpr
  apply integral_nonpos_of_ae
  have hJ : ∀ᵐ z ∂fullBase, 0 < z.1.2 ∧ 0 < z.2.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    have hp : ∀ᵐ z ∂base, 0 < z.2 := by
      apply (Measure.ae_prod_iff_ae_ae (by measurability : MeasurableSet {z : ℝ × ℝ | 0 < z.2})).mpr
      exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Ioi)
    exact hp.mono (fun z hz => hp.mono (fun w hw => ⟨hz, hw⟩))
  filter_upwards [hJ] with z hz
  have hpos : 0 ≤ jointDensity z := mul_nonneg (density_pos _).le (density_pos _).le
  have hle : jointDensity z ≤ 1 :=
    mul_le_one₀ (density_le_one hz.1.le) (density_pos _).le (density_le_one hz.2.le)
  exact mul_nonpos_of_nonneg_of_nonpos hpos (log_nonpos hpos hle)

/-- Standard compatible complex structure for the interleaved symplectic form. -/
theorem omega_sq : omega * omega = -(1 : Matrix (Bool × Bool) (Bool × Bool) ℝ) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [Matrix.mul_apply, Fintype.sum_prod_type, omega]

theorem omega_orthogonal : omega.transpose * omega = 1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [Matrix.mul_apply, Fintype.sum_prod_type, omega]

/-- One bundled conclusion keeps the actual realization, spectrum witness,
and saturation tied to the same law. -/
theorem fourth_harmonic_witness :
    IsProbabilityMeasure law ∧
    (∀ i, MemLp (coord i) 2 law) ∧
    ¬ (phi =ᵐ[angular] fun _ => 1 / (2 * π)) ∧
    covariance = 1 ∧ covariance.PosDef ∧
    (∃ S : Matrix (Bool × Bool) (Bool × Bool) ℝ,
      S.transpose * omega * S = omega ∧
      covariance = S.transpose * williamsonDiagonal (fun _ => 1) * S) ∧
    (∀ j, uncertainty j = 1) ∧
    Integrable (fun z => jointDensity z * log (jointDensity z)) fullBase ∧
    0 ≤ actionAngleEntropy := by
  exact ⟨law_probability, law_coordinate_memLp, phi_not_ae_uniform,
    covariance_eq_identity, covariance_posDef, williamson_certificate,
    uncertainty_eq_one, joint_log_integrable, actionAngleEntropy_nonneg⟩

end DinovLean.Fourth
