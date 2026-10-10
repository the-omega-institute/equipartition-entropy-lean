import DinovLean.Angular4

/-! Realization of the fourth harmonic with exponential actions, actual
integral covariance of its Cartesian pushforward, and a Williamson witness. -/
noncomputable section
open Real MeasureTheory Set Matrix
open scoped ENNReal
namespace DinovLean.Fourth

abbrev action : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
abbrev base : Measure (ℝ × ℝ) := angular.prod action
def density (z : ℝ × ℝ) : ℝ := phi z.1 * exp (-z.2)
def oneLaw : Measure (ℝ × ℝ) := base.withDensity (fun z => ENNReal.ofReal (density z))
def phase (k : Bool) (t : ℝ) : ℝ := if k then cos t else sin t
def Z (k : Bool) (z : ℝ × ℝ) : ℝ := sqrt (2 * z.2) * phase k z.1

theorem phase_mean (k : Bool) : ∫ t, phase k t * phi t ∂angular = 0 := by
  cases k
  · exact sin_mean
  · exact cos_mean

theorem phase_product (k l : Bool) :
    (∫ t, phase k t * phase l t * phi t ∂angular) = if k = l then 1/2 else 0 := by
  cases k <;> cases l <;> simp only [phase, Bool.false_eq_true, ↓reduceIte]
  · simpa only [pow_two] using sin_sq
  · exact sin_cos
  · have he : (fun t => cos t * sin t * phi t) = fun t => sin t * cos t * phi t := by funext t; ring
    rw [he]; exact sin_cos
  · simpa only [pow_two] using cos_sq

@[fun_prop] theorem density_measurable : Measurable density := by unfold density; fun_prop

theorem density_pos (z : ℝ × ℝ) : 0 < density z := mul_pos (phi_pos _) (exp_pos _)

theorem action_mass : ∫ J, exp (-J) ∂action = 1 := integral_exp_neg_Ioi_zero

theorem action_integrable : Integrable (fun J : ℝ => exp (-J)) action := by
  simpa [action, IntegrableOn] using (GammaIntegral_convergent (s := 1) (by norm_num))

theorem action_first_moment : ∫ J, J * exp (-J) ∂action = 1 := by
  have hi := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1) (by norm_num) (by norm_num)
  norm_num at hi; exact hi

theorem action_first_integrable : Integrable (fun J : ℝ => J * exp (-J)) action := by
  have hi := GammaIntegral_convergent (s := 2) (by norm_num)
  norm_num at hi
  simpa [IntegrableOn, action, mul_comm] using hi

theorem density_integrable : Integrable density base :=
  (phi_continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mul_prod action_integrable

theorem density_mass : ∫ z, density z ∂base = 1 := by
  simp only [density]
  rw [integral_prod_mul (f := phi) (g := fun J : ℝ => exp (-J)), phi_mass, action_mass, mul_one]

instance one_probability : IsProbabilityMeasure oneLaw := by
  constructor
  rw [oneLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal density_integrable (ae_of_all _ (fun z => (density_pos z).le)), density_mass]
  norm_num

/-- Exact conditional action marginal at every real action value. -/
theorem action_fiber (J : ℝ) : ∫ t, density (t, J) ∂angular = exp (-J) := by
  simp only [density]
  rw [integral_mul_const, phi_mass, one_mul]

theorem expectation (h : (ℝ × ℝ) → ℝ) :
    (∫ z, h z ∂oneLaw) = ∫ z, h z * density z ∂base := by
  rw [oneLaw, integral_withDensity_eq_integral_toReal_smul density_measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  congr 1; funext z
  rw [ENNReal.toReal_ofReal (density_pos z).le, smul_eq_mul, mul_comm]

theorem coordinate_mean (k : Bool) : ∫ z, Z k z ∂oneLaw = 0 := by
  rw [expectation]
  have he : (fun z => Z k z * density z) = fun z : ℝ × ℝ =>
      (phase k z.1 * phi z.1) * (sqrt (2 * z.2) * exp (-z.2)) := by
    funext z; unfold Z density; ring
  rw [he, integral_prod_mul (f := fun t => phase k t * phi t) (g := fun J : ℝ => sqrt (2 * J) * exp (-J)), phase_mean, zero_mul]

private theorem positive_action_ae : ∀ᵐ z ∂base, 0 < z.2 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability : MeasurableSet {z : ℝ × ℝ | 0 < z.2})).2
  exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Ioi)

theorem coordinate_product_ae (k l : Bool) :
    (fun z => Z k z * Z l z * density z) =ᵐ[base]
    fun z : ℝ × ℝ => (phase k z.1 * phase l z.1 * phi z.1) * (2 * (z.2 * exp (-z.2))) := by
  filter_upwards [positive_action_ae] with z hz
  unfold Z density
  calc
    _ = sqrt (2 * z.2) ^ 2 * (phase k z.1 * phase l z.1 * phi z.1 * exp (-z.2)) := by ring
    _ = _ := by rw [sq_sqrt (by positivity)]; ring

theorem coordinate_product (k l : Bool) :
    (∫ z, Z k z * Z l z ∂oneLaw) = if k = l then 1 else 0 := by
  rw [expectation, integral_congr_ae (coordinate_product_ae k l),
    integral_prod_mul (f := fun t => phase k t * phase l t * phi t) (g := fun J : ℝ => 2 * (J * exp (-J))),
    phase_product, integral_const_mul, action_first_moment]
  split_ifs <;> norm_num

theorem coordinate_square_integrable (k : Bool) :
    Integrable (fun z => Z k z ^ 2 * density z) base := by
  have hc : Continuous (fun t => phase k t * phase k t * phi t) := by
    cases k <;> dsimp [phase] <;> fun_prop
  have hi : Integrable (fun z : ℝ × ℝ =>
      (phase k z.1 * phase k z.1 * phi z.1) * (2 * (z.2 * exp (-z.2)))) base :=
    (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mul_prod
      (action_first_integrable.const_mul 2)
  simpa only [pow_two] using hi.congr (coordinate_product_ae k k).symm

@[fun_prop] theorem Z_measurable (k : Bool) : Measurable (Z k) := by
  cases k <;> unfold Z <;> simp only [phase, Bool.false_eq_true, ↓reduceIte] <;> fun_prop

theorem coordinate_memLp (k : Bool) : MemLp (Z k) 2 oneLaw := by
  apply (memLp_two_iff_integrable_sq (Z_measurable k).aestronglyMeasurable).mpr
  rw [oneLaw, integrable_withDensity_iff density_measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (density_pos _).le]
  simpa only [mul_comm] using coordinate_square_integrable k

theorem one_covariance (k l : Bool) :
    ProbabilityTheory.covariance (Z k) (Z l) oneLaw = if k = l then 1 else 0 := by
  simp only [ProbabilityTheory.covariance, coordinate_mean, sub_zero]
  exact coordinate_product k l

abbrev TorusTwo := (ℝ × ℝ) × (ℝ × ℝ)
abbrev CartesianTwo := (ℝ × ℝ) × (ℝ × ℝ)
def torusLaw : Measure TorusTwo := oneLaw.prod oneLaw
def Y (i : Bool × Bool) (z : TorusTwo) : ℝ := Z i.2 (if i.1 then z.2 else z.1)
def Psi (z : ℝ × ℝ) : ℝ × ℝ := (Z false z, Z true z)
def Psi2 : TorusTwo → CartesianTwo := Prod.map Psi Psi
def law : Measure CartesianTwo := Measure.map Psi2 torusLaw
def coord (i : Bool × Bool) (x : CartesianTwo) : ℝ :=
  if i.2 then (if i.1 then x.2 else x.1).2 else (if i.1 then x.2 else x.1).1
/-- Actual covariance using Mathlib's integral definition. -/
def covariance : Matrix (Bool × Bool) (Bool × Bool) ℝ :=
  fun i k => ProbabilityTheory.covariance (coord i) (coord k) law

@[fun_prop] theorem Psi2_measurable : Measurable Psi2 := by unfold Psi2 Psi; fun_prop
instance torus_probability : IsProbabilityMeasure torusLaw := by unfold torusLaw; infer_instance
instance law_probability : IsProbabilityMeasure law := Measure.isProbabilityMeasure_map Psi2_measurable.aemeasurable

theorem coord_comp (i : Bool × Bool) : coord i ∘ Psi2 = Y i := by
  rcases i with ⟨j, k⟩; cases j <;> cases k <;> rfl

theorem law_coordinate_memLp (i : Bool × Bool) : MemLp (coord i) 2 law := by
  have hm : Measurable (coord i) := by rcases i with ⟨j,k⟩; cases j <;> cases k <;> unfold coord <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  apply (memLp_map_measure_iff hm.aestronglyMeasurable Psi2_measurable.aemeasurable).mpr
  rw [coord_comp]
  rcases i with ⟨j, k⟩
  cases j
  · exact (coordinate_memLp k).comp_fst oneLaw
  · exact (coordinate_memLp k).comp_snd oneLaw

private theorem cov_fst (k l : Bool) :
    ProbabilityTheory.covariance (Y (false,k)) (Y (false,l)) torusLaw = if k = l then 1 else 0 := by
  simp only [Y, Bool.false_eq_true, ↓reduceIte, torusLaw, ProbabilityTheory.covariance,
    integral_fun_fst, probReal_univ, one_smul, coordinate_mean, sub_zero]
  rw [integral_fun_fst (fun z => Z k z * Z l z), probReal_univ, one_smul]
  exact coordinate_product k l

private theorem cov_snd (k l : Bool) :
    ProbabilityTheory.covariance (Y (true,k)) (Y (true,l)) torusLaw = if k = l then 1 else 0 := by
  simp only [Y, ↓reduceIte, torusLaw, ProbabilityTheory.covariance,
    integral_fun_snd, probReal_univ, one_smul, coordinate_mean, sub_zero]
  rw [integral_fun_snd (fun z => Z k z * Z l z), probReal_univ, one_smul]
  exact coordinate_product k l

private theorem cov_cross (k l : Bool) :
    ProbabilityTheory.covariance (Y (false,k)) (Y (true,l)) torusLaw = 0 :=
  ProbabilityTheory.covariance_fst_snd_prod (coordinate_memLp k) (coordinate_memLp l)

/-- The nonuniform fourth-harmonic density has actual Cartesian covariance I₄. -/
theorem covariance_eq_identity : covariance = 1 := by
  ext ⟨j,k⟩ ⟨l,m⟩
  have hmap : covariance (j,k) (l,m) = ProbabilityTheory.covariance (Y (j,k)) (Y (l,m)) torusLaw := by
    unfold covariance law
    rw [ProbabilityTheory.covariance_map
      (law_coordinate_memLp (j,k)).aestronglyMeasurable
      (law_coordinate_memLp (l,m)).aestronglyMeasurable Psi2_measurable.aemeasurable,
      coord_comp, coord_comp]
  rw [hmap]
  cases j <;> cases l <;> cases k <;> cases m <;> simp only [Matrix.one_apply, Prod.mk.injEq, and_self, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals first
    | exact cov_fst _ _
    | exact cov_snd _ _
    | exact cov_cross _ _
    | exact (ProbabilityTheory.covariance_comm _ _).trans (cov_cross _ _)

theorem covariance_posDef : covariance.PosDef := by rw [covariance_eq_identity]; exact Matrix.PosDef.one

def uncertainty (j : Bool) : ℝ := sqrt (Matrix.det !![
  covariance (j,false) (j,false), covariance (j,false) (j,true);
  covariance (j,true) (j,false), covariance (j,true) (j,true)])

theorem uncertainty_eq_one (j : Bool) : uncertainty j = 1 := by
  simp [uncertainty, covariance_eq_identity, Matrix.det_fin_two]

/-- Interleaved (q₁,p₁,q₂,p₂) symplectic form. -/
def omega : Matrix (Bool × Bool) (Bool × Bool) ℝ := fun i k =>
  if i.1 = k.1 then (if i.2 = k.2 then 0 else if i.2 then -1 else 1) else 0

/-- Williamson diagonal with each frequency repeated on its q,p pair. -/
def williamsonDiagonal (ν : Bool → ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℝ :=
  Matrix.diagonal (fun i => ν i.1)

/-- An explicit symplectic factorization certifying frequencies (1,1). -/
theorem williamson_certificate :
    ∃ S : Matrix (Bool × Bool) (Bool × Bool) ℝ,
      S.transpose * omega * S = omega ∧
      covariance = S.transpose * williamsonDiagonal (fun _ => 1) * S := by
  refine ⟨1, ?_, ?_⟩
  · simp
  · simpa [williamsonDiagonal, Matrix.diagonal_one] using covariance_eq_identity

/-- Exact saturation of uⱼ ≥ νmin, for the certified spectrum (1,1). -/
theorem problem317b_saturated (j : Bool) : uncertainty j = min (1 : ℝ) 1 := by
  simpa using uncertainty_eq_one j

end DinovLean.Fourth
