import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Finite relative entropy, explicit exponential tilting, and the algebraic
Gibbs gap used in the centered second-harmonic variational principle.
No assertion here identifies finite sums with the continuous conditional laws. -/
noncomputable section
open Real Finset
namespace DinovLean

/-- Unnormalized scalar KL summand, including p = 0. -/
def klTerm (p q : ℝ) : ℝ := p * log (p / q) - p + q

theorem klTerm_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    0 ≤ klTerm p q := by
  have h := mul_nonneg hq.le (InformationTheory.klFun_nonneg (div_nonneg hp hq.le))
  have he : klTerm p q = q * InformationTheory.klFun (p / q) := by
    dsimp [klTerm, InformationTheory.klFun]
    field_simp
    ring
  rw [he]
  exact h

theorem klTerm_eq_zero_iff {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    klTerm p q = 0 ↔ p = q := by
  have he : klTerm p q = q * InformationTheory.klFun (p / q) := by
    dsimp [klTerm, InformationTheory.klFun]
    field_simp
    ring
  rw [he, mul_eq_zero, or_iff_right hq.ne',
    InformationTheory.klFun_eq_zero_iff (div_nonneg hp hq.le), div_eq_one_iff_eq hq.ne']

/-- Finite KL against a strictly positive reference; log at zero is harmless. -/
def finiteKL {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * log (p i / q i)

theorem finiteKL_eq_sum_klTerm {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) :
    finiteKL p q = ∑ i, klTerm (p i) (q i) := by
  simp only [klTerm, sum_add_distrib, sum_sub_distrib, hp, hq, finiteKL]
  ring

theorem finiteKL_nonneg {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 < q i)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) : 0 ≤ finiteKL p q := by
  rw [finiteKL_eq_sum_klTerm hp hq]
  exact sum_nonneg fun i _ => klTerm_nonneg (hp0 i) (hq0 i)

theorem finiteKL_eq_zero_iff {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 < q i)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) :
    finiteKL p q = 0 ↔ p = q := by
  rw [finiteKL_eq_sum_klTerm hp hq,
    sum_eq_zero_iff_of_nonneg (fun i _ => klTerm_nonneg (hp0 i) (hq0 i))]
  constructor
  · intro h
    funext i
    exact (klTerm_eq_zero_iff (hp0 i) (hq0 i)).mp (h i (mem_univ i))
  · intro h i _
    exact (klTerm_eq_zero_iff (hp0 i) (hq0 i)).mpr (congrFun h i)

/-- A finite reference law tilted by an arbitrary real statistic.
For the second harmonic set T_i = J_i cos(2(θ_i-α)). -/
def partition {ι : Type*} [Fintype ι] (r T : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, r i * exp (lam * T i)

def gibbs {ι : Type*} [Fintype ι] (r T : ι → ℝ) (lam : ℝ) (i : ι) : ℝ :=
  r i * exp (lam * T i) / partition r T lam

theorem partition_pos {ι : Type*} [Fintype ι] [Nonempty ι] {r T : ι → ℝ}
    (hr : ∀ i, 0 < r i) (lam : ℝ) : 0 < partition r T lam := by
  exact sum_pos (fun i _ => mul_pos (hr i) (exp_pos _)) univ_nonempty

theorem gibbs_pos {ι : Type*} [Fintype ι] [Nonempty ι] {r T : ι → ℝ}
    (hr : ∀ i, 0 < r i) (lam : ℝ) (i : ι) : 0 < gibbs r T lam i :=
  div_pos (mul_pos (hr i) (exp_pos _)) (partition_pos hr lam)

theorem gibbs_sum {ι : Type*} [Fintype ι] [Nonempty ι] {r T : ι → ℝ}
    (hr : ∀ i, 0 < r i) (lam : ℝ) : ∑ i, gibbs r T lam i = 1 := by
  simp only [gibbs, ← sum_div]
  change partition r T lam / partition r T lam = 1
  exact div_self (partition_pos hr lam).ne'

theorem gibbs_log_ratio {ι : Type*} [Fintype ι] [Nonempty ι] {r T : ι → ℝ}
    (hr : ∀ i, 0 < r i) (lam : ℝ) (i : ι) :
    log (gibbs r T lam i / r i) = lam * T i - log (partition r T lam) := by
  have hrat : gibbs r T lam i / r i = exp (lam * T i) / partition r T lam := by
    dsimp [gibbs]
    field_simp [(hr i).ne', (partition_pos hr lam).ne']
  rw [hrat, log_div (exp_pos _).ne' (partition_pos hr lam).ne', log_exp]

/-- Exact finite Gibbs identity, allowing zero candidate probabilities. -/
theorem finite_gibbs_identity {ι : Type*} [Fintype ι] [Nonempty ι]
    {p r T : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 < r i)
    (hp : ∑ i, p i = 1) (lam : ℝ) :
    finiteKL p (gibbs r T lam) =
      finiteKL p r - lam * (∑ i, p i * T i) + log (partition r T lam) := by
  have ht (i : ι) : p i * log (p i / gibbs r T lam i) =
      p i * log (p i / r i) - lam * (p i * T i) + p i * log (partition r T lam) := by
    by_cases hzero : p i = 0
    · simp [hzero]
    · have hpos : 0 < p i := lt_of_le_of_ne (hp0 i) (Ne.symm hzero)
      have hlog := gibbs_log_ratio (T := T) hr lam i
      rw [log_div hpos.ne' (gibbs_pos hr lam i).ne', log_div hpos.ne' (hr i).ne']
      rw [log_div (gibbs_pos hr lam i).ne' (hr i).ne'] at hlog
      nlinarith
  simp only [finiteKL, ht, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hp]
  ring

theorem finite_gibbs_inequality {ι : Type*} [Fintype ι] [Nonempty ι]
    {p r T : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 < r i)
    (hp : ∑ i, p i = 1) (lam : ℝ) :
    lam * (∑ i, p i * T i) - log (partition r T lam) ≤ finiteKL p r := by
  have h := finiteKL_nonneg hp0 (gibbs_pos (T := T) hr lam) hp (gibbs_sum (T := T) hr lam)
  rw [finite_gibbs_identity hp0 hr hp lam] at h
  linarith

theorem finite_gibbs_equality_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    {p r T : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 < r i)
    (hp : ∑ i, p i = 1) (lam : ℝ) :
    finiteKL p r = lam * (∑ i, p i * T i) - log (partition r T lam) ↔
      p = gibbs r T lam := by
  have h := finiteKL_eq_zero_iff hp0 (gibbs_pos (T := T) hr lam) hp (gibbs_sum (T := T) hr lam)
  rw [finite_gibbs_identity hp0 hr hp lam] at h
  constructor
  · intro he; apply h.mp; linarith
  · intro he; have := h.mpr he; linarith

/-- Finite conditional model: every action fiber has its own normalizer,
so exponential tilting preserves the supplied action weights. -/
theorem conditional_gibbs_identity {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    {p r T : κ → ι → ℝ} {w : κ → ℝ}
    (hp0 : ∀ j i, 0 ≤ p j i) (hr : ∀ j i, 0 < r j i)
    (hp : ∀ j, ∑ i, p j i = 1) (lam : ℝ) :
    (∑ j, w j * finiteKL (p j) (gibbs (r j) (T j) lam)) =
      (∑ j, w j * finiteKL (p j) (r j)) -
      lam * (∑ j, w j * (∑ i, p j i * T j i)) +
      (∑ j, w j * log (partition (r j) (T j) lam)) := by
  simp_rw [finite_gibbs_identity (hp0 _) (hr _) (hp _), mul_add, mul_sub]
  simp only [sum_add_distrib, sum_sub_distrib]
  congr 2
  rw [mul_sum]
  apply sum_congr rfl
  intro j _; ring

theorem conditional_gibbs_nonneg {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    {p r T : κ → ι → ℝ} {w : κ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hp0 : ∀ j i, 0 ≤ p j i) (hr : ∀ j i, 0 < r j i)
    (hp : ∀ j, ∑ i, p j i = 1) (lam : ℝ) :
    0 ≤ ∑ j, w j * finiteKL (p j) (gibbs (r j) (T j) lam) := by
  apply sum_nonneg
  intro j _
  exact mul_nonneg (hw j) (finiteKL_nonneg (hp0 j) (gibbs_pos (T := T j) (hr j) lam)
    (hp j) (gibbs_sum (T := T j) (hr j) lam))

theorem conditional_gibbs_eq_zero_iff {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    {p r T : κ → ι → ℝ} {w : κ → ℝ}
    (hw : ∀ j, 0 < w j) (hp0 : ∀ j i, 0 ≤ p j i) (hr : ∀ j i, 0 < r j i)
    (hp : ∀ j, ∑ i, p j i = 1) (lam : ℝ) :
    (∑ j, w j * finiteKL (p j) (gibbs (r j) (T j) lam)) = 0 ↔
      ∀ j, p j = gibbs (r j) (T j) lam := by
  have hn (j : κ) : 0 ≤ finiteKL (p j) (gibbs (r j) (T j) lam) :=
    finiteKL_nonneg (hp0 j) (gibbs_pos (T := T j) (hr j) lam) (hp j)
      (gibbs_sum (T := T j) (hr j) lam)
  rw [sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hw j).le (hn j))]
  constructor
  · intro h j
    have hz := (mul_eq_zero.mp (h j (mem_univ j))).resolve_left (hw j).ne'
    exact (finiteKL_eq_zero_iff (hp0 j) (gibbs_pos (T := T j) (hr j) lam) (hp j)
      (gibbs_sum (T := T j) (hr j) lam)).mp hz
  · intro h j _
    have hz := (finiteKL_eq_zero_iff (hp0 j) (gibbs_pos (T := T j) (hr j) lam) (hp j)
      (gibbs_sum (T := T j) (hr j) lam)).mpr (h j)
    rw [hz, mul_zero]

/-- The explicit action-weighted second harmonic. -/
def secondStatistic {κ ι : Type*} (J : κ → ℝ) (θ : ι → ℝ) (α : ℝ) (j : κ) (i : ι) : ℝ :=
  J j * cos (2 * (θ i - α))

/-- The exact scalar gap after the analytic identities have been supplied. -/
theorem gibbs_gap_identity {lam a m K C b D : ℝ}
    (hD : D = K - lam * a + b) (hC : C = lam * m - b) :
    lam * (m - a) = (C - K) + D := by linarith

theorem gibbs_gap_bound {lam a m K C b D : ℝ}
    (hlam : 0 < lam) (hD0 : 0 ≤ D) (hKC : K ≤ C)
    (hD : D = K - lam * a + b) (hC : C = lam * m - b) : a ≤ m := by
  have := gibbs_gap_identity hD hC
  nlinarith

theorem gibbs_gap_eq_iff {lam a m K C b D : ℝ}
    (hlam : 0 < lam) (hD0 : 0 ≤ D) (hKC : K ≤ C)
    (hD : D = K - lam * a + b) (hC : C = lam * m - b) :
    a = m ↔ K = C ∧ D = 0 := by
  have h := gibbs_gap_identity hD hC
  constructor
  · intro ham; constructor <;> nlinarith
  · rintro ⟨hK, hzero⟩; nlinarith

def area (a : ℝ) : ℝ := sqrt (1 - a ^ 2)

theorem area_antitone {a m : ℝ} (ha : 0 ≤ a) (ham : a ≤ m) :
    area m ≤ area a := by
  apply sqrt_le_sqrt
  nlinarith

theorem area_eq_iff {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m)
    (ha1 : a ≤ 1) (hm1 : m ≤ 1) : area a = area m ↔ a = m := by
  have hsa : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hsm : 0 ≤ 1 - m ^ 2 := by nlinarith
  constructor
  · intro h
    have hs : (area a) ^ 2 = (area m) ^ 2 := congrArg (fun x : ℝ => x ^ 2) h
    dsimp [area] at hs
    rw [sq_sqrt hsa, sq_sqrt hsm] at hs
    nlinarith
  · intro h; rw [h]

/-- Lower bound and all scalar equality conditions; density equality is a separate bridge. -/
theorem centered_lower_bound {lam a m K C b D : ℝ}
    (hlam : 0 < lam) (ha : 0 ≤ a) (hm : 0 ≤ m) (ha1 : a ≤ 1) (hm1 : m ≤ 1)
    (hD0 : 0 ≤ D) (hKC : K ≤ C)
    (hD : D = K - lam * a + b) (hC : C = lam * m - b) :
    area m ≤ area a ∧ (area a = area m ↔ K = C ∧ D = 0) := by
  exact ⟨area_antitone ha (gibbs_gap_bound hlam hD0 hKC hD hC),
    (area_eq_iff ha hm ha1 hm1).trans (gibbs_gap_eq_iff hlam hD0 hKC hD hC)⟩

theorem entropy_gap_identity {lam a m K C b D S s Smax : ℝ}
    (hD : D = K - lam * a + b) (hC : C = lam * m - b)
    (hS : S = Smax - 2 * K) (hs : s = Smax - 2 * C) :
    lam * (m - a) = (S - s) / 2 + D := by linarith

end DinovLean
