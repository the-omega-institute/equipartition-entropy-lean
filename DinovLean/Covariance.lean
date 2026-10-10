import DinovLean.Gibbs
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The real 2 by 2 covariance bound and exact equality conditions. -/
noncomputable section
open Real Matrix
namespace DinovLean

def block (vq vp c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![vq, c; c, vp]

theorem block_det (vq vp c : ℝ) : (block vq vp c).det = vq * vp - c ^ 2 := by
  simp [block, Matrix.det_fin_two, pow_two]

theorem block_trace_gap (vq vp c : ℝ) :
    (vq + vp) ^ 2 - 4 * (block vq vp c).det = (vq - vp) ^ 2 + 4 * c ^ 2 := by
  rw [block_det]; ring

/-- For nonnegative diagonal entries, the covariance area is at most half the trace.
The determinant hypothesis makes equality nondegenerate and is explicit. -/
theorem covariance_trace_bound {vq vp c : ℝ} (hq : 0 ≤ vq) (hp : 0 ≤ vp)
    (hd : 0 ≤ (block vq vp c).det) :
    sqrt (block vq vp c).det ≤ (vq + vp) / 2 := by
  have hgap := block_trace_gap vq vp c
  have hs := sq_sqrt hd
  have hn := sqrt_nonneg (block vq vp c).det
  nlinarith [sq_nonneg (vq - vp), sq_nonneg c]

theorem covariance_trace_eq_iff {vq vp c : ℝ} (hq : 0 ≤ vq) (hp : 0 ≤ vp)
    (hd : 0 ≤ (block vq vp c).det) :
    sqrt (block vq vp c).det = (vq + vp) / 2 ↔ vq = vp ∧ c = 0 := by
  constructor
  · intro he
    have hs := sq_sqrt hd
    have hgap := block_trace_gap vq vp c
    constructor <;> nlinarith [sq_nonneg (vq - vp), sq_nonneg c]
  · rintro ⟨rfl, rfl⟩
    rw [block_det]
    simp only [sq, mul_zero, sub_zero, sqrt_mul_self hq]
    ring

/-- Raw energy η, with the squared mean subtracted from the covariance trace. -/
theorem covariance_energy_bound {vq vp c η μq μp : ℝ}
    (hq : 0 ≤ vq) (hp : 0 ≤ vp) (hd : 0 ≤ (block vq vp c).det)
    (htrace : vq + vp = 2 * η - (μq ^ 2 + μp ^ 2)) :
    sqrt (block vq vp c).det ≤ η := by
  have h := covariance_trace_bound hq hp hd
  nlinarith [sq_nonneg μq, sq_nonneg μp]

theorem covariance_energy_eq_iff {vq vp c η μq μp : ℝ}
    (hq : 0 ≤ vq) (hp : 0 ≤ vp) (hd : 0 ≤ (block vq vp c).det)
    (htrace : vq + vp = 2 * η - (μq ^ 2 + μp ^ 2)) :
    sqrt (block vq vp c).det = η ↔ μq = 0 ∧ μp = 0 ∧ vq = η ∧ vp = η ∧ c = 0 := by
  constructor
  · intro he
    have hb := covariance_trace_bound hq hp hd
    have hmeans : μq = 0 ∧ μp = 0 := by
      constructor <;> nlinarith [sq_nonneg μq, sq_nonneg μp]
    obtain ⟨hmq, hmp⟩ := hmeans
    have ht : sqrt (block vq vp c).det = (vq + vp) / 2 := by
      rw [hmq, hmp] at htrace; simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, sub_zero] at htrace
      linarith
    obtain ⟨hv, hc⟩ := (covariance_trace_eq_iff hq hp hd).mp ht
    exact ⟨hmq, hmp, by linarith, by linarith, hc⟩
  · rintro ⟨rfl, rfl, hqη, hpη, rfl⟩
    rw [hqη, hpη, block_det]
    have hη : 0 ≤ η := hqη ▸ hq
    simpa [pow_two] using sqrt_mul_self hη

/-- Determinant of the actual centered moment block once its moment bridge is supplied. -/
theorem second_harmonic_block_det (x y : ℝ) :
    (block (1 - x) (1 + x) y).det = 1 - (x ^ 2 + y ^ 2) := by
  rw [block_det]; ring

end DinovLean
