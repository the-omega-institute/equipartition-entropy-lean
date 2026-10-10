import DinovLean.FourthHarmonic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-! Conditional analytic certificate: derivative identities imply strictly
increasing cost and a monotone inverse. No Bessel differentiation or infinite
range assertion is silently assumed to have been proved. -/
noncomputable section
open Set Real
namespace DinovLean

def cost (b m : ℝ → ℝ) (x : ℝ) : ℝ := x * m x - b x

theorem cost_hasDerivAt {b m : ℝ → ℝ} {x v : ℝ}
    (hb : HasDerivAt b (m x) x) (hm : HasDerivAt m v x) :
    HasDerivAt (cost b m) (x * v) x := by
  have h := ((hasDerivAt_id x).mul hm).sub hb
  change HasDerivAt (cost b m) (1 * m x + x * v - m x) x at h
  simpa using h

/-- Includes the endpoint x = 0, at which the derivative may be zero. -/
theorem cost_strictMonoOn {b m v : ℝ → ℝ}
    (hc : ContinuousOn (cost b m) (Ici 0))
    (hb : ∀ x, 0 < x → HasDerivAt b (m x) x)
    (hm : ∀ x, 0 < x → HasDerivAt m (v x) x)
    (hv : ∀ x, 0 < x → 0 < v x) : StrictMonoOn (cost b m) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hc
  intro x hx
  rw [interior_Ici] at hx
  rw [(cost_hasDerivAt (hb x hx) (hm x hx)).deriv]
  exact mul_pos hx (hv x hx)

theorem cost_inverse_unique {c : ℝ → ℝ} (hc : StrictMonoOn c (Ici 0))
    {x y K : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hcx : c x = K) (hcy : c y = K) :
    x = y := hc.injOn hx hy (hcx.trans hcy.symm)

/-- Any right inverse in the nonnegative half-line is strictly increasing. -/
theorem cost_inverse_strictMonoOn {c L : ℝ → ℝ}
    (hc : StrictMonoOn c (Ici 0))
    (hL : ∀ K, 0 ≤ K → 0 ≤ L K) (hinv : ∀ K, 0 ≤ K → c (L K) = K) :
    StrictMonoOn L (Ici 0) := by
  intro K hK H hH hKH
  by_contra h
  have hle : L H ≤ L K := le_of_not_gt h
  have := hc.monotoneOn (hL H hH) (hL K hK) hle
  rw [hinv H hH, hinv K hK] at this
  linarith

/-- Existence and uniqueness from continuity, strict increase, and an explicit
unboundedness hypothesis. The continuous second-harmonic cost's unboundedness
is not proved in this project. -/
theorem cost_inverse_existsUnique {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Ici 0)) (hmono : StrictMonoOn c (Ici 0))
    (hc0 : c 0 = 0) (hrange : ∀ K, 0 ≤ K → ∃ B, 0 ≤ B ∧ K ≤ c B)
    {K : ℝ} (hK : 0 ≤ K) : ∃! x, 0 ≤ x ∧ c x = K := by
  obtain ⟨B, hB, hKB⟩ := hrange K hK
  have hi := intermediate_value_Icc hB (hcont.mono (by intro x hx; exact hx.1))
  obtain ⟨x, hx, hcx⟩ := hi (show K ∈ Icc (c 0) (c B) by rw [hc0]; exact ⟨hK, hKB⟩)
  refine ⟨x, ⟨hx.1, hcx⟩, ?_⟩
  intro y hy
  exact cost_inverse_unique hmono hy.1 hx.1 hy.2 hcx

/-- Raising the entropy floor decreases its concentration parameter. -/
theorem floor_parameter_antitone {c L : ℝ → ℝ} {Smax : ℝ}
    (hc : StrictMonoOn c (Ici 0))
    (hL : ∀ K, 0 ≤ K → 0 ≤ L K) (hinv : ∀ K, 0 ≤ K → c (L K) = K) :
    AntitoneOn (fun s => L ((Smax - s) / 2)) (Iic Smax) := by
  intro s hs t ht hst
  change s ≤ Smax at hs
  change t ≤ Smax at ht
  exact (cost_inverse_strictMonoOn hc hL hinv).monotoneOn
    (by change 0 ≤ (Smax - t) / 2; linarith) (by change 0 ≤ (Smax - s) / 2; linarith) (by linarith)

/-- The envelope is monotone under the supplied analytic moment monotonicity. -/
theorem lower_envelope_monotone {c L m : ℝ → ℝ} {Smax : ℝ}
    (hc : StrictMonoOn c (Ici 0))
    (hL : ∀ K, 0 ≤ K → 0 ≤ L K) (hinv : ∀ K, 0 ≤ K → c (L K) = K)
    (hm : MonotoneOn m (Ici 0)) (hm0 : ∀ x, 0 ≤ x → 0 ≤ m x) :
    MonotoneOn (fun s => area (m (L ((Smax - s) / 2)))) (Iic Smax) := by
  intro s hs t ht hst
  change s ≤ Smax at hs
  change t ≤ Smax at ht
  have hKs : 0 ≤ (Smax - s) / 2 := by linarith
  have hKt : 0 ≤ (Smax - t) / 2 := by linarith
  have hp := floor_parameter_antitone hc hL hinv hs ht hst
  exact area_antitone (hm0 _ (hL _ hKt)) (hm (hL _ hKt) (hL _ hKs) hp)

end DinovLean
