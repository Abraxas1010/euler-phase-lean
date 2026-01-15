import HeytingLean.Analysis.EulerBoundary
import Mathlib.Analysis.Complex.Trigonometric

namespace HeytingLean
namespace Complex

open scoped Real

/-!
# Complex nucleus (unitary rotation)

This module packages the simplest “complexified nucleus” action

`z ↦ e^{iθ} * z`

as a lightweight object `ComplexNucleus`.  It reuses the canonical definition
`HeytingLean.Analysis.eulerBoundary` from `Analysis/EulerBoundary.lean`.

This is *not* the LoF order-theoretic `Reentry.eulerBoundary`; it is the unit-circle
phase used for Fourier/spectral/complex-analysis bridges.
-/

/-- A complex nucleus is parameterized by an angle `θ`. -/
structure ComplexNucleus where
  θ : ℝ

namespace ComplexNucleus

/-- The complex nucleus action: `z ↦ e^{iθ} * z`. -/
noncomputable def action (R : ComplexNucleus) (z : ℂ) : ℂ :=
  HeytingLean.Analysis.eulerBoundary R.θ * z

@[simp] theorem action_zero : (⟨0⟩ : ComplexNucleus).action = id := by
  funext z
  simp [action, HeytingLean.Analysis.eulerBoundary]

theorem action_pi : (⟨Real.pi⟩ : ComplexNucleus).action = fun z => -z := by
  funext z
  have hpi : HeytingLean.Analysis.eulerBoundary Real.pi = (-1 : ℂ) := by
    -- `e^{iπ} = cos π + i sin π = -1 + i·0 = -1`.
    rw [HeytingLean.Analysis.eulerBoundary_expansion]
    simp [Real.cos_pi, Real.sin_pi]
  simp [action, hpi]

theorem action_two_pi : (⟨2 * Real.pi⟩ : ComplexNucleus).action = id := by
  funext z
  -- Use periodicity of the Euler boundary and `e^{i·0} = 1`.
  have hper : Function.Periodic HeytingLean.Analysis.eulerBoundary (2 * Real.pi) :=
    HeytingLean.Analysis.eulerBoundary_periodic
  have h2pi : HeytingLean.Analysis.eulerBoundary (2 * Real.pi) = (1 : ℂ) := by
    -- From `eulerBoundary (0 + 2π) = eulerBoundary 0`.
    have := hper 0
    simpa [HeytingLean.Analysis.eulerBoundary_zero] using this
  simp [action, h2pi]

theorem action_norm (R : ComplexNucleus) (z : ℂ) :
    ‖R.action z‖ = ‖z‖ := by
  simp only [action, Complex.norm_mul, HeytingLean.Analysis.norm_eulerBoundary, one_mul]

theorem action_continuous (R : ComplexNucleus) : Continuous R.action := by
  -- `z ↦ (const) * z`
  simpa [action] using (continuous_const.mul continuous_id)

theorem action_comp (R₁ R₂ : ComplexNucleus) (z : ℂ) :
    R₁.action (R₂.action z) = (⟨R₁.θ + R₂.θ⟩ : ComplexNucleus).action z := by
  simp [action, HeytingLean.Analysis.eulerBoundary_add, mul_assoc]

end ComplexNucleus

/-- The “real nucleus” as the degenerate restriction `θ ∈ {0, π}`. -/
def RealNucleus := { R : ComplexNucleus // R.θ = 0 ∨ R.θ = Real.pi }

end Complex
end HeytingLean

