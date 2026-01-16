import HeytingLean.Analysis.EulerBoundary
import Mathlib.Analysis.Normed.Operator.LinearIsometry

namespace HeytingLean
namespace Analysis

/-!
# Euler boundary ↔ spectral “phase” lemma

`WIP/euler_boundary.md` connects eigen-relations `A v = λ • v` to “phase fixed points”.

As stated there, this is *not* correct for arbitrary operators: to conclude `‖λ‖ = 1`, one needs
`A` to preserve norms (e.g. be unitary/isometric).

This module provides the basic, correct lemma for a complex linear isometry.
-/

namespace EulerSpectral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If `A` is a complex linear isometry and `A v = λ • v` for a nonzero `v`, then `‖λ‖ = 1`. -/
theorem norm_eigenvalue_eq_one_of_linearIsometry
    (A : E →ₗᵢ[ℂ] E) {v : E} (hv : v ≠ 0) {μ : ℂ} (hAv : A v = μ • v) :
    ‖μ‖ = 1 := by
  have hvnorm : ‖v‖ ≠ 0 := by
    simpa [norm_eq_zero] using hv
  have h :
      ‖v‖ = ‖μ‖ * ‖v‖ := by
    calc
      ‖v‖ = ‖A v‖ := by
        simp
      _ = ‖μ • v‖ := by
        simp [hAv]
      _ = ‖μ‖ * ‖v‖ := by
        simp [norm_smul]
  -- Cancel `‖v‖` (nonzero) from the right.
  have : (1 : ℝ) = ‖μ‖ := by
    apply mul_right_cancel₀ hvnorm
    simpa [one_mul] using h
  simpa using this.symm

end EulerSpectral

end Analysis
end HeytingLean
