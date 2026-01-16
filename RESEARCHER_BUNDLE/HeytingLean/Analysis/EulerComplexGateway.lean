import HeytingLean.Analysis.EulerBoundary
import Mathlib.Analysis.Complex.CauchyIntegral

namespace HeytingLean
namespace Analysis

open scoped Real

/-!
# Euler boundary → complex analysis gateway

This file is intentionally small:

- defines the canonical “Euler rotation” `z ↦ e^{iθ} * z`,
- proves basic analytic/topological facts (continuity, isometry), and
- imports Mathlib's complex-analysis gateway (`CauchyIntegral`) so downstream modules can
  build on it without guessing import locations.

It does **not** claim “holomorphic iff commutes with Euler rotation”; such a statement is not
standard and should be treated as a staged interface if desired.
-/

namespace EulerComplex

/-- Euler rotation of the complex plane by angle `θ`. -/
noncomputable def rotate (θ : ℝ) (z : ℂ) : ℂ :=
  eulerBoundary θ * z

@[simp] lemma rotate_def (θ : ℝ) (z : ℂ) : rotate θ z = eulerBoundary θ * z := rfl

lemma rotate_continuous (θ : ℝ) : Continuous (rotate θ) := by
  simpa [rotate] using (continuous_const.mul continuous_id)

lemma rotate_isometry (θ : ℝ) : Isometry (rotate θ) := by
  -- Work with `dist` (not `edist`) for stability under simp.
  refine Isometry.of_dist_eq ?_
  intro z w
  -- `dist (a*z) (a*w) = ‖a‖ * dist z w`; here `‖a‖ = 1`.
  -- Convert to norms and use multiplicativity.
  simp [rotate, dist_eq_norm]
  calc
    ‖eulerBoundary θ * z - eulerBoundary θ * w‖
        = ‖eulerBoundary θ * (z - w)‖ := by
            simp [mul_sub]
    _ = ‖eulerBoundary θ‖ * ‖z - w‖ := by
            simp
    _ = ‖z - w‖ := by
            simp [norm_eulerBoundary]

lemma rotate_norm (θ : ℝ) (z : ℂ) : ‖rotate θ z‖ = ‖z‖ := by
  -- Directly: multiplication by a unit-norm scalar preserves norm.
  simp [rotate, norm_eulerBoundary]

end EulerComplex

end Analysis
end HeytingLean
