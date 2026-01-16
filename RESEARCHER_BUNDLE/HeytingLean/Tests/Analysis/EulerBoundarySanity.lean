import HeytingLean.Analysis.EulerBoundary
import HeytingLean.Analysis.EulerComplexGateway
import HeytingLean.Analysis.EulerFourierBridge
import HeytingLean.Analysis.EulerSpectralBridge

namespace HeytingLean
namespace Tests
namespace Analysis

open scoped Real

open HeytingLean.Analysis

example : eulerBoundary 0 = (1 : ℂ) := by
  exact eulerBoundary_zero

example (θ : ℝ) : eulerBoundary θ = Real.cos θ + Complex.I * Real.sin θ := by
  exact eulerBoundary_expansion θ

example (θ : ℝ) : ‖eulerBoundary θ‖ = 1 := by
  exact norm_eulerBoundary θ

example (θ : ℝ) : Isometry (HeytingLean.Analysis.EulerComplex.rotate θ) := by
  exact HeytingLean.Analysis.EulerComplex.rotate_isometry θ

example (n : ℤ) (θ : ℝ) :
    HeytingLean.Analysis.EulerFourier.fourierMode n θ =
      fourier (T := (2 * Real.pi)) n (θ : AddCircle (2 * Real.pi)) := by
  exact HeytingLean.Analysis.EulerFourier.fourierMode_eq_fourier_two_pi n θ

example (v : ℂ) (hv : v ≠ 0) :
    ‖(1 : ℂ)‖ = 1 := by
  -- A tiny smoke test: apply the spectral lemma to the identity isometry.
  exact
    (HeytingLean.Analysis.EulerSpectral.norm_eigenvalue_eq_one_of_linearIsometry
      (A := (LinearIsometry.id : ℂ →ₗᵢ[ℂ] ℂ)) (v := v) hv (μ := (1 : ℂ)) (by simp))

end Analysis
end Tests
end HeytingLean
