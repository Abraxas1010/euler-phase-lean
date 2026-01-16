import HeytingLean.Analysis.EulerBoundary
import Mathlib.Analysis.Fourier.AddCircle

namespace HeytingLean
namespace Analysis

open scoped Real
open scoped BigOperators

open MeasureTheory

/-!
# Euler boundary ↔ Fourier (Mathlib bridge)

`WIP/euler_boundary.md` informally identifies Fourier modes as iterates of the unit-circle phase
map `θ ↦ e^{iθ}`.  Mathlib formalizes Fourier analysis on the additive circle `AddCircle T` with
monomials

`fourier n : AddCircle T → ℂ,  x ↦ exp (2π i n x / T)`.

This module provides a small bridge: for `T = 2π`, these monomials coincide with
`θ ↦ e^{i(n•θ)}` on `ℝ`.
-/

namespace EulerFourier

/-- Fourier mode as “Euler boundary iteration”: `θ ↦ e^{i(n•θ)}`. -/
noncomputable def fourierMode (n : ℤ) (θ : ℝ) : ℂ :=
  eulerBoundary ((n : ℝ) * θ)

lemma fourierMode_def (n : ℤ) (θ : ℝ) : fourierMode n θ = eulerBoundary ((n : ℝ) * θ) := rfl

lemma fourierMode_eq_fourier_two_pi (n : ℤ) (θ : ℝ) :
    fourierMode n θ =
      fourier (T := (2 * Real.pi)) n (θ : AddCircle (2 * Real.pi)) := by
  -- Expand both sides to `Complex.exp` and cancel the `(2π)/(2π)` factor.
  unfold fourierMode
  unfold eulerBoundary
  have h2pi0c : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (by exact_mod_cast Real.pi_ne_zero)
  have hcast : (((n : ℝ) * θ : ℝ) : ℂ) = (n : ℂ) * (θ : ℂ) := by
    simp [Complex.ofReal_mul]
  have hexp :
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (θ : ℂ) / (2 * (Real.pi : ℂ))) =
        Complex.I * ((n : ℂ) * (θ : ℂ)) := by
    -- Rewrite the numerator as `(2π) * (I * (n*θ))` and cancel.
    have hn :
        (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (θ : ℂ)) =
          (2 * (Real.pi : ℂ)) * (Complex.I * ((n : ℂ) * (θ : ℂ))) := by
      simp [mul_assoc, mul_left_comm, mul_comm]
    calc
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (θ : ℂ) / (2 * (Real.pi : ℂ)))
          = ((2 * (Real.pi : ℂ)) * (Complex.I * ((n : ℂ) * (θ : ℂ)))) / (2 * (Real.pi : ℂ)) := by
              simp [hn]
      _ = Complex.I * ((n : ℂ) * (θ : ℂ)) := by
              simpa [mul_assoc] using
                (mul_div_cancel_left₀ (Complex.I * ((n : ℂ) * (θ : ℂ))) h2pi0c)
  -- Now use Mathlib's closed form for the Fourier monomial on `AddCircle`.
  have hfourier :
      fourier (T := (2 * Real.pi)) n (θ : AddCircle (2 * Real.pi)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (θ : ℂ) / (2 * (Real.pi : ℂ))) := by
    -- `fourier_coe_apply` uses `↑(2*π)`; rewrite it into `2 * (π:ℂ)` for cancellation.
    simp [Complex.ofReal_mul, mul_left_comm, mul_comm]
  -- Rewrite the RHS via `hfourier`, then simplify exponents to match.
  -- (All algebra happens inside the exponent; we never unfold `exp` itself.)
  rw [hfourier]
  -- Now both sides are exponentials with definally equal exponents.
  simp [hcast, hexp]

/-- Re-export: Fourier series sums to `f` in `L²(AddCircle (2π))`. -/
theorem hasSum_fourier_series_L2_two_pi :
    let hT : Fact (0 < (2 * Real.pi)) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
    ∀ f : MeasureTheory.Lp ℂ 2 (@AddCircle.haarAddCircle (2 * Real.pi) hT),
      HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f := by
  intro hT f
  classical
  haveI : Fact (0 < (2 * Real.pi)) := hT
  -- `hasSum_fourier_series_L2` is Mathlib's core completeness statement.
  simpa using (hasSum_fourier_series_L2 (T := (2 * Real.pi)) f)

end EulerFourier

end Analysis
end HeytingLean
