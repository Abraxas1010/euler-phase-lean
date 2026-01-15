import HeytingLean.Analysis.EulerBoundary
import Mathlib.Analysis.Fourier.AddCircle

namespace HeytingLean
namespace Analysis

open scoped Real

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
  eulerBoundary (n • θ)

lemma fourierMode_def (n : ℤ) (θ : ℝ) : fourierMode n θ = eulerBoundary (n • θ) := rfl

lemma fourierMode_eq_fourier_two_pi (n : ℤ) (θ : ℝ) :
    fourierMode n θ =
      fourier (T := (2 * Real.pi)) n (θ : AddCircle (2 * Real.pi)) := by
  -- Expand both sides to `Complex.exp` and simplify the `(2π)/(2π)` factor.
  unfold fourierMode
  unfold eulerBoundary
  have h2pi0 : (2 * Real.pi : ℝ) ≠ 0 := by
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    nlinarith
  have h2pi0c : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast h2pi0
  -- Use Mathlib's closed form for the Fourier monomials on `AddCircle`.
  -- `fourier_coe_apply` gives `exp (2π i n θ / T)`.
  -- With `T = 2π` this is exactly `exp (i * (n•θ))`.
  -- The remaining work is arithmetic in the exponent inside `exp`.
  have hfourier :
      fourier (T := (2 * Real.pi)) n (θ : AddCircle (2 * Real.pi)) =
        Complex.exp (2 * Real.pi * Complex.I * n * θ / (2 * Real.pi)) := by
    simpa using (fourier_coe_apply (T := (2 * Real.pi)) (n := n) (x := θ))
  -- Rewrite division by `2π` as multiplication by its inverse and cancel.
  -- (ℂ is commutative, so `simp` + commutativity is enough once we expose `h2pi0c`.)
  calc
    Complex.exp (Complex.I * (n • θ))
        = Complex.exp (Complex.I * ((n : ℝ) * θ)) := by
            -- `n • θ` is `((n : ℝ) * θ)` in `ℝ`.
            simpa [zsmul_eq_mul]
    _ = Complex.exp (Complex.I * ((n : ℂ) * (θ : ℂ))) := by
            norm_cast
    _ = Complex.exp (2 * Real.pi * Complex.I * n * θ / (2 * Real.pi)) := by
            -- Cancel the `2π` factor.
            -- We rewrite the exponent using commutativity and `mul_inv_cancel`.
            have :
                (2 * Real.pi * (Complex.I * ((n : ℂ) * (θ : ℂ))) / (2 * Real.pi)) =
                  (Complex.I * ((n : ℂ) * (θ : ℂ))) := by
              -- `a * x / a = x` for `a ≠ 0`.
              simp [div_eq_mul_inv, h2pi0c, mul_assoc, mul_left_comm, mul_comm]
            -- Now match Mathlib's monomial normal form.
            -- `fourier_coe_apply` uses `2π * I * n * θ / T`; commute factors to align.
            -- The `simp` above already did the cancellation; we just massage associativity/commutativity.
            -- `simp` on the exponent is safe because we never unfold `exp`.
            -- (Use `congrArg` to rewrite inside `exp`.)
            exact congrArg Complex.exp (by
              -- reorder and apply `this`
              simpa [mul_assoc, mul_left_comm, mul_comm, this])
    _ = fourier (T := (2 * Real.pi)) n (θ : AddCircle (2 * Real.pi)) := by
            simpa [hfourier]

/-- Re-export: Fourier series sums to `f` in `L²(AddCircle (2π))`. -/
theorem hasSum_fourier_series_L2_two_pi
    (f : Lp ℂ 2 <| @haarAddCircle (2 * Real.pi) (by
      -- `0 < 2π`
      exact (show Fact (0 < (2 * Real.pi)) from ⟨mul_pos (by norm_num) Real.pi_pos⟩)) ) :
    HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f := by
  -- `hasSum_fourier_series_L2` is Mathlib's core completeness statement.
  simpa using (hasSum_fourier_series_L2 (T := (2 * Real.pi)) f)

end EulerFourier

end Analysis
end HeytingLean

