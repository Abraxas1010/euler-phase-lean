import HeytingLean.Complex.ComplexNucleus
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace HeytingLean
namespace Complex

/-!
# Phase eigenforms

This file defines a lightweight “eigenform-with-phase” structure:

`F J = λ * J` with `‖λ‖ = 1`.

It generalizes the classical “fixed-point eigenform” case `λ = 1` (and the “anti” case `λ = -1`)
without claiming any deeper connection to LoF/Bauer eigenforms beyond this analogy.
-/

/-- An eigenform with a unit-modulus complex phase. -/
structure PhaseEigenform (F : ℂ → ℂ) where
  val : ℂ
  phase : ℂ
  phase_unit : ‖phase‖ = 1
  is_eigen : F val = phase * val

namespace PhaseEigenform

variable {F : ℂ → ℂ}

/-- Standard eigenform: `phase = 1`, so `F(J) = J`. -/
def real (J : ℂ) (h : F J = J) : PhaseEigenform F where
  val := J
  phase := 1
  phase_unit := by simp
  is_eigen := by simp [h]

/-- Anti-eigenform: `phase = -1`, so `F(J) = -J`. -/
def anti (J : ℂ) (h : F J = -J) : PhaseEigenform F where
  val := J
  phase := -1
  phase_unit := by simp
  is_eigen := by simp [h]

/-- Quarter-phase eigenform: `phase = i`, so `F(J) = i * J`. -/
def quarter (J : ℂ) (h : F J = Complex.I * J) : PhaseEigenform F where
  val := J
  phase := Complex.I
  phase_unit := by simp
  is_eigen := h

/-- Extract a canonical real “angle” from the phase via `Complex.arg`. -/
noncomputable def angle (P : PhaseEigenform F) : ℝ :=
  Complex.arg P.phase

/-- A phase eigenform has its phase on the unit sphere around `0`. -/
theorem phase_on_circle (P : PhaseEigenform F) : P.phase ∈ Metric.sphere (0 : ℂ) 1 := by
  -- `x ∈ sphere 0 1 ↔ ‖x‖ = 1`.
  simpa [Metric.mem_sphere, dist_eq_norm] using P.phase_unit

/-- If two eigenforms share the same nonzero value, their phases coincide. -/
theorem phase_unique (P Q : PhaseEigenform F)
    (hv : P.val = Q.val) (hnz : P.val ≠ 0) : P.phase = Q.phase := by
  -- Compare `F v` in two ways.
  have hP : F P.val = P.phase * P.val := P.is_eigen
  have hQ : F P.val = Q.phase * P.val := by
    simpa [hv] using Q.is_eigen
  have : P.phase * P.val = Q.phase * P.val := by
    exact hP.symm.trans hQ
  exact mul_right_cancel₀ hnz this

end PhaseEigenform

end Complex
end HeytingLean
