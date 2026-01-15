import HeytingLean.Complex.ComplexNucleus
import HeytingLean.Complex.PhaseEigenforms
import HeytingLean.Complex.AnalyticMaps
import HeytingLean.Complex.ContourIntegral
import HeytingLean.Complex.CliffordComplexBridge

namespace HeytingLean
namespace Tests
namespace Complex

open scoped Real

open HeytingLean.Complex

/-! # Smoke tests for the Complex Analysis integration layer -/

-- ComplexNucleus at θ = 0
example : (⟨0⟩ : ComplexNucleus).action (1 : ℂ) = 1 := by
  simp [ComplexNucleus.action]

-- ComplexNucleus at θ = π is negation
example : (⟨Real.pi⟩ : ComplexNucleus).action (3 : ℂ) = -3 := by
  have := congrArg (fun f => f (3 : ℂ)) (ComplexNucleus.action_pi)
  simpa using this

-- Norm preservation
example (θ : ℝ) (z : ℂ) : ‖(⟨θ⟩ : ComplexNucleus).action z‖ = ‖z‖ :=
  ComplexNucleus.action_norm _ _

-- PhaseEigenform construction
example : PhaseEigenform.real (F := id) (1 : ℂ) rfl =
    { val := 1, phase := 1, phase_unit := by simp, is_eigen := by simp } := rfl

-- Anti-eigenform
example : (PhaseEigenform.anti (F := fun z => -z) (1 : ℂ) rfl).phase = -1 := rfl

-- Holomorphic id
example : HeytingLean.Complex.Holomorphic (id : ℂ → ℂ) :=
  id_holomorphic

-- `Cl2Rep` round-trip
example (z : ℂ) : (Cl2Rep.ofComplex z).toComplex = z :=
  Cl2Rep.toComplex_ofComplex z

-- Rotor is a phase (exists θ)
example (x : Cl2Rep) (hx : x.IsRotor) : ∃ θ, x.toComplex = HeytingLean.Analysis.eulerBoundary θ :=
  Cl2Rep.rotor_is_phase x hx

-- Import smoke checks
#check ComplexNucleus.action_continuous
#check PhaseEigenform.phase_on_circle
#check HeytingLean.Complex.Holomorphic
#check circleIntegral
#check circleWindingNumber

end Complex
end Tests
end HeytingLean

