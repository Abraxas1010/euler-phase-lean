/-!
# Euler Phase Lean - Complex Boundary Formalization

Machine-checked formalization of the complexified boundary thesis:
"The boundary of distinction is inherently complex;
Boolean/real is the degenerate θ ∈ {0, π} case"

## Modules

### Analysis Layer (Euler Boundary)
- `EulerBoundary`: e^(iθ) with periodicity, unit norm, and God Equation
- `EulerFourierBridge`: Connection to Fourier coefficients
- `EulerSpectralBridge`: Spectral measure integration
- `EulerComplexGateway`: Complex gateway abstraction

### Complex Layer (Phase Eigenforms)
- `ComplexNucleus`: R_ℂ = e^(iθ) rotation action
- `PhaseEigenforms`: λ = e^(iθ) eigenforms generalizing real Y-eigenforms
- `AnalyticMaps`: Holomorphic functions + rotation compatibility
- `ContourIntegral`: Circle integrals + Cauchy formula
- `CliffordComplexBridge`: Cl(2,0) ↔ ℂ correspondence

### Ontology Layer (Monadology Bridge)
- `Monadology`: Bridge to Ontological Mathematics (Pythagorean Illuminati tradition)
  - Monad = ComplexNucleus
  - God Equation = euler_identity
  - Frequency Domain ↔ Spacetime Domain

### Key Theorems
- `euler_identity`: e^(iπ) + 1 = 0 (the "God Equation")
- `action_comp`: R_θ₁ ∘ R_θ₂ = R_{θ₁+θ₂}
- `rotor_is_phase`: Unit-norm Cl2Rep elements are e^(iθ)
- `spinor_phase_correspondence`: Rotor action = phase eigenform
- `monad_composition`: Monad phases add (group structure)
-/

-- Analysis Layer
import HeytingLean.Analysis.EulerBoundary
import HeytingLean.Analysis.EulerFourierBridge
import HeytingLean.Analysis.EulerSpectralBridge
import HeytingLean.Analysis.EulerComplexGateway

-- Complex Layer
import HeytingLean.Complex.ComplexNucleus
import HeytingLean.Complex.PhaseEigenforms
import HeytingLean.Complex.AnalyticMaps
import HeytingLean.Complex.ContourIntegral
import HeytingLean.Complex.CliffordComplexBridge

-- Ontology Layer
import HeytingLean.Ontology.Monadology

-- Tests
import HeytingLean.Tests.Analysis.EulerBoundarySanity
import HeytingLean.Tests.Complex.ComplexAnalysisSanity
