/-!
# Euler Phase Lean - Complex Boundary Formalization

Machine-checked formalization of the complexified boundary thesis:
"The boundary of distinction is inherently complex;
Boolean/real is the degenerate θ ∈ {0, π} case"

## Modules

### Analysis Layer (Euler Boundary)
- `EulerBoundary`: e^(iθ) with periodicity and unit norm
- `EulerFourierBridge`: Connection to Fourier coefficients
- `EulerSpectralBridge`: Spectral measure integration
- `EulerComplexGateway`: Complex gateway abstraction

### Complex Layer (Phase Eigenforms)
- `ComplexNucleus`: R_ℂ = e^(iθ) rotation action
- `PhaseEigenforms`: λ = e^(iθ) eigenforms generalizing real Y-eigenforms
- `AnalyticMaps`: Holomorphic functions + rotation compatibility
- `ContourIntegral`: Circle integrals + Cauchy formula
- `CliffordComplexBridge`: Cl(2,0) ↔ ℂ correspondence

### Key Theorems
- `action_comp`: R_θ₁ ∘ R_θ₂ = R_{θ₁+θ₂}
- `rotor_is_phase`: Unit-norm Cl2Rep elements are e^(iθ)
- `spinor_phase_correspondence`: Rotor action = phase eigenform
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

-- Tests
import HeytingLean.Tests.Analysis.EulerBoundarySanity
import HeytingLean.Tests.Complex.ComplexAnalysisSanity
