/-!
# Euler Phase Lean - Complex Boundary Formalization

Machine-checked formalization of the complexified boundary thesis:
"The boundary of distinction is inherently complex;
Boolean/real is the degenerate θ ∈ {0, π} case"

## Modules

### Laws of Form Layer (Nucleus Infrastructure)
- `PrimaryAlgebra`: Frame-based LoF base (locale interpretation)
- `Nucleus`: Reentry nucleus, Euler boundary, Ω fixed-point sublocale
- `SKY`: SKY combinator calculus with small-step reduction
- `CombinatorMap`: K=unmark, S=mark, Y=reentry correspondence

### Epistemic Layer (Occam's Razor)
- `Occam`: Birthday minimization, `breathe`, `birth`, `occam` operators

### Logic Layer (Principle of Sufficient Reason)
- `PSR`: Sufficient = fixed by nucleus, reachability, `occam_sufficient`

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
- `Primordial`: Dialectic pair, zero_sum, supported oscillation

### Quantum Layer (Bloch Sphere)
- `LoFBloch`: Bloch sphere model with LoF coordinates (j, k, mark)
  - void = |0⟩ (north pole), mark = |1⟩ (south pole)
  - reentry = |+⟩ (equator)
  - Pauli gates as Bloch rotations
  - su(2) Poisson bracket structure

### Key Theorems
- `euler_identity`: e^(iπ) + 1 = 0 (the "God Equation")
- `zero_sum`: dialectic pair sums to zero (thesis + antithesis = 0)
- `occam_sufficient`: Occam reduction is invariant under nucleus
- `sufficient_eulerBoundary`: Euler boundary satisfies PSR
- `action_comp`: R_θ₁ ∘ R_θ₂ = R_{θ₁+θ₂}
- `rotor_is_phase`: Unit-norm Cl2Rep elements are e^(iθ)
- `spinor_phase_correspondence`: Rotor action = phase eigenform
- `monad_composition`: Monad phases add (group structure)
- `poisson_is_su2`: Bloch coordinate brackets match su(2)
-/

-- Laws of Form Layer
import HeytingLean.LoF.PrimaryAlgebra
import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.Combinators.Heyting.CombinatorMap

-- Epistemic Layer
import HeytingLean.Epistemic.Occam

-- Logic Layer
import HeytingLean.Logic.PSR

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
import HeytingLean.Ontology.Primordial

-- Quantum Layer
import HeytingLean.Quantum.LoFBloch

-- Tests
import HeytingLean.Tests.Analysis.EulerBoundarySanity
import HeytingLean.Tests.Complex.ComplexAnalysisSanity
