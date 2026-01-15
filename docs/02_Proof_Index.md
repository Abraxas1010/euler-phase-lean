# Proof Index

## Euler Boundary (Analysis/EulerBoundary.lean)

| Declaration | Type | Description |
|-------------|------|-------------|
| `eulerBoundary` | def | e^(iθ) = exp(I * θ) |
| `eulerBoundary_zero` | theorem | e^(i·0) = 1 |
| `eulerBoundary_expansion` | theorem | e^(iθ) = cos(θ) + i·sin(θ) |
| `eulerBoundary_add` | theorem | e^(i(θ₁+θ₂)) = e^(iθ₁)·e^(iθ₂) |
| `eulerBoundary_periodic` | theorem | e^(i(θ+2π)) = e^(iθ) |
| `norm_eulerBoundary` | theorem | ‖e^(iθ)‖ = 1 |

## Complex Nucleus (Complex/ComplexNucleus.lean)

| Declaration | Type | Description |
|-------------|------|-------------|
| `ComplexNucleus` | structure | Rotation parameterized by angle θ |
| `ComplexNucleus.action` | def | z ↦ e^(iθ) * z |
| `action_zero` | theorem | R_0 = id |
| `action_pi` | theorem | R_π(z) = -z |
| `action_two_pi` | theorem | R_{2π} = id |
| `action_norm` | theorem | ‖R_θ(z)‖ = ‖z‖ |
| `action_continuous` | theorem | R_θ is continuous |
| `action_comp` | theorem | R_θ₁ ∘ R_θ₂ = R_{θ₁+θ₂} |
| `RealNucleus` | def | θ ∈ {0, π} restriction |

## Phase Eigenforms (Complex/PhaseEigenforms.lean)

| Declaration | Type | Description |
|-------------|------|-------------|
| `PhaseEigenform` | structure | Eigenform with phase λ = e^(iθ) |
| `realEigenform` | def | Classical eigenform (λ = 1) |
| `antiEigenform` | def | Anti-eigenform (λ = -1) |
| `quarterEigenform` | def | Quarter-turn eigenform (λ = i) |
| `phase_unique` | theorem | Eigenvalue determines phase uniquely |

## Analytic Maps (Complex/AnalyticMaps.lean)

| Declaration | Type | Description |
|-------------|------|-------------|
| `DistinctionPreservingAt` | def | Complex differentiable at z |
| `Holomorphic` | def | Globally complex differentiable |
| `RotationCompatible` | def | f(R·z) = R·f(z) |
| `id_holomorphic` | theorem | Identity is holomorphic |
| `comp_holomorphic` | theorem | Composition preserves holomorphicity |
| `nucleus_action_holomorphic` | theorem | R_θ is holomorphic |
| `rotationCompatible_id` | theorem | Identity is rotation-compatible |
| `rotationCompatible_mul` | theorem | Scalar multiplication is rotation-compatible |
| `rotationCompatible_comp` | theorem | Composition preserves rotation-compatibility |

## Contour Integral (Complex/ContourIntegral.lean)

| Declaration | Type | Description |
|-------------|------|-------------|
| `circleIntegral` | def | Re-export of Mathlib circle integral |
| `unitCircle` | def | {z : ‖z‖ = 1} |
| `circleWindingNumber` | def | 1 if inside circle, 0 otherwise |
| `circleWindingNumber_of_mem` | theorem | Inside → winding = 1 |
| `circleWindingNumber_of_not_mem` | theorem | Outside → winding = 0 |
| `circleIntegral_div_sub_of_differentiableOn` | theorem | Cauchy integral formula |
| `cauchyValue_eq_inv_two_pi_I_mul_circleIntegral` | theorem | f(w) = (1/2πi)∮f(z)/(z-w)dz |
| `circleWindingNumber_wellDefined` | theorem | Winding number is integer |

## Clifford Bridge (Complex/CliffordComplexBridge.lean)

| Declaration | Type | Description |
|-------------|------|-------------|
| `Cl2Rep` | structure | scalar + bivector representation |
| `Cl2Rep.toComplex` | def | a + b·(e₁e₂) ↦ a + bi |
| `Cl2Rep.ofComplex` | def | a + bi ↦ a + b·(e₁e₂) |
| `toComplex_ofComplex` | theorem | Left inverse |
| `ofComplex_toComplex` | theorem | Right inverse |
| `Cl2Rep.mul` | def | Multiplication via complex multiplication |
| `toComplex_mul` | theorem | Homomorphism |
| `IsRotor` | def | ‖x.toComplex‖ = 1 |
| `rotor_is_phase` | theorem | Rotors are exactly e^(iθ) |
| `rotor_action_eq_nucleus` | theorem | Rotor action = ComplexNucleus action |
| `spinor_phase_correspondence` | theorem | Bridge to PhaseEigenform |
