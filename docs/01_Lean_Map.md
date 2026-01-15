# Lean Module Map

## Overview

This formalization consists of two layers: the **Euler Boundary Layer** (foundational e^(iθ) definitions) and the **Complex Analysis Layer** (phase eigenforms and nucleus actions).

## Module Structure

```
HeytingLean/
├── Analysis/                     # Euler Boundary Layer
│   ├── EulerBoundary.lean       # e^(iθ) = cos(θ) + i·sin(θ)
│   ├── EulerFourierBridge.lean  # Connection to Fourier analysis
│   ├── EulerSpectralBridge.lean # Spectral measure integration
│   └── EulerComplexGateway.lean # Gateway abstraction
│
├── Complex/                      # Complex Analysis Layer
│   ├── ComplexNucleus.lean      # R_ℂ = e^(iθ) rotation
│   ├── PhaseEigenforms.lean     # λ = e^(iθ) eigenforms
│   ├── AnalyticMaps.lean        # Holomorphic functions
│   ├── ContourIntegral.lean     # Circle integrals
│   └── CliffordComplexBridge.lean # Cl(2,0) ↔ ℂ
│
└── Tests/                        # Sanity tests
```

## Dependency Graph

```
EulerBoundary
    │
    ├───→ EulerFourierBridge
    ├───→ EulerSpectralBridge
    └───→ EulerComplexGateway
            │
            └───→ ComplexNucleus
                    │
                    ├───→ PhaseEigenforms
                    │         │
                    │         ├───→ AnalyticMaps
                    │         │         │
                    │         │         └───→ ContourIntegral
                    │         │
                    │         └───→ CliffordComplexBridge
                    │
                    └───→ Tests/*
```

## Key Imports from Mathlib

- `Mathlib.Analysis.SpecialFunctions.Complex.Log` - Complex exponential
- `Mathlib.Analysis.Complex.Trigonometric` - Trigonometric identities
- `Mathlib.Analysis.Complex.CauchyIntegral` - Cauchy integral formula
- `Mathlib.MeasureTheory.Integral.CircleIntegral` - Circle integrals
- `Mathlib.Analysis.Analytic.Basic` - Analyticity
