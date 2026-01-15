// Euler Phase Lean - UMAP Visualization Data
// Machine-checked formalization of complex boundary thesis
// Generated: 2026-01-15

const eulerPhaseProofsData = {
  items: [
    // === Analysis Layer: Euler Boundary ===
    { name: "eulerBoundary", kind: "def", family: "EulerBoundary", pos: { x: 0.15, y: 0.85, z: 0.50 } },
    { name: "eulerBoundary_zero", kind: "theorem", family: "EulerBoundary", pos: { x: 0.18, y: 0.82, z: 0.48 } },
    { name: "eulerBoundary_expansion", kind: "theorem", family: "EulerBoundary", pos: { x: 0.12, y: 0.80, z: 0.52 } },
    { name: "eulerBoundary_add", kind: "theorem", family: "EulerBoundary", pos: { x: 0.20, y: 0.78, z: 0.45 } },
    { name: "eulerBoundary_periodic", kind: "theorem", family: "EulerBoundary", pos: { x: 0.22, y: 0.83, z: 0.55 } },
    { name: "norm_eulerBoundary", kind: "theorem", family: "EulerBoundary", pos: { x: 0.16, y: 0.88, z: 0.47 } },

    // === Analysis Layer: Fourier Bridge ===
    { name: "fourierCoeffEuler", kind: "def", family: "FourierBridge", pos: { x: 0.30, y: 0.75, z: 0.40 } },
    { name: "fourierCoeff_eulerBoundary", kind: "theorem", family: "FourierBridge", pos: { x: 0.33, y: 0.72, z: 0.42 } },
    { name: "euler_fourier_correspondence", kind: "theorem", family: "FourierBridge", pos: { x: 0.28, y: 0.70, z: 0.38 } },
    { name: "fourierCoeff_zero_one", kind: "theorem", family: "FourierBridge", pos: { x: 0.35, y: 0.77, z: 0.44 } },

    // === Analysis Layer: Spectral Bridge ===
    { name: "spectralMeasure", kind: "def", family: "SpectralBridge", pos: { x: 0.25, y: 0.60, z: 0.35 } },
    { name: "spectralIntegral", kind: "def", family: "SpectralBridge", pos: { x: 0.28, y: 0.58, z: 0.33 } },
    { name: "spectral_euler_consistency", kind: "theorem", family: "SpectralBridge", pos: { x: 0.22, y: 0.55, z: 0.37 } },

    // === Analysis Layer: Complex Gateway ===
    { name: "ComplexGateway", kind: "structure", family: "ComplexGateway", pos: { x: 0.40, y: 0.65, z: 0.30 } },
    { name: "complexGateway_toComplex", kind: "def", family: "ComplexGateway", pos: { x: 0.43, y: 0.62, z: 0.28 } },
    { name: "complexGateway_norm", kind: "theorem", family: "ComplexGateway", pos: { x: 0.38, y: 0.68, z: 0.32 } },

    // === Complex Layer: ComplexNucleus ===
    { name: "ComplexNucleus", kind: "structure", family: "ComplexNucleus", pos: { x: 0.55, y: 0.75, z: 0.60 } },
    { name: "ComplexNucleus.action", kind: "def", family: "ComplexNucleus", pos: { x: 0.58, y: 0.72, z: 0.58 } },
    { name: "action_zero", kind: "theorem", family: "ComplexNucleus", pos: { x: 0.52, y: 0.78, z: 0.62 } },
    { name: "action_pi", kind: "theorem", family: "ComplexNucleus", pos: { x: 0.60, y: 0.70, z: 0.55 } },
    { name: "action_two_pi", kind: "theorem", family: "ComplexNucleus", pos: { x: 0.56, y: 0.80, z: 0.65 } },
    { name: "action_norm", kind: "theorem", family: "ComplexNucleus", pos: { x: 0.62, y: 0.77, z: 0.57 } },
    { name: "action_continuous", kind: "theorem", family: "ComplexNucleus", pos: { x: 0.50, y: 0.73, z: 0.63 } },
    { name: "action_comp", kind: "theorem", family: "ComplexNucleus", pos: { x: 0.64, y: 0.82, z: 0.59 } },
    { name: "RealNucleus", kind: "def", family: "ComplexNucleus", pos: { x: 0.48, y: 0.68, z: 0.67 } },

    // === Complex Layer: PhaseEigenforms ===
    { name: "PhaseEigenform", kind: "structure", family: "PhaseEigenforms", pos: { x: 0.70, y: 0.60, z: 0.50 } },
    { name: "realEigenform", kind: "def", family: "PhaseEigenforms", pos: { x: 0.73, y: 0.57, z: 0.48 } },
    { name: "antiEigenform", kind: "def", family: "PhaseEigenforms", pos: { x: 0.68, y: 0.63, z: 0.52 } },
    { name: "quarterEigenform", kind: "def", family: "PhaseEigenforms", pos: { x: 0.75, y: 0.55, z: 0.45 } },
    { name: "phase_unique", kind: "theorem", family: "PhaseEigenforms", pos: { x: 0.72, y: 0.65, z: 0.55 } },

    // === Complex Layer: AnalyticMaps ===
    { name: "DistinctionPreservingAt", kind: "def", family: "AnalyticMaps", pos: { x: 0.80, y: 0.45, z: 0.40 } },
    { name: "Holomorphic", kind: "def", family: "AnalyticMaps", pos: { x: 0.83, y: 0.42, z: 0.38 } },
    { name: "RotationCompatible", kind: "def", family: "AnalyticMaps", pos: { x: 0.78, y: 0.48, z: 0.42 } },
    { name: "id_holomorphic", kind: "theorem", family: "AnalyticMaps", pos: { x: 0.85, y: 0.40, z: 0.35 } },
    { name: "comp_holomorphic", kind: "theorem", family: "AnalyticMaps", pos: { x: 0.82, y: 0.50, z: 0.44 } },
    { name: "nucleus_action_holomorphic", kind: "theorem", family: "AnalyticMaps", pos: { x: 0.76, y: 0.52, z: 0.46 } },
    { name: "rotationCompatible_id", kind: "theorem", family: "AnalyticMaps", pos: { x: 0.88, y: 0.38, z: 0.33 } },
    { name: "rotationCompatible_mul", kind: "theorem", family: "AnalyticMaps", pos: { x: 0.80, y: 0.55, z: 0.48 } },
    { name: "rotationCompatible_comp", kind: "theorem", family: "AnalyticMaps", pos: { x: 0.84, y: 0.47, z: 0.36 } },

    // === Complex Layer: ContourIntegral ===
    { name: "circleIntegral", kind: "def", family: "ContourIntegral", pos: { x: 0.60, y: 0.30, z: 0.25 } },
    { name: "unitCircle", kind: "def", family: "ContourIntegral", pos: { x: 0.63, y: 0.27, z: 0.23 } },
    { name: "circleWindingNumber", kind: "def", family: "ContourIntegral", pos: { x: 0.58, y: 0.33, z: 0.27 } },
    { name: "circleWindingNumber_of_mem", kind: "theorem", family: "ContourIntegral", pos: { x: 0.65, y: 0.25, z: 0.20 } },
    { name: "circleWindingNumber_of_not_mem", kind: "theorem", family: "ContourIntegral", pos: { x: 0.55, y: 0.35, z: 0.30 } },
    { name: "circleIntegral_div_sub_of_differentiableOn", kind: "theorem", family: "ContourIntegral", pos: { x: 0.62, y: 0.22, z: 0.18 } },
    { name: "cauchyValue_eq_inv_two_pi_I_mul_circleIntegral", kind: "theorem", family: "ContourIntegral", pos: { x: 0.68, y: 0.20, z: 0.15 } },
    { name: "circleWindingNumber_wellDefined", kind: "theorem", family: "ContourIntegral", pos: { x: 0.57, y: 0.28, z: 0.22 } },

    // === Complex Layer: CliffordComplexBridge ===
    { name: "Cl2Rep", kind: "structure", family: "CliffordBridge", pos: { x: 0.35, y: 0.40, z: 0.70 } },
    { name: "Cl2Rep.toComplex", kind: "def", family: "CliffordBridge", pos: { x: 0.38, y: 0.37, z: 0.68 } },
    { name: "Cl2Rep.ofComplex", kind: "def", family: "CliffordBridge", pos: { x: 0.32, y: 0.43, z: 0.72 } },
    { name: "toComplex_ofComplex", kind: "theorem", family: "CliffordBridge", pos: { x: 0.40, y: 0.35, z: 0.65 } },
    { name: "ofComplex_toComplex", kind: "theorem", family: "CliffordBridge", pos: { x: 0.30, y: 0.45, z: 0.75 } },
    { name: "Cl2Rep.mul", kind: "def", family: "CliffordBridge", pos: { x: 0.42, y: 0.38, z: 0.62 } },
    { name: "toComplex_mul", kind: "theorem", family: "CliffordBridge", pos: { x: 0.37, y: 0.32, z: 0.58 } },
    { name: "IsRotor", kind: "def", family: "CliffordBridge", pos: { x: 0.45, y: 0.42, z: 0.77 } },
    { name: "rotor_is_phase", kind: "theorem", family: "CliffordBridge", pos: { x: 0.33, y: 0.48, z: 0.80 } },
    { name: "rotor_action_eq_nucleus", kind: "theorem", family: "CliffordBridge", pos: { x: 0.48, y: 0.45, z: 0.73 } },
    { name: "spinor_phase_correspondence", kind: "theorem", family: "CliffordBridge", pos: { x: 0.40, y: 0.50, z: 0.82 } },

    // === Tests ===
    { name: "euler_boundary_sanity", kind: "test", family: "Tests", pos: { x: 0.10, y: 0.15, z: 0.85 } },
    { name: "complex_analysis_sanity", kind: "test", family: "Tests", pos: { x: 0.90, y: 0.15, z: 0.85 } }
  ],

  edges: [
    // EulerBoundary internal
    [0, 1], [0, 2], [0, 3], [0, 4], [0, 5],  // eulerBoundary -> its theorems
    [2, 1],  // expansion -> zero
    [3, 4],  // add -> periodic

    // FourierBridge depends on EulerBoundary
    [0, 6], [0, 7], [0, 8], [0, 9],  // eulerBoundary -> Fourier defs
    [6, 7], [6, 8],  // fourierCoeffEuler -> theorems

    // SpectralBridge depends on EulerBoundary
    [0, 10], [0, 11], [0, 12],  // eulerBoundary -> spectral
    [10, 11], [10, 12],

    // ComplexGateway depends on Euler + Fourier
    [0, 13], [6, 13], [10, 13],  // gateway uses all analysis
    [13, 14], [13, 15],

    // ComplexNucleus depends on EulerBoundary
    [0, 16], [0, 17],  // eulerBoundary -> ComplexNucleus
    [17, 18], [17, 19], [17, 20],  // action -> action_zero/pi/two_pi
    [2, 19],  // expansion -> action_pi
    [4, 20],  // periodic -> action_two_pi
    [5, 21],  // norm_eulerBoundary -> action_norm
    [17, 22], [17, 23],  // action -> continuous, comp
    [3, 23],  // add -> action_comp
    [16, 24],  // ComplexNucleus -> RealNucleus

    // PhaseEigenforms depends on ComplexNucleus
    [16, 25], [17, 25],  // ComplexNucleus -> PhaseEigenform
    [25, 26], [25, 27], [25, 28], [25, 29],  // PhaseEigenform -> constructors + unique

    // AnalyticMaps depends on PhaseEigenforms + ComplexNucleus
    [25, 30], [25, 31], [25, 32],  // PhaseEigenform -> DistinctionPreserving, etc.
    [17, 35],  // action -> nucleus_action_holomorphic
    [32, 36], [32, 37], [32, 38],  // RotationCompatible -> theorems

    // ContourIntegral depends on AnalyticMaps
    [31, 39], [31, 45],  // Holomorphic -> circleIntegral, Cauchy
    [39, 40], [39, 41],  // circleIntegral -> unitCircle, windingNumber
    [41, 42], [41, 43], [41, 46],  // windingNumber -> lemmas

    // CliffordBridge depends on PhaseEigenforms + ComplexNucleus
    [25, 47], [16, 47],  // PhaseEigenform, ComplexNucleus -> Cl2Rep
    [47, 48], [47, 49],  // Cl2Rep -> toComplex, ofComplex
    [48, 50], [49, 51],  // roundtrip theorems
    [47, 52], [52, 53],  // mul and its theorem
    [47, 54], [54, 55],  // IsRotor -> rotor_is_phase
    [0, 55],  // eulerBoundary -> rotor_is_phase (uses norm_eq_one_iff)
    [55, 56], [17, 56],  // rotor_is_phase, action -> rotor_action_eq_nucleus
    [56, 57], [25, 57],  // -> spinor_phase_correspondence

    // Tests depend on all
    [0, 58], [16, 58],  // euler_boundary_sanity
    [25, 59], [47, 59], [39, 59]  // complex_analysis_sanity
  ]
};

// Family colors for visualization
const familyColors = {
  'EulerBoundary': '#5e9cff',      // Blue - foundation
  'FourierBridge': '#c77dff',      // Purple - harmonic analysis
  'SpectralBridge': '#4ade80',     // Green - spectral theory
  'ComplexGateway': '#22d3d3',     // Cyan - gateway abstraction
  'ComplexNucleus': '#fbbf24',     // Amber - core complex nucleus
  'PhaseEigenforms': '#f472b6',    // Pink - eigenforms
  'AnalyticMaps': '#fb923c',       // Orange - analytic functions
  'ContourIntegral': '#ef4444',    // Red - integration
  'CliffordBridge': '#d946ef',     // Magenta - Clifford algebra
  'Tests': '#a3a3a3'               // Gray - tests
};

// Export for module use
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { eulerPhaseProofsData, familyColors };
}
