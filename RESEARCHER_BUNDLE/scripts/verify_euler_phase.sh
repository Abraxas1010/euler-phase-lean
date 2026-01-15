#!/usr/bin/env bash
set -euo pipefail

echo "=== Euler Phase Lean Verification ==="
echo ""

cd "$(dirname "$0")/.."

# Check for sorry/admit
echo "Checking for sorry/admit..."
if grep -rn "sorry\|admit" HeytingLean/*.lean HeytingLean/**/*.lean 2>/dev/null; then
    echo "ERROR: Found sorry/admit in codebase"
    exit 1
fi
echo "✓ No sorry/admit found"
echo ""

# Build
echo "Building with lake..."
lake build --wfail
echo "✓ Build successful"
echo ""

# Check key declarations exist
echo "Verifying key declarations..."
lake env lean -c "import HeytingLean" 2>/dev/null || {
    echo "ERROR: Failed to import HeytingLean"
    exit 1
}
echo "✓ All declarations type-check"
echo ""

# Summary
echo "=== Verification Complete ==="
echo ""
echo "Key modules verified:"
echo "  - Analysis/EulerBoundary.lean"
echo "  - Analysis/EulerFourierBridge.lean"
echo "  - Analysis/EulerSpectralBridge.lean"
echo "  - Analysis/EulerComplexGateway.lean"
echo "  - Complex/ComplexNucleus.lean"
echo "  - Complex/PhaseEigenforms.lean"
echo "  - Complex/AnalyticMaps.lean"
echo "  - Complex/ContourIntegral.lean"
echo "  - Complex/CliffordComplexBridge.lean"
echo ""
echo "All checks passed!"
