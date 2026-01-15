# Reproducibility Guide

## Requirements

- **Lean 4**: Version specified in `lean-toolchain`
- **Lake**: Included with Lean 4
- **Git**: For cloning and dependency management

## Quick Start

```bash
# Clone the repository
git clone https://github.com/Abraxas1010/euler-phase-lean.git
cd euler-phase-lean/RESEARCHER_BUNDLE

# Install Mathlib (this may take a while on first run)
lake update

# Build the project
lake build --wfail

# Run verification script
./scripts/verify_euler_phase.sh
```

## Build Details

### Toolchain

The exact Lean version is pinned in `lean-toolchain`:
```
leanprover/lean4:v4.x.x
```

### Dependencies

The `lake-manifest.json` pins the exact Mathlib commit hash for reproducibility.

### Build Flags

We use `--wfail` to treat warnings as errors, ensuring:
- No unused imports
- No unused variables
- No deprecation warnings

## Verification Checklist

1. **No sorry/admit**: `grep -rn "sorry\|admit" HeytingLean/` returns empty
2. **Clean build**: `lake build --wfail` succeeds
3. **All imports resolve**: No "unknown identifier" errors
4. **Tests pass**: Sanity test modules compile

## Troubleshooting

### "unknown identifier" errors

Run `lake update` to ensure Mathlib is properly installed.

### Build cache issues

```bash
lake clean
lake update
lake build
```

### Out of memory during build

Mathlib is large. Ensure you have at least 8GB RAM available, or use:
```bash
lake build -j1  # Single-threaded build
```

## Continuous Integration

This repository is designed for local verification. For CI integration, see the parent [HeytingLean](https://github.com/Abraxas1010/heyting) project.
