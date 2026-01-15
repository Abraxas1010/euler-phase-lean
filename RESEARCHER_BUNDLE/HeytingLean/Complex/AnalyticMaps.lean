import HeytingLean.Complex.PhaseEigenforms
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

namespace HeytingLean
namespace Complex

/-!
# Analytic maps (Mathlib-aligned) + rotation-compatibility predicate

`WIP/complex_analysis.md` frames holomorphic functions as “distinction-preserving”.
Formally, we reuse Mathlib’s standard notion:

* `DifferentiableAt ℂ f z` for pointwise complex differentiability;
* `Differentiable ℂ f` for global holomorphicity.

Additionally, to make precise (and *correct*) a common heuristic in the notes, we define an
explicit **rotation-compatibility** predicate and prove it for the linear maps we actually use.

We do **not** claim “holomorphic iff rotation-compatible” (false in general).
-/

/-- Pointwise “distinction-preserving” = complex differentiable at `z`. -/
def DistinctionPreservingAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  DifferentiableAt ℂ f z

/-- Global “distinction-preserving” = holomorphic. -/
def Holomorphic (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f

/-- Rotation-compatibility with the complex nucleus action. -/
def RotationCompatible (f : ℂ → ℂ) : Prop :=
  ∀ (R : ComplexNucleus) (z : ℂ), f (R.action z) = R.action (f z)

theorem id_holomorphic : Holomorphic (id : ℂ → ℂ) :=
  differentiable_id

theorem comp_holomorphic {f g : ℂ → ℂ} (hf : Holomorphic f) (hg : Holomorphic g) :
    Holomorphic (f ∘ g) :=
  hf.comp hg

theorem const_holomorphic (c : ℂ) : Holomorphic (fun _ => c) :=
  differentiable_const c

theorem mul_holomorphic (c : ℂ) : Holomorphic (fun z => c * z) :=
  (differentiable_const c).mul differentiable_id

theorem nucleus_action_holomorphic (R : ComplexNucleus) : Holomorphic R.action := by
  -- `z ↦ (const) * z` is differentiable.
  simpa [ComplexNucleus.action] using mul_holomorphic (c := HeytingLean.Analysis.eulerBoundary R.θ)

theorem rotationCompatible_id : RotationCompatible (id : ℂ → ℂ) := by
  intro R z
  rfl

theorem rotationCompatible_mul (c : ℂ) : RotationCompatible (fun z => c * z) := by
  intro R z
  -- Commutativity of `ℂ` multiplication.
  simp only [ComplexNucleus.action]
  ring

theorem rotationCompatible_comp {f g : ℂ → ℂ}
    (hf : RotationCompatible f) (hg : RotationCompatible g) :
    RotationCompatible (f ∘ g) := by
  intro R z
  simp [Function.comp, hf R (g z), hg R z]

end Complex
end HeytingLean

