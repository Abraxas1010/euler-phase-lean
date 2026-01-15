import HeytingLean.Complex.AnalyticMaps
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace HeytingLean
namespace Complex

open scoped Real

open MeasureTheory

/-!
# Contour integrals (circle) + Cauchy formula re-exports

This module focuses on **circle integrals** (`∮ z in C(c,R), ...`) which are already supported
by Mathlib, and records a minimal “winding number” proxy for circles:

* `circleWindingNumber c R w = 1` if `w ∈ ball c R`, else `0`.

General winding numbers for arbitrary loops are not implemented here (and are not currently
provided under the name `windingNumber` in this project’s pinned Mathlib snapshot).
-/

/-- Re-export: circle integral from Mathlib. -/
noncomputable def circleIntegral (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℂ :=
  ∮ z in C(c, R), f z

/-- The unit circle centered at the origin. -/
def unitCircle : Set ℂ := Metric.sphere 0 1

/-- A circle-only "winding number": `1` if the point lies inside the circle, else `0`. -/
noncomputable def circleWindingNumber (c : ℂ) (R : ℝ) (w : ℂ) : ℤ :=
  by
    classical
    exact if w ∈ Metric.ball c R then 1 else 0

@[simp] lemma circleWindingNumber_of_mem {c w : ℂ} {R : ℝ} (hw : w ∈ Metric.ball c R) :
    circleWindingNumber c R w = 1 := by
  classical
  simp [circleWindingNumber, hw]

@[simp] lemma circleWindingNumber_of_not_mem {c w : ℂ} {R : ℝ} (hw : w ∉ Metric.ball c R) :
    circleWindingNumber c R w = 0 := by
  classical
  simp [circleWindingNumber, hw]

/-- Cauchy integral formula (circle): `∮ f(z)/(z-w) dz = 2π i f(w)` under `DifferentiableOn`. -/
theorem circleIntegral_div_sub_of_differentiableOn
    {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (Metric.closedBall c R))
    (hw : w ∈ Metric.ball c R) :
    (∮ z in C(c, R), f z / (z - w)) = 2 * Real.pi * Complex.I * f w := by
  -- Mathlib’s lemma is stated with scalar multiplication `•`.
  simpa [smul_eq_mul, div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm] using
    (_root_.DifferentiableOn.circleIntegral_sub_inv_smul (E := ℂ) (R := R) (c := c) (w := w)
      (f := f) hd hw)

/-- A rearranged form of the Cauchy integral formula solving for `f(w)`. -/
theorem cauchyValue_eq_inv_two_pi_I_mul_circleIntegral
    {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (Metric.closedBall c R))
    (hw : w ∈ Metric.ball c R) :
    f w = (2 * Real.pi * Complex.I : ℂ)⁻¹ * (∮ z in C(c, R), f z / (z - w)) := by
  have h := circleIntegral_div_sub_of_differentiableOn (R := R) (c := c) (w := w) (f := f) hd hw
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
      -- `2π ≠ 0` in `ℂ`.
      exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
    exact mul_ne_zero h2pi Complex.I_ne_zero
  have hmul : (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (∮ z in C(c, R), f z / (z - w)) = f w := by
    calc
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * (∮ z in C(c, R), f z / (z - w))
          = (2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I * f w) := by
              simp [h]
      _ = f w := by
              -- `a⁻¹ * (a * b) = b` for `a ≠ 0`.
              simpa [mul_assoc] using inv_mul_cancel_left₀ hne (f w)
  exact hmul.symm

/-- Trivial “well-definedness” lemma: the circle-only winding number yields an integer. -/
theorem circleWindingNumber_wellDefined (c : ℂ) (R : ℝ) (w : ℂ) :
    ∃ n : ℤ, circleWindingNumber c R w = n := by
  exact ⟨circleWindingNumber c R w, rfl⟩

end Complex
end HeytingLean
