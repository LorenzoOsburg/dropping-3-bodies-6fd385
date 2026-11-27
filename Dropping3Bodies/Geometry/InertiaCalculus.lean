module

public import Dropping3Bodies.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open scoped Topology RealInnerProductSpace

namespace DroppingThreeBodies

noncomputable section

/-- The mass-weighted moment of three position curves about the origin. -/
def massMomentCurve (m : Fin 3 → ℝ) (q : Fin 3 → ℝ → Point) (t : ℝ) : ℝ :=
  massMoment m (fun i => q i t)

/-- Its expected derivative, written body by body. -/
def massMomentRate (m : Fin 3 → ℝ) (q : Fin 3 → ℝ → Point)
    (v : Fin 3 → Point) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, m i * (2 * inner ℝ (q i t) (v i))

/-- D3B-F02; PAPER-20261029 `eq:Im`; derivative of the mass moment for
    arbitrary real mass weights. No sign or equal-mass assumption is used. -/
theorem hasDerivAt_massMomentCurve
    (m : Fin 3 → ℝ) {q : Fin 3 → ℝ → Point} {v : Fin 3 → Point} {t : ℝ}
    (hq : ∀ i, HasDerivAt (fun τ => q i τ) (v i) t) :
    HasDerivAt (massMomentCurve m q)
      (massMomentRate m q v t) t := by
  have h0 : HasDerivAt (fun τ => m 0 * ‖q 0 τ‖ ^ 2)
      (m 0 * (2 * inner ℝ (q 0 t) (v 0))) t :=
    HasDerivAt.const_mul (m 0) ((hq 0).norm_sq)
  have h1 : HasDerivAt (fun τ => m 1 * ‖q 1 τ‖ ^ 2)
      (m 1 * (2 * inner ℝ (q 1 t) (v 1))) t :=
    HasDerivAt.const_mul (m 1) ((hq 1).norm_sq)
  have h2 : HasDerivAt (fun τ => m 2 * ‖q 2 τ‖ ^ 2)
      (m 2 * (2 * inner ℝ (q 2 t) (v 2))) t :=
    HasDerivAt.const_mul (m 2) ((hq 2).norm_sq)
  have hs := HasDerivAt.add h0 (HasDerivAt.add h1 h2)
  have hfun : massMomentCurve m q =ᶠ[𝓝 t]
      ((fun τ => m 0 * ‖q 0 τ‖ ^ 2) +
        ((fun τ => m 1 * ‖q 1 τ‖ ^ 2) + (fun τ => m 2 * ‖q 2 τ‖ ^ 2))) := by
    filter_upwards [] with τ
    simp [massMomentCurve, massMoment, Fin.sum_univ_succ]
  simpa [massMomentRate, Fin.sum_univ_succ] using
    hs.congr_of_eventuallyEq hfun

end

end DroppingThreeBodies