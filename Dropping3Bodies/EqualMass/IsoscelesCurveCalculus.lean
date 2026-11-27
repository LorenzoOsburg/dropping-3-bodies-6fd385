module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

@[expose] public section

/-!
# Scalar curve calculus for the isosceles bootstrap

These rules are independent of Newton's equation. They expose the exact
Wronskian and quotient derivatives needed by a later trajectory argument.
-/

namespace DroppingThreeBodies

noncomputable section

/-- `x*z' - z*x'`, with the derivative curves passed explicitly. -/
def scalarWronskianCurve (x xdot z zdot : ℝ → ℝ) (t : ℝ) : ℝ :=
  x t * zdot t - z t * xdot t

/-- The ratio `z/x`, defined wherever the denominator is nonzero. -/
def scalarRatioCurve (x z : ℝ → ℝ) (t : ℝ) : ℝ :=
  z t / x t

/-- Product-rule derivative of the scalar Wronskian. -/
theorem hasDerivAt_scalarWronskianCurve
    (x xdot xddot z zdot zddot : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (xdot t) t)
    (hxdot : HasDerivAt xdot (xddot t) t)
    (hz : HasDerivAt z (zdot t) t)
    (hzdot : HasDerivAt zdot (zddot t) t) :
    HasDerivAt (fun s => scalarWronskianCurve x xdot z zdot s)
      (x t * zddot t - z t * xddot t) t := by
  have hleft := hx.mul hzdot
  have hright := hz.mul hxdot
  have h := hleft.sub hright
  have hder : HasDerivAt (fun s => x s * zdot s - z s * xdot s)
      (x t * zddot t - z t * xddot t) t :=
    h.congr_deriv (by ring)
  change HasDerivAt (fun s => x s * zdot s - z s * xdot s)
    (x t * zddot t - z t * xddot t) t
  exact hder

/-- Quotient-rule derivative of `z/x`, expressed as the Wronskian divided
    by `x^2`. -/
theorem hasDerivAt_scalarRatioCurve
    (x xdot z zdot : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (xdot t) t)
    (hz : HasDerivAt z (zdot t) t) (hxt : x t ≠ 0) :
    HasDerivAt (scalarRatioCurve x z)
      (scalarWronskianCurve x xdot z zdot t / (x t) ^ 2) t := by
  have hquot := hz.div hx hxt
  have hder : HasDerivAt (fun s => z s / x s)
      (scalarWronskianCurve x xdot z zdot t / (x t) ^ 2) t :=
    hquot.congr_deriv (by simp [scalarWronskianCurve]; ring)
  change HasDerivAt (fun s => z s / x s)
    (scalarWronskianCurve x xdot z zdot t / (x t) ^ 2) t
  exact hder

end

end DroppingThreeBodies
