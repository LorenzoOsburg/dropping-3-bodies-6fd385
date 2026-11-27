module

public import NBody.ODE.Solution

@[expose] public section

namespace NBody

/-! The derivative transport below uses the vector-valued chain rule
`HasDerivAt.scomp` from `Mathlib.Analysis.Calculus.Deriv.Comp`. -/

/-- Translate the time parameter of a solution and its open time domain. -/
theorem SolutionOn.timeShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} {X : E → E} {z : ℝ → E} {I : Set ℝ} (h : SolutionOn Ω X z I)
    (c : ℝ) :
    SolutionOn Ω X (fun t => z (t + c)) ((fun t : ℝ => t + c) ⁻¹' I) := by
  refine ⟨h.1.preimage (continuous_id.add continuous_const), ?_⟩
  intro t ht
  have hzt := h.2 (t + c) ht
  refine ⟨hzt.1, ?_⟩
  simpa [Function.comp_def] using
    hzt.2.scomp t ((hasDerivAt_id t).add_const c)

/-- Translate a state-space solution when the domain and vector field are
invariant under a fixed additive shift. -/
theorem SolutionOn.translateBy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ω : Set E} {X : E → E} {z : ℝ → E} {I : Set ℝ}
    (h : SolutionOn Ω X z I) (c : E)
    (hDomain : ∀ x, x ∈ Ω → x + c ∈ Ω)
    (hField : ∀ x, x ∈ Ω → X (x + c) = X x) :
    SolutionOn Ω X (fun t => z t + c) I := by
  refine ⟨h.1, fun t ht => ?_⟩
  obtain ⟨hzΩ, hz'⟩ := h.2 t ht
  refine ⟨hDomain (z t) hzΩ, ?_⟩
  simpa [hField (z t) hzΩ] using hz'.const_add c

end NBody
