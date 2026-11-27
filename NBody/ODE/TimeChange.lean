module

public import NBody.ODE.Solution

@[expose] public section

namespace NBody

noncomputable section

/-- The vector field induced on a new parameter when physical time has
derivative `1 / g`. The nonvanishing condition is stated in the theorem, not
baked into this totalized definition. -/
def timeChangedField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (X : E → E) (x : E) : E := (g x)⁻¹ • X x

/-- Transport a classical solution through a differentiable increasing time
change `dt/dτ = 1/g`; positivity guarantees the physical-time map has nonzero
derivative. -/
theorem SolutionOn.timeChange {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ω : Set E} {X : E → E} {z : ℝ → E} {I J : Set ℝ}
    (h : SolutionOn Ω X z I) (hJ : IsOpen J) (θ : ℝ → ℝ)
    (hmap : ∀ τ ∈ J, θ τ ∈ I) (g : E → ℝ)
    (_hg : ∀ τ ∈ J, 0 < g (z (θ τ)))
    (hθ : ∀ τ ∈ J,
      HasDerivAt θ ((g (z (θ τ)))⁻¹) τ) :
    SolutionOn Ω (timeChangedField g X) (fun τ => z (θ τ)) J := by
  refine ⟨hJ, ?_⟩
  intro τ hτ
  have hstate := h.2 (θ τ) (hmap τ hτ)
  refine ⟨hstate.1, ?_⟩
  have hcomp := hstate.2.scomp τ (hθ τ hτ)
  simpa [timeChangedField, Function.comp_def] using hcomp

end

end NBody
