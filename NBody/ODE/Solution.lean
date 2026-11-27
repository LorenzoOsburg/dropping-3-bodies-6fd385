module

public import Mathlib.Analysis.ODE.ExistUnique
public import PrincipiaThreeBodies.Definitions

@[expose] public section

namespace NBody

/-- Restrict a solution to an open subset of its time domain. -/
theorem SolutionOn.restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} {X : E → E} {z : ℝ → E} {I J : Set ℝ}
    (h : SolutionOn Ω X z I) (hJ : IsOpen J) (hJI : J ⊆ I) :
    SolutionOn Ω X z J := by
  refine ⟨hJ, fun t ht => h.2 t (hJI ht)⟩

/-- An initial-value problem packages a solution and its specified initial state. -/
structure InitialValueProblem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (X : E → E) (z : ℝ → E) (I : Set ℝ) (a : ℝ) (z₀ : E) : Prop where
  solution : SolutionOn Ω X z I
  initial_mem : a ∈ I
  initial_eq : z a = z₀

/-- Uniqueness on a compact time segment under a uniform Lipschitz bound on the
state domain. This specializes Mathlib.Analysis.ODE.ExistUnique.
ODE_solution_unique_of_mem_Icc_right to an autonomous field. -/
theorem solutions_eqOn_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} {X : E → E} {z w : ℝ → E} {I : Set ℝ} {a b : ℝ} {K : NNReal}
    (hLip : LipschitzOnWith K X Ω)
    (hz : SolutionOn Ω X z I) (hw : SolutionOn Ω X w I)
    (hI : Set.Icc a b ⊆ I) (_hab : a ≤ b) (hinit : z a = w a) :
    Set.EqOn z w (Set.Icc a b) := by
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => X) (s := fun _ => Ω) (K := K)
  · intro t ht
    exact hLip
  · apply HasDerivAt.continuousOn
    intro t ht
    exact (hz.2 t (hI ht)).2
  · intro t ht
    exact ((hz.2 t (hI (Set.Ico_subset_Icc_self ht))).2).hasDerivWithinAt
  · intro t ht
    exact (hz.2 t (hI (Set.Ico_subset_Icc_self ht))).1
  · apply HasDerivAt.continuousOn
    intro t ht
    exact (hw.2 t (hI ht)).2
  · intro t ht
    exact ((hw.2 t (hI (Set.Ico_subset_Icc_self ht))).2).hasDerivWithinAt
  · intro t ht
    exact (hw.2 t (hI (Set.Ico_subset_Icc_self ht))).1
  · exact hinit

end NBody
