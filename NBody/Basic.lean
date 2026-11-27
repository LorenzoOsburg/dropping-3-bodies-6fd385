module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Separation.Basic
public import PrincipiaThreeBodies.Definitions

@[expose] public section

namespace NBody

noncomputable section

/-- Physical sign assumptions, kept separate from algebraic identities. -/
def PhysicalParameters {ι : Type*} (G : ℝ) (m : ι → ℝ) : Prop :=
  0 < G ∧ ∀ i, 0 < m i

theorem collisionFree_iff_pairwise_dist_pos {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (q : Config ι d) :
    CollisionFree q ↔ ∀ i j, i ≠ j → 0 < dist (q i) (q j) := by
  constructor
  · intro h i j hij
    exact dist_pos.mpr (h i j hij)
  · intro h i j hij
    exact dist_pos.mp (h i j hij)

theorem isOpen_regularPhaseSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) : IsOpen (regularPhaseSet ι d) := by
  classical
  let pairCondition : (ι × ι) → Set (Phase ι d) := fun ij =>
    {z | ij.1 = ij.2 ∨ z.1 ij.1 ≠ z.1 ij.2}
  have hopen : IsOpen (⋂ ij : ι × ι, pairCondition ij) :=
    isOpen_iInter_of_finite fun ij => by
      by_cases hij : ij.1 = ij.2
      · simp [pairCondition, hij]
      · simp only [pairCondition, hij, false_or]
        exact isOpen_ne_fun
          ((continuous_apply ij.1).comp continuous_fst)
          ((continuous_apply ij.2).comp continuous_fst)
  have heq : regularPhaseSet ι d = ⋂ ij : ι × ι, pairCondition ij := by
    ext z
    simp only [regularPhaseSet, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hz ij
      by_cases hij : ij.1 = ij.2
      · exact Or.inl hij
      · exact Or.inr (hz ij.1 ij.2 hij)
    · intro hz i j hij
      exact (hz (i, j)).resolve_left hij
  rw [heq]
  exact hopen

end

end NBody
