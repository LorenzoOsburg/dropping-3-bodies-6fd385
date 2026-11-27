module

public import NBody.Potential.InversePower
public import NBody.Singularities.Endpoints

@[expose] public section

namespace NBody

/-- A labelled binary tree describing a hierarchical cluster decomposition. -/
inductive ClusterTree (ι : Type*) where
  | leaf : ι → ClusterTree ι
  | join : ClusterTree ι → ClusterTree ι → ClusterTree ι
  deriving DecidableEq, Repr

/-- The set of particle labels represented by a cluster tree. -/
def ClusterTree.labels {ι : Type*} [DecidableEq ι] : ClusterTree ι → Finset ι
  | .leaf i => {i}
  | .join left right => left.labels ∪ right.labels

/-- Branches of every binary merge represent disjoint sets of labels. -/
def ClusterTree.WellFormed {ι : Type*} [DecidableEq ι] : ClusterTree ι → Prop
  | .leaf _ => True
  | .join left right => left.WellFormed ∧ right.WellFormed ∧
      Disjoint left.labels right.labels

/-- A fixed cluster is collapsing when all of its distinct members share one
position. -/
def ClusterCollapsed {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (S : Finset ι) (q : Config ι d) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → q i = q j

/-- A cluster stays uniformly separated from its complement. -/
def ClusterSeparatedFromComplement {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (S : Finset ι) (q : Config ι d) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ i ∈ S, ∀ j ∉ S, δ ≤ dist (q i) (q j)

/-- Uniform cluster separation rules out a collision between the cluster and
its complement. -/
theorem cluster_separated_implies_no_cross_collision
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    {S : Finset ι} {q : Config ι d} {δ : ℝ}
    (hsep : ClusterSeparatedFromComplement S q δ)
    {i j : ι} (hi : i ∈ S) (hj : j ∉ S) : q i ≠ q j := by
  intro heq
  have hdist := hsep.2 i hi j hj
  rw [heq, dist_self] at hdist
  linarith [hsep.1]

end NBody
