module

public import Dropping3Bodies.Geometry.SideOrderClassification
public import Dropping3Bodies.Dynamics.FirstSyzygyPlacement
public import Dropping3Bodies.EqualMass.GeneralIsoscelesException
public import Dropping3Bodies.EqualMass.EquilateralMaximalEndpoint
public import Dropping3Bodies.Geometry.ScaleneSideSelection

@[expose] public section

/-! Exhaustive side-order dispatch for equal-mass zero-velocity starts. -/

namespace DroppingThreeBodies

open Filter
open scoped Topology

noncomputable section

private def baseEndpointPerm (i : Fin 3) : Equiv.Perm (Fin 3) :=
  match i with
  | 0 => Equiv.swap 0 2
  | 1 => Equiv.swap 1 2
  | _ => Equiv.swap 0 1

private theorem baseEndpointPerm_spec (i : Fin 3) :
    baseEndpointPerm i 0 = cyclicPrev i ∧
    baseEndpointPerm i 1 = cyclicNext i ∧
    baseEndpointPerm i 2 = i := by
  fin_cases i <;> decide

private theorem dist_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  nlinarith [sq_nonneg (a - b)]

/-- Every collision-free, noncollinear equal-mass rest start falls into one of
three side-order regimes. Strictly longest opposite side gives a first regular
syzygy with that body between the others. Equal sides give the actual maximal
homothetic collapse. Two equal longest sides give the isosceles collision
exception, with positive finite maximal forward extent and the base pair
collapsing at its endpoint. -/
theorem equalMass_maximal_sideOrder_classification
    (q : Fin 3 → Point) (hcf : CollisionFree q)
    (harea : signedDoubleArea q ≠ 0) :
    (∃ i T, T ∈ maximalNewtonUnionDomain (q, fun _ : Fin 3 => (0 : Point)) ∧
      0 < T ∧
      FirstRegularSyzygy
        (maximalNewtonUnionTrajectory (q, fun _ : Fin 3 => (0 : Point)))
        (maximalNewtonUnionDomain (q, fun _ : Fin 3 => (0 : Point))) 0 T ∧
      Sbtw ℝ
        ((maximalNewtonUnionTrajectory (q, fun _ : Fin 3 => (0 : Point)) T).1
          (cyclicPrev i))
        ((maximalNewtonUnionTrajectory (q, fun _ : Fin 3 => (0 : Point)) T).1 i)
        ((maximalNewtonUnionTrajectory (q, fun _ : Fin 3 => (0 : Point)) T).1
          (cyclicNext i))) ∨
    (∃ (K : ℝ), let T := homotheticCollapseTime K
      0 < T ∧
      (∀ t, 0 ≤ t → (t ∈ maximalNewtonUnionDomain
        (q, fun _ : Fin 3 => (0 : Point)) ↔ t < T)) ∧
      (∀ t, 0 ≤ t → t < T → signedDoubleArea
        (maximalNewtonUnionTrajectory (q, fun _ : Fin 3 => (0 : Point)) t).1 ≠ 0) ∧
      (∀ i j : Fin 3, Tendsto
        (fun t => dist ((maximalNewtonUnionTrajectory
          (q, fun _ : Fin 3 => (0 : Point)) t).1 i)
          ((maximalNewtonUnionTrajectory
            (q, fun _ : Fin 3 => (0 : Point)) t).1 j))
        (𝓝[<] T) (𝓝 0))) ∨
    (∃ i, sideSq q i < sideSq q (cyclicPrev i) ∧
      sideSq q i < sideSq q (cyclicNext i) ∧
      sideSq q (cyclicPrev i) = sideSq q (cyclicNext i) ∧
      (∀ t ∈ maximalNewtonUnionDomain
        (q, fun _ : Fin 3 => (0 : Point)), 0 ≤ t →
        signedDoubleArea
          (maximalNewtonUnionTrajectory (q, fun _ : Fin 3 => (0 : Point)) t).1 ≠ 0) ∧
      0 < sSup (maximalNewtonUnionDomain (q, fun _ : Fin 3 => (0 : Point))) ∧
      sSup (maximalNewtonUnionDomain (q, fun _ : Fin 3 => (0 : Point))) ≤
        Real.sqrt (8 * (dist (q (cyclicPrev i)) (q (cyclicNext i)) / 2) ^ 3) ∧
      Tendsto
        (fun t => dist ((maximalNewtonUnionTrajectory
          (q, fun _ : Fin 3 => (0 : Point)) t).1 (cyclicPrev i))
          ((maximalNewtonUnionTrajectory
            (q, fun _ : Fin 3 => (0 : Point)) t).1 (cyclicNext i)))
        (nhdsWithin (sSup (maximalNewtonUnionDomain
          (q, fun _ : Fin 3 => (0 : Point))))
          (Set.Iio (sSup (maximalNewtonUnionDomain
            (q, fun _ : Fin 3 => (0 : Point)))))) (𝓝 0)) := by
  let s : Fin 3 → ℝ := fun i => sideSq q i
  obtain hmax | hall | hbase := sideValue_order_trichotomy s
  · obtain ⟨i, hip, hin⟩ := hmax
    left
    obtain ⟨T, hT, hTpos, hfirst, hbetween⟩ :=
      maximalNewtonUnion_firstRegularSyzygy_middleBody_of_strictLongest
        (q, fun _ : Fin 3 => (0 : Point)) hcf (by intro j; rfl) harea i
        (by simpa [s] using hip) (by simpa [s] using hin)
    exact ⟨i, T, hT, hTpos, hfirst, hbetween⟩
  · have heq := hall
    right
    left
    let d := dist (q 0) (q 1)
    have hd : 0 < d := dist_pos.mpr (by
      intro h
      have hc := (collisionFree_iff_dist_pos q).mp hcf 0 1 (by decide)
      rw [h] at hc
      simp at hc)
    have h01 : dist (q 0) (q 1) = d := rfl
    have h02 : dist (q 0) (q 2) = d := by
      apply dist_eq_of_sq_eq dist_nonneg dist_nonneg

      have h0 : sideSq q 2 = dist (q 1) (q 0) ^ 2 := by
        simpa [cyclicPrev, cyclicNext] using
          (sideSq_eq_cyclicNeighborDistance q (2 : Fin 3))
      have h1 : sideSq q 1 = dist (q 0) (q 2) ^ 2 := by
        simpa [cyclicPrev, cyclicNext] using
          (sideSq_eq_cyclicNeighborDistance q (1 : Fin 3))
      rw [← h1, dist_comm (q 0) (q 1), ← h0]
      simpa [s] using heq 1 2
    have h12 : dist (q 1) (q 2) = d := by
      apply dist_eq_of_sq_eq dist_nonneg dist_nonneg
      have h0 : sideSq q 2 = dist (q 1) (q 0) ^ 2 := by
        simpa [cyclicPrev, cyclicNext] using
          (sideSq_eq_cyclicNeighborDistance q (2 : Fin 3))
      have h1 : sideSq q 0 = dist (q 2) (q 1) ^ 2 := by
        simpa [cyclicPrev, cyclicNext] using
          (sideSq_eq_cyclicNeighborDistance q (0 : Fin 3))
      rw [dist_comm (q 1) (q 2), ← h1, dist_comm (q 0) (q 1), ← h0]
      simpa [s] using heq 0 2
    obtain ⟨K, hK, hphase, hdomain, hareaT, hcollapse⟩ :=
      exists_equilateral_maximal_drop q d hd h01 h02 h12
    let T := homotheticCollapseTime K
    have hTpos : 0 < T := by
      change 0 < homotheticCollapseTime K
      exact mul_pos hK (by positivity)
    refine ⟨K, ?_⟩
    simpa [T] using And.intro hTpos (And.intro hdomain (And.intro hareaT hcollapse))
  · obtain ⟨i, hi, hp, heq⟩ := hbase
    right
    right
    let σ := baseEndpointPerm i
    have hσ := baseEndpointPerm_spec i
    have hbaseDist : q (cyclicPrev i) ≠ q (cyclicNext i) := by
      intro h
      have hc := (collisionFree_iff_dist_pos q).mp hcf
        (cyclicPrev i) (cyclicNext i) (cyclicPrev_ne_cyclicNext i)
      rw [h] at hc
      simp at hc
    have hprevSq : sideSq q (cyclicPrev i) =
        dist (q (cyclicNext i)) (q i) ^ 2 := by
      rw [sideSq_eq_cyclicNeighborDistance]
      rw [cyclicPrev_cyclicPrev, cyclicNext_cyclicPrev]
    have hnextSq : sideSq q (cyclicNext i) =
        dist (q (cyclicPrev i)) (q i) ^ 2 := by
      rw [sideSq_eq_cyclicNeighborDistance]
      rw [cyclicPrev_cyclicNext, cyclicNext_cyclicNext, dist_comm]
    have hlegs : dist (q (cyclicPrev i)) (q i) =
        dist (q (cyclicNext i)) (q i) := by
      apply dist_eq_of_sq_eq dist_nonneg dist_nonneg
      rw [← hnextSq, ← hprevSq]
      exact heq.symm
    have hlong : dist (q (cyclicPrev i)) (q i) >
        dist (q (cyclicPrev i)) (q (cyclicNext i)) := by
      apply (sq_lt_sq₀ dist_nonneg dist_nonneg).mp
      have hiBase : sideSq q i =
          dist (q (cyclicPrev i)) (q (cyclicNext i)) ^ 2 :=
        sideSq_eq_cyclicNeighborDistance q i
      rw [← hiBase, ← hnextSq]
      exact hp
    rcases hσ with ⟨hσ0, hσ1, hσ2⟩
    have hresult := maximalNewtonUnion_general_isosceles_no_forward_syzygy
      (q, fun _ : Fin 3 => (0 : Point)) hcf (by intro j; rfl) σ
      (by simpa [σ, hσ0, hσ1] using hbaseDist) (by simpa [σ, hσ0, hσ1, hσ2] using hlegs)
      (by simpa [σ, hσ0, hσ1, hσ2] using hlong)
    rcases hresult with ⟨hno, ⟨hpos, hbound⟩, hcollapse⟩
    refine ⟨i, ?_, ?_, ?_, ?_, hpos, ?_, ?_⟩
    · simpa [s] using hi
    · simpa [s] using hp
    · simpa [s] using heq
    · simpa using hno
    · simpa [σ, hσ0, hσ1] using hbound
    · simpa [σ, hσ0, hσ1] using hcollapse

end

end DroppingThreeBodies
