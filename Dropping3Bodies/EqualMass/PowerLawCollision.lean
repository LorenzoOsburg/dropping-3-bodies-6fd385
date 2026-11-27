module

public import Dropping3Bodies.EqualMass.PowerLawComparison
public import Dropping3Bodies.EqualMass.PowerLawGeometry
public import Dropping3Bodies.EqualMass.PowerLawEnergy

@[expose] public section

namespace DroppingThreeBodies.CentralForce

open Set
noncomputable section

/-- The labeled ordering persists at every point of an initially noncollinear segment. -/
theorem power_order_on_segment {α g m a t : ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hs : EqualPowerSolution α g m z I) (hα : 0 < α) (hg : 0 < g) (hm : 0 < m)
    (hc : IsPreconnected I) (hat : a ≤ t) (hseg : Icc a t ⊆ I)
    (hrest : ∀ j, (z a).2 j = 0)
    (harea : ∀ u ∈ Icc a t, 0 < signedDoubleArea (z a).1 * signedDoubleArea (z u).1)
    (h01 : sideSq (z a).1 1 < sideSq (z a).1 0) (h12 : sideSq (z a).1 2 < sideSq (z a).1 1) :
    sideSq (z t).1 1 < sideSq (z t).1 0 ∧ sideSq (z t).1 2 < sideSq (z t).1 1 := by
  have gaps := (positive_gaps_iff_side_order _).2 ⟨h01, h12⟩
  have positive (i : Fin 3) (hi : 0 < sideGap (z a).1 i) : 0 < sideGap (z t).1 i :=
    pos_of_mul_pos_right
      ((power_gap_comparison hs hα hg hm hc hat hseg hrest harea i hi.ne').1 t ⟨hat, le_rfl⟩)
      hi.le
  exact (positive_gaps_iff_side_order _).1 ⟨positive 2 gaps.1, positive 0 gaps.2⟩

/-- For subcritical potentials the shortest pair carries uniformly positive
absolute angular momentum after any positive elapsed time. Energy then gives
one positive lower bound for all three distances. -/
theorem power_subcritical_separation {α g m a b T : ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hs : EqualPowerSolution α g m z I) (hα : 0 < α) (hα2 : α < 2)
    (hg : 0 < g) (hm : 0 < m) (hc : IsPreconnected I)
    (hab : a < b) (hbT : b < T) (hseg : Ico a T ⊆ I)
    (hrest : ∀ j, (z a).2 j = 0)
    (harea : ∀ t ∈ Ico a T, 0 < signedDoubleArea (z a).1 * signedDoubleArea (z t).1)
    (h01 : sideSq (z a).1 1 < sideSq (z a).1 0) (h12 : sideSq (z a).1 2 < sideSq (z a).1 1) :
    ∃ δ > 0, ∀ t ∈ Ico b T, ∀ i j : Fin 3, i ≠ j → δ ≤ dist ((z t).1 i) ((z t).1 j) := by
  have haI := hseg (show a ∈ Ico a T from ⟨le_rfl, hab.trans hbT⟩)
  have gap := ((positive_gaps_iff_side_order _).2 ⟨h01, h12⟩).1
  have subseg (u) (hu : u ∈ Ico a T) : Icc a u ⊆ Ico a T :=
    fun s h => ⟨h.1, h.2.trans_lt hu.2⟩
  have comp (u) (hu : u ∈ Ico a T) := power_gap_comparison hs hα hg hm hc hu.1
    ((subseg u hu).trans hseg) hrest (fun s h => harea s (subseg u hu h)) 2 gap.ne'
  let k := |powerPairRotation z 2 b|
  have hk : 0 < k := by
    apply abs_pos.mpr
    exact right_ne_zero_of_mul ((comp b ⟨hab.le, hbT⟩).2.2 b ⟨hab, le_rfl⟩).ne'
  refine ⟨(k ^ 2 * m / (12 * g)) ^ (2 - α)⁻¹, Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro t ht i j hij
  have ht' : t ∈ Ico a T := ⟨hab.le.trans ht.1, ht.2⟩
  have horder := power_order_on_segment hs hα hg hm hc ht'.1 ((subseg t ht').trans hseg)
    hrest (fun s h => harea s (subseg t ht' h)) h01 h12
  have hshort := shortest_distance_of_side_order horder
  have hk' : k ≤ |powerPairRotation z 2 t| :=
    (comp t ht').2.1.monotoneOn ⟨hab.le, ht.1⟩ ⟨ht'.1, le_rfl⟩ ht.1
  have hsq : k ^ 2 ≤ cross (sideVector (z t).1 2) (sideVector (z t).2 2) ^ 2 := by
    calc
      _ ≤ |powerPairRotation z 2 t| ^ 2 := (sq_le_sq₀ hk.le (abs_nonneg _)).2 hk'
      _ = _ := sq_abs _
  exact (power_subcritical_distance_bound hs hα hα2 hg hm hc haI (hseg ht') hrest
    hshort hsq).trans (hshort i j hij)

end
end DroppingThreeBodies.CentralForce
