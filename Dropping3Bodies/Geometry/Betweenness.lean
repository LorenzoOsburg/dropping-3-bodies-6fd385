module

public import Dropping3Bodies.Geometry.Coordinates
public import Dropping3Bodies.Geometry.SyzygyMidpoint
public import Dropping3Bodies.Geometry.BodyIndex
public import Mathlib.Analysis.Convex.StrictConvexBetween

@[expose] public section

/-! A collinear positive path-angle criterion implies strict betweenness. -/

namespace DroppingThreeBodies

theorem sbtw_of_cross_path_eq_zero_of_dot_path_pos
    (a b c : Point)
    (hcross : cross (b - a) (c - b) = 0)
    (hdot : 0 < dot2 (b - a) (c - b))
    (hab : a ≠ b) (hbc : b ≠ c) :
    Sbtw ℝ a b c := by
  let u : Point := b - a
  let v : Point := c - b
  have hcross' : cross u v = 0 := by simpa [u, v] using hcross
  have hdot' : 0 < dot2 u v := by simpa [u, v] using hdot
  have hdotSq : dot2 u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    have h := cross_sq_add_dot2_sq u v
    rw [hcross'] at h
    nlinarith
  have hdotNorm : dot2 u v = ‖u‖ * ‖v‖ := by
    have hu : 0 ≤ ‖u‖ := norm_nonneg _
    have hv : 0 ≤ ‖v‖ := norm_nonneg _
    have hprod : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg hu hv
    nlinarith [hdotSq]
  have hnormSq : ‖u + v‖ ^ 2 = (‖u‖ + ‖v‖) ^ 2 := by
    have hdotAdd : dot2 (u + v) (u + v) =
        dot2 u u + dot2 v v + 2 * dot2 u v := by
      simp [dot2]
      ring
    calc
      ‖u + v‖ ^ 2 = dot2 (u + v) (u + v) := norm_sq_eq_dot2 (u + v)
      _ = dot2 u u + dot2 v v + 2 * dot2 u v := hdotAdd
      _ = ‖u‖ ^ 2 + ‖v‖ ^ 2 + 2 * (‖u‖ * ‖v‖) := by
        rw [← norm_sq_eq_dot2 u, ← norm_sq_eq_dot2 v, hdotNorm]
      _ = (‖u‖ + ‖v‖) ^ 2 := by
        ring
  have hnorm : ‖u + v‖ = ‖u‖ + ‖v‖ := by
    have hleft : 0 ≤ ‖u + v‖ := norm_nonneg _
    have hright : 0 ≤ ‖u‖ + ‖v‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [hnormSq]
  have hsame : SameRay ℝ u v := sameRay_iff_norm_add.mpr hnorm
  have hwbtw : Wbtw ℝ a b c := by
    apply wbtw_iff_sameRay_vsub.mpr
    simpa [u, v] using hsame
  exact ⟨hwbtw, hab.symm, hbc⟩

/-- If the signed area vanishes, two distinct endpoints and a positive
    consecutive path dot product put the middle point strictly between them. -/
theorem sbtw_of_collinear_of_path_dot_pos
    (a b c : Point)
    (hcross : cross (b - a) (c - b) = 0)
    (hdot : 0 < dot2 (b - a) (c - b))
    (hab : a ≠ b) (hbc : b ≠ c) :
    Sbtw ℝ a b c :=
  sbtw_of_cross_path_eq_zero_of_dot_path_pos a b c hcross hdot hab hbc

/-- Apply the path criterion to three distinct vertices of a configuration
    whose signed double area vanishes. -/
theorem sbtw_configuration_of_path_dot_pos
    (q : Fin 3 → Point) (i j k : Fin 3)
    (harea : signedDoubleArea q = 0)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hdistinct : ∀ m n, m ≠ n → q m ≠ q n)
    (hdot : 0 < dot2 (q i - q j) (q k - q i)) :
    Sbtw ℝ (q j) (q i) (q k) := by
  have hcross : cross (q i - q j) (q k - q i) = 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [signedDoubleArea, cross] <;> nlinarith
  exact sbtw_of_cross_path_eq_zero_of_dot_path_pos
    (q j) (q i) (q k) hcross hdot
    (hdistinct j i hij.symm) (hdistinct i k hki.symm)

/-- At a collision-free collinear configuration, a weakly longest opposite
    side puts its body in the open segment between the other two bodies. -/
theorem sbtw_of_longest_opposite_side
    (q : Fin 3 → Point) (i : Fin 3)
    (harea : signedDoubleArea q = 0)
    (hdistinct : ∀ j k, j ≠ k → q j ≠ q k)
    (hlongPrev : dist (q (cyclicPrev i)) (q (cyclicNext i)) ^ 2 ≥
      dist (q i) (q (cyclicPrev i)) ^ 2)
    (hlongNext : dist (q (cyclicPrev i)) (q (cyclicNext i)) ^ 2 ≥
      dist (q (cyclicNext i)) (q i) ^ 2) :
    Sbtw ℝ (q (cyclicPrev i)) (q i) (q (cyclicNext i)) := by
  have hdot := syzygy_longest_opposite_side_forces_positive_between_dot
    q i harea hdistinct hlongPrev hlongNext
  exact sbtw_configuration_of_path_dot_pos q i (cyclicPrev i) (cyclicNext i)
    harea (cyclicPrev_ne_self i).symm (cyclicPrev_ne_cyclicNext i)
    (cyclicNext_ne_self i) hdistinct hdot

end DroppingThreeBodies
