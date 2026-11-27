module

public import Dropping3Bodies.EqualMass.SideFrame
public import Dropping3Bodies.Geometry.BodyIndex

@[expose] public section

/-!
# Equal adjacent sides at a syzygy

At a collinear configuration, equal distances from one body to the other two
force that body to be their midpoint, provided the opposite side is nonzero.
The proof is expressed in the cyclic side frame used by the equal-mass
comparison argument.
-/

namespace DroppingThreeBodies

/-- Sum of the two vertices opposite the given cyclic body index. -/
def oppositePairSum (q : Fin 3 → Point) (i : Fin 3) : Point :=
  match i with
  | 0 => q 1 + q 2
  | 1 => q 2 + q 0
  | _ => q 0 + q 1

theorem sideOffset_eq_zero_of_syzygy_and_tied_gap
    (q : Fin 3 → Point) (i : Fin 3)
    (harea : signedDoubleArea q = 0)
    (hgap : sideGap q i = 0)
    (hside : sideVector q i ≠ 0) :
    sideOffset q i = 0 := by
  let r := sideVector q i
  let s := sideOffset q i
  have hcross : cross r s = 0 := by
    have h := signedDoubleArea_eq_cross_sideFrame q i
    dsimp [r, s] at h ⊢
    rw [h]
    exact harea
  have hdot : dot2 r s = 0 := by
    have h := sideGap_eq_neg_two_dot_sideFrame q i
    dsimp [r, s] at h ⊢
    rw [hgap] at h
    linarith
  have hnormproduct : ‖r‖ ^ 2 * ‖s‖ ^ 2 = 0 := by
    have h := cross_sq_add_dot2_sq r s
    rw [hcross, hdot] at h
    nlinarith
  have hrnorm : ‖r‖ ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    exact hside (norm_eq_zero.mp hzero)
  have hsnorm : ‖s‖ ^ 2 = 0 := (mul_eq_zero.mp hnormproduct).resolve_left hrnorm
  have hs : ‖s‖ = 0 := by nlinarith [sq_nonneg ‖s‖]
  have hs0 : s = 0 := norm_eq_zero.mp hs
  simpa [r, s] using hs0

theorem syzygy_tied_gap_body_is_midpoint
    (q : Fin 3 → Point) (i : Fin 3)
    (harea : signedDoubleArea q = 0)
    (hgap : sideGap q i = 0)
    (hside : sideVector q i ≠ 0) :
    q i = (1 / 2 : ℝ) • oppositePairSum q i := by
  have hOffset := sideOffset_eq_zero_of_syzygy_and_tied_gap q i harea hgap hside
  fin_cases i
  · change q 0 = (1 / 2 : ℝ) • (q 1 + q 2)
    have h₀ : q 0 - (1 / 2 : ℝ) • (q 1 + q 2) = 0 := by
      simpa [sideOffset] using hOffset
    exact sub_eq_zero.mp h₀
  · change q 1 = (1 / 2 : ℝ) • (q 2 + q 0)
    have h₁ : q 1 - (1 / 2 : ℝ) • (q 2 + q 0) = 0 := by
      simpa [sideOffset] using hOffset
    exact sub_eq_zero.mp h₁
  · change q 2 = (1 / 2 : ℝ) • (q 0 + q 1)
    have h₂ : q 2 - (1 / 2 : ℝ) • (q 0 + q 1) = 0 := by
      simpa [sideOffset] using hOffset
    exact sub_eq_zero.mp h₂

/-- In a collision-free collinear triple, if the side opposite body `0` is
    at least as long as both other sides, the two vectors from that body
    toward the opposite endpoints point in the same direction. This is a
    coordinate-free betweenness criterion for body `0`. -/
theorem syzygy_longest_opposite_side0_forces_positive_between_dot
    (q : Fin 3 → Point)
    (harea : signedDoubleArea q = 0)
    (hdistinct : ∀ i j, i ≠ j → q i ≠ q j)
    (hlong01 : dist (q 1) (q 2) ^ 2 ≥ dist (q 0) (q 1) ^ 2)
    (hlong02 : dist (q 1) (q 2) ^ 2 ≥ dist (q 2) (q 0) ^ 2) :
    0 < dot2 (q 0 - q 1) (q 2 - q 0) := by
  let u := q 0 - q 1
  let v := q 2 - q 0
  have hu : u ≠ 0 := by
    dsimp [u]
    exact sub_ne_zero.mpr (hdistinct 0 1 (by decide))
  have hv : v ≠ 0 := by
    dsimp [v]
    exact sub_ne_zero.mpr (hdistinct 2 0 (by decide))
  have hcross : cross u v = 0 := by
    have hraw : cross (q 1 - q 0) (q 2 - q 0) = 0 := by
      simpa [signedDoubleArea] using harea
    have hneg : q 1 - q 0 = -u := by dsimp [u]; abel
    have hv' : q 2 - q 0 = v := by rfl
    rw [hneg, hv'] at hraw
    dsimp [cross] at hraw ⊢
    linarith
  have hdotSq : dot2 u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    have h := cross_sq_add_dot2_sq u v
    rw [hcross] at h
    nlinarith
  have hnormU : 0 < ‖u‖ ^ 2 := by
    have hp : 0 < ‖u‖ := norm_pos_iff.mpr hu
    positivity
  have hnormV : 0 < ‖v‖ ^ 2 := by
    have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  have hsum : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 +
      2 * dot2 u v := by
    rw [norm_sq_eq_dot2 (u + v), norm_sq_eq_dot2 u, norm_sq_eq_dot2 v]
    simp [dot2]
    ring
  have hdist : dist (q 1) (q 2) ^ 2 =
      ‖u‖ ^ 2 + ‖v‖ ^ 2 + 2 * dot2 u v := by
    have hvec : q 1 - q 2 = -(u + v) := by dsimp [u, v]; abel
    rw [dist_eq_norm, hvec, norm_neg, hsum]
  have hlongU : 0 ≤ ‖v‖ ^ 2 + 2 * dot2 u v := by
    have h := hlong01
    rw [hdist, dist_eq_norm] at h
    have hvec : q 0 - q 1 = u := by rfl
    rw [hvec] at h
    nlinarith
  have hlongV : 0 ≤ ‖u‖ ^ 2 + 2 * dot2 u v := by
    have h := hlong02
    rw [hdist, dist_eq_norm] at h
    have hvec : q 2 - q 0 = v := by rfl
    rw [hvec] at h
    nlinarith
  have hdotNe : dot2 u v ≠ 0 := by
    intro hz
    rw [hz] at hdotSq
    nlinarith [mul_pos hnormU hnormV]
  have hdotPos : 0 < dot2 u v := by
    by_contra hnot
    have hneg : dot2 u v < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hdotNe
    have hprod : 0 ≤ (‖u‖ ^ 2 + 2 * dot2 u v) *
        (‖v‖ ^ 2 + 2 * dot2 u v) := mul_nonneg hlongV hlongU
    have hmulU : dot2 u v * (‖u‖ ^ 2 + 2 * dot2 u v) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) hlongV
    have hmulV : dot2 u v * (‖v‖ ^ 2 + 2 * dot2 u v) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) hlongU
    nlinarith [hdotSq]
  simpa [u, v] using hdotPos

/-- Recenter a cyclic configuration so that body `i` becomes body `0`, with
    the two other bodies in previous/next order. -/
def bodyCyclicView (q : Fin 3 → Point) (i : Fin 3) : Fin 3 → Point :=
  fun j => if j = 0 then q i else if j = 1 then q (cyclicPrev i)
    else q (cyclicNext i)

/-- The body-index independent version of the longest-opposite-side
    criterion. The dot product uses the consecutive path vectors through `i`.
    The proof reduces each finite index case to the verified body-0 lemma. -/
theorem syzygy_longest_opposite_side_forces_positive_between_dot
    (q : Fin 3 → Point) (i : Fin 3)
    (harea : signedDoubleArea q = 0)
    (hdistinct : ∀ j k, j ≠ k → q j ≠ q k)
    (hlongPrev : dist (q (cyclicPrev i)) (q (cyclicNext i)) ^ 2 ≥
      dist (q i) (q (cyclicPrev i)) ^ 2)
    (hlongNext : dist (q (cyclicPrev i)) (q (cyclicNext i)) ^ 2 ≥
      dist (q (cyclicNext i)) (q i) ^ 2) :
    0 < dot2 (q i - q (cyclicPrev i)) (q (cyclicNext i) - q i) := by
  have hviewArea : signedDoubleArea (bodyCyclicView q i) = 0 := by
    fin_cases i <;>
      simp [bodyCyclicView, signedDoubleArea, cross, cyclicPrev, cyclicNext] at * <;>
      nlinarith
  have hviewDistinct : ∀ j k, j ≠ k → bodyCyclicView q i j ≠ bodyCyclicView q i k := by
    intro j k hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [bodyCyclicView, cyclicPrev, cyclicNext]
  have hviewLongPrev :
      dist (bodyCyclicView q i 1) (bodyCyclicView q i 2) ^ 2 ≥
        dist (bodyCyclicView q i 0) (bodyCyclicView q i 1) ^ 2 := by
    simpa [bodyCyclicView, cyclicPrev, cyclicNext] using hlongPrev
  have hviewLongNext :
      dist (bodyCyclicView q i 1) (bodyCyclicView q i 2) ^ 2 ≥
        dist (bodyCyclicView q i 2) (bodyCyclicView q i 0) ^ 2 := by
    simpa [bodyCyclicView, cyclicPrev, cyclicNext, dist_comm] using hlongNext
  have hresult := syzygy_longest_opposite_side0_forces_positive_between_dot
    (bodyCyclicView q i) hviewArea hviewDistinct hviewLongPrev hviewLongNext
  simpa [bodyCyclicView, cyclicPrev, cyclicNext] using hresult

end DroppingThreeBodies
