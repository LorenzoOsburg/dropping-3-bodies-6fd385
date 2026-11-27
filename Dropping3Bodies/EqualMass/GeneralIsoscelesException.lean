module

public import Dropping3Bodies.Geometry.IsoscelesNormalization
public import Dropping3Bodies.Geometry.IsoscelesNormalizationConsequences
public import Dropping3Bodies.Geometry.EuclideanAreaSymmetry
public import Dropping3Bodies.Dynamics.MaximalEuclideanSymmetry
public import Dropping3Bodies.Dynamics.MaximalTranslation
public import Dropping3Bodies.EqualMass.IsoscelesMaximalEndpoint

@[expose] public section

/-! Transport the canonical equal-mass isosceles collision exception to
    arbitrary position, orientation, and body labels. -/

namespace DroppingThreeBodies

open Filter
open scoped Topology

noncomputable section

/-- An isosceles equal-mass rest start with two strictly longer equal legs
    has no syzygy on its maximal regular forward trajectory, independently
    of its position, orientation, or body labels. -/
theorem maximalNewtonUnion_general_isosceles_no_forward_syzygy
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (σ : Equiv.Perm (Fin 3))
    (hbaseDistinct : z₀.1 (σ 0) ≠ z₀.1 (σ 1))
    (hlegs : dist (z₀.1 (σ 0)) (z₀.1 (σ 2)) =
      dist (z₀.1 (σ 1)) (z₀.1 (σ 2)))
    (hlegsLong : dist (z₀.1 (σ 0)) (z₀.1 (σ 2)) >
      dist (z₀.1 (σ 0)) (z₀.1 (σ 1))) :
    (∀ t ∈ maximalNewtonUnionDomain z₀, 0 ≤ t →
      signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 ≠ 0) ∧
    (0 < sSup (maximalNewtonUnionDomain z₀) ∧
      sSup (maximalNewtonUnionDomain z₀) ≤ Real.sqrt (8*(dist (z₀.1 (σ 0))
        (z₀.1 (σ 1)) / 2)^3)) ∧
    Tendsto
      (fun t => dist ((maximalNewtonUnionTrajectory z₀ t).1 (σ 0))
        ((maximalNewtonUnionTrajectory z₀ t).1 (σ 1)))
      (nhdsWithin (sSup (maximalNewtonUnionDomain z₀))
        (Set.Iio (sSup (maximalNewtonUnionDomain z₀)))) (𝓝 0) := by
  let p := z₀.1 (σ 0)
  let q := z₀.1 (σ 1)
  let r := z₀.1 (σ 2)
  let b := (1 / 2 : ℝ) • (p + q)
  obtain ⟨O, u, v, hnormal⟩ :=
    exists_isosceles_normalization p q r hbaseDistinct hlegs
  let zP := permutePhase σ z₀
  let zT := translatePhase (-b) zP
  let zN := orthogonalPhase O zT
  let x := dist p q / 2
  have hx : 0 < x := by
    dsimp [x, p, q]
    exact div_pos (dist_pos.mpr hbaseDistinct) (by norm_num)
  have hbaseSum : (orthogonalConfiguration O
      (centerAtBaseMidpoint p q (orderedTriangle p q r)) 0) +
        (orthogonalConfiguration O
          (centerAtBaseMidpoint p q (orderedTriangle p q r)) 1) = 0 := by
    change O (p - b) + O (q - b) = 0
    rw [← O.map_add]
    have hsum : (p - b) + (q - b) = 0 := by
      dsimp [b]
      module
    rw [hsum]
    simp
  have hu : u = 0 := by
    have h := congrArg (fun f : Fin 3 → Point => (f 0 + f 1) 1) hnormal
    rw [hbaseSum] at h
    simp [isoscelesConfiguration, pointXY] at h
    linarith
  have hstartN : zN =
      (isoscelesConfiguration x 0 v,
        fun _ : Fin 3 => (0 : Point)) := by
    apply Prod.ext
    · change orthogonalConfiguration O
        (translateConfiguration (-b) (permuteConfiguration σ z₀.1)) =
          isoscelesConfiguration x 0 v
      have hcfg :
          translateConfiguration (-b) (permuteConfiguration σ z₀.1) =
            centerAtBaseMidpoint p q (orderedTriangle p q r) := by
        funext i
        fin_cases i <;>
          simp [translateConfiguration, translatePoint, permuteConfiguration,
            centerAtBaseMidpoint, orderedTriangle, p, q, r, b] <;> module
      rw [hcfg, hnormal, hu]
    · funext i
      change O (z₀.2 (σ i)) = 0
      rw [hrest]
      simp
  have hcfP : CollisionFree zP.1 := by
    rw [collisionFree_iff_dist_pos] at hcf ⊢
    intro i j hij
    exact hcf (σ i) (σ j) (fun h => hij (σ.injective h))
  have hcfT : CollisionFree zT.1 := by
    rw [collisionFree_iff_dist_pos] at hcfP ⊢
    intro i j hij
    change 0 < dist (translatePoint (-b) (permuteConfiguration σ z₀.1 i))
      (translatePoint (-b) (permuteConfiguration σ z₀.1 j))
    rw [translatePoint_dist]
    exact hcfP i j hij
  have hcfN : CollisionFree zN.1 := by
    rw [collisionFree_iff_dist_pos] at hcfT ⊢
    intro i j hij
    change 0 < dist (O (zT.1 i)) (O (zT.1 j))
    rw [O.dist_map]
    exact hcfT i j hij
  have hbaseN : dist (isoscelesConfiguration x 0 v 0)
      (isoscelesConfiguration x 0 v 1) = dist p q := by
    have hnorm' :
        dist (orthogonalConfiguration O
          (centerAtBaseMidpoint p q (orderedTriangle p q r)) 0)
          (orthogonalConfiguration O
            (centerAtBaseMidpoint p q (orderedTriangle p q r)) 1) =
          dist p q := by
      change dist (O (p - b)) (O (q - b)) = dist p q
      rw [O.dist_map]
      simpa [translatePoint, b, sub_eq_add_neg] using
        (translatePoint_dist (-b) p q)
    rw [hnormal] at hnorm'
    rw [hu] at hnorm'
    simpa [x] using hnorm'
  have hlegN : dist (isoscelesConfiguration x 0 v 0)
      (isoscelesConfiguration x 0 v 2) = dist p r := by
    have hnorm' :
        dist (orthogonalConfiguration O
          (centerAtBaseMidpoint p q (orderedTriangle p q r)) 0)
          (orthogonalConfiguration O
            (centerAtBaseMidpoint p q (orderedTriangle p q r)) 2) =
          dist p r := by
      change dist (O (p - b)) (O (r - b)) = dist p r
      rw [O.dist_map]
      simpa [translatePoint, b, sub_eq_add_neg] using
        (translatePoint_dist (-b) p r)
    rw [hnormal] at hnorm'
    rw [hu] at hnorm'
    simpa [x] using hnorm'
  have hlongN : dist (isoscelesConfiguration x 0 v 0)
      (isoscelesConfiguration x 0 v 2) >
      dist (isoscelesConfiguration x 0 v 0)
        (isoscelesConfiguration x 0 v 1) := by
    rw [hlegN, hbaseN]
    exact hlegsLong
  have hratio := isosceles_normalized_ratio_branches x 0 v hx hlongN
  have hcanonical := maximalNewtonUnion_isosceles_no_forward_syzygy_of_longer_legs
    x 0 v hx hratio zN hstartN hcfN
  have hdomainP : maximalNewtonUnionDomain zP =
      maximalNewtonUnionDomain z₀ :=
    maximalNewtonUnionDomain_permute z₀ σ
  have hdomainT : maximalNewtonUnionDomain zT =
      maximalNewtonUnionDomain zP :=
    maximalNewtonUnionDomain_translate zP (-b)
  have hdomainN : maximalNewtonUnionDomain zN =
      maximalNewtonUnionDomain zT :=
    maximalNewtonUnionDomain_orthogonal zT O
  have hdomain : maximalNewtonUnionDomain zN =
      maximalNewtonUnionDomain z₀ :=
    hdomainN.trans (hdomainT.trans hdomainP)
  have hsup : sSup (maximalNewtonUnionDomain zN) =
      sSup (maximalNewtonUnionDomain z₀) := congrArg sSup hdomain
  have hendpoint :=
    maximalNewtonUnionDomain_positive_finite_rightExtent_of_isosceles_rest
      x 0 v hx zN hstartN hcfN
  have hbaseLimit :=
    maximalNewtonUnion_isosceles_base_pair_distance_tends_zero
      x 0 v hx zN hstartN hcfN
  refine ⟨?_, ?_⟩
  · intro t ht ht0
    have htP : t ∈ maximalNewtonUnionDomain zP := by
      rw [hdomainP]
      exact ht
    have htT : t ∈ maximalNewtonUnionDomain zT := by
      rw [hdomainT]
      exact htP
    have htN : t ∈ maximalNewtonUnionDomain zN := by
      rw [hdomainN]
      exact htT
    have htrajP := maximalNewtonUnionTrajectory_permute z₀ σ ht
    have htrajT := maximalNewtonUnionTrajectory_translate zP (-b) htP
    have htrajN := maximalNewtonUnionTrajectory_orthogonal zT O htT
    have hareaP : signedDoubleArea
        (maximalNewtonUnionTrajectory zP t).1 = 0 ↔
        signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 = 0 :=
      by
        rw [htrajP]
        exact signedDoubleArea_permuteConfiguration_eq_zero_iff σ
          (maximalNewtonUnionTrajectory z₀ t).1
    have hareaT : signedDoubleArea
        (maximalNewtonUnionTrajectory zT t).1 =
        signedDoubleArea (maximalNewtonUnionTrajectory zP t).1 := by
      rw [htrajT]
      exact signedDoubleArea_translateConfiguration (-b)
        (maximalNewtonUnionTrajectory zP t).1
    have hareaN : signedDoubleArea
        (maximalNewtonUnionTrajectory zN t).1 = 0 ↔
        signedDoubleArea (maximalNewtonUnionTrajectory zT t).1 = 0 := by
      rw [htrajN]
      exact signedDoubleArea_orthogonalConfiguration_eq_zero_iff O
        (maximalNewtonUnionTrajectory zT t).1
    intro harea0
    have hareaT0 : signedDoubleArea
        (maximalNewtonUnionTrajectory zT t).1 = 0 := by
      rw [hareaT]
      exact hareaP.mpr harea0
    have hareaN0 : signedDoubleArea
        (maximalNewtonUnionTrajectory zN t).1 = 0 :=
      hareaN.mpr hareaT0
    exact (hcanonical t htN ht0) hareaN0
  · refine ⟨?_, ?_⟩
    · constructor
      · rw [← hsup]
        exact hendpoint.1
      · rw [← hsup]
        simpa [x, p, q] using hendpoint.2
    · let τ := sSup (maximalNewtonUnionDomain z₀)
      let f₀ := fun t => dist ((maximalNewtonUnionTrajectory z₀ t).1 (σ 0))
        ((maximalNewtonUnionTrajectory z₀ t).1 (σ 1))
      let fN := fun t => dist ((maximalNewtonUnionTrajectory zN t).1 0)
        ((maximalNewtonUnionTrajectory zN t).1 1)
      have hlimitN : Tendsto fN
          (nhdsWithin τ (Set.Iio τ)) (𝓝 0) := by
        simpa [fN, τ, hsup] using hbaseLimit
      have hboundedN : BddAbove (maximalNewtonUnionDomain zN) := by
        refine ⟨Real.sqrt (8*x^3), ?_⟩
        intro t ht
        exact le_of_lt
          (maximalNewtonUnionDomain_bddAbove_of_isosceles_rest
            x 0 v hx zN hstartN hcfN t ht)
      have hbounded₀ : BddAbove (maximalNewtonUnionDomain z₀) := by
        rw [← hdomain]
        exact hboundedN
      have hzero₀ : (0 : ℝ) ∈ maximalNewtonUnionDomain z₀ := by
        obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
        exact maximalNewtonWitness_interval_subset z₀ w
          ⟨w.left_lt_zero, w.zero_lt_right⟩
      have hconn₀ : IsPreconnected (maximalNewtonUnionDomain z₀) :=
        isPreconnected_maximalNewtonUnionDomain z₀
      have hnonempty₀ : (maximalNewtonUnionDomain z₀).Nonempty :=
        ⟨0, hzero₀⟩
      have hright : ∀ t ∈ Set.Ico 0 τ,
          t ∈ maximalNewtonUnionDomain z₀ := by
        intro t ht
        obtain ⟨s, hs, hts⟩ :=
          (lt_csSup_iff hbounded₀ hnonempty₀).mp ht.2
        exact hconn₀.Icc_subset hzero₀ hs ⟨ht.1, le_of_lt hts⟩
      have hτpos : 0 < τ := by
        dsimp [τ]
        rw [← hsup]
        exact hendpoint.1
      have hnear : ∀ᶠ t in nhdsWithin τ (Set.Iio τ), 0 < t := by
        exact Filter.Eventually.filter_mono
          (nhdsWithin_le_nhds (s := Set.Iio τ)) (Ioi_mem_nhds hτpos)
      have hevent : f₀ =ᶠ[nhdsWithin τ (Set.Iio τ)] fN := by
        filter_upwards [hnear, self_mem_nhdsWithin] with t htt htτ
        have ht₀ : t ∈ maximalNewtonUnionDomain z₀ :=
          hright t ⟨le_of_lt htt, htτ⟩
        have htP : t ∈ maximalNewtonUnionDomain zP := by
          rw [hdomainP]
          exact ht₀
        have htT : t ∈ maximalNewtonUnionDomain zT := by
          rw [hdomainT]
          exact htP
        have htN : t ∈ maximalNewtonUnionDomain zN := by
          rw [hdomainN]
          exact htT
        dsimp [f₀, fN]
        rw [maximalNewtonUnionTrajectory_orthogonal zT O htT,
          maximalNewtonUnionTrajectory_translate zP (-b) htP,
          maximalNewtonUnionTrajectory_permute z₀ σ ht₀]
        simp [orthogonalPhase, orthogonalConfiguration, translatePhase,
          translateConfiguration, translatePoint, permutePhase,
          permuteConfiguration, O.dist_map]
      exact hlimitN.congr' hevent.symm

end

end DroppingThreeBodies
