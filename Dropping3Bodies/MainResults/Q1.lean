module

public import Dropping3Bodies.Dynamics.GeneralRegularDomain
public import Dropping3Bodies.Inertia.InitialBranchMonotonicity
public import Dropping3Bodies.Inertia.RegularEndpointDerivative

@[expose] public section

/-!
# Public Q1 contracts

The local IVP adapter is from `Dynamics/GeneralRegularDomain.lean`;
branch monotonicity is from `Inertia/InitialBranchMonotonicity.lean`; the
regular-endpoint derivative is project-derived from the Riccati and trace
identities in `Inertia/JacobiRiccati.lean`. This assembles the frozen
paper contract `thm:inertia`; no first-syzygy existence is assumed.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Every admissible rest datum has an actual general-mass local Newton
solution. On its regular noncollinear initial branch, both Montgomery's pair
moment and the physical center-of-mass moment are strictly antitone. The
branch contains a nontrivial interval `[0,δ]`, so the monotonicity statement
is not vacuous. -/
theorem exists_local_q1_initialBranch (G : ℝ) (hG : 0 < G)
    (d : InitialData) :
    ∃ ε > 0, ∃ z : ℝ → Phase,
      z 0 = (d.position, initialVelocity d) ∧
      GeneralClassicalNewtonSolution G d.mass z (Set.Ioo (-ε) ε) ∧
      StrictAntiOn (pairMomentCurve d.mass (fun i s => (z s).1 i))
        (BeforeFirstCollinearity z (Set.Ioo (-ε) ε) 0) ∧
      StrictAntiOn (centerOfMassMomentCurve d.mass (fun i s => (z s).1 i))
        (BeforeFirstCollinearity z (Set.Ioo (-ε) ε) 0) ∧
      ∃ δ > 0,
        Set.Icc 0 δ ⊆ BeforeFirstCollinearity z (Set.Ioo (-ε) ε) 0 := by
  have hcf : CollisionFree d.position := initialData_collisionFree d
  obtain ⟨ε, hε, z, hz0, hsol⟩ :=
    exists_local_generalClassicalNewtonSolution G d.mass
      (d.position, initialVelocity d) hcf
  have h0I : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
    constructor <;> linarith
  have hconn : IsPreconnected (Set.Ioo (-ε) ε) := isPreconnected_Ioo
  have hrest : ∀ i, (z 0).2 i = 0 := by
    intro i
    have hv := congrArg Prod.snd hz0
    simpa [initialVelocity] using congrArg (fun v : Fin 3 → Point => v i) hv
  have hpair := generalNewton_pairMomentCurve_strictAntiOn_initialBranch
    hsol hconn (d.positive_mass 0) (d.positive_mass 1) (d.positive_mass 2)
    hG hrest
  have hcenter := generalNewton_centerOfMassMomentCurve_strictAntiOn_initialBranch
    hsol hconn (d.positive_mass 0) (d.positive_mass 1) (d.positive_mass 2)
    hG hrest
  let A : ℝ → ℝ := fun s => signedDoubleArea (z s).1
  have hAcont : ContinuousAt A 0 := by
    have hfield : Continuous (fun q : Fin 3 → Point => signedDoubleArea q) := by
      unfold signedDoubleArea cross
      fun_prop
    have hzcont : ContinuousAt z 0 := (hsol.2 0 h0I).2.continuousAt
    dsimp [A]
    exact hfield.continuousAt.comp hzcont.fst
  have hA0 : A 0 ≠ 0 := by
    have hpos : (z 0).1 = d.position := congrArg Prod.fst hz0
    simpa [A, hpos] using d.noncollinear
  have hpre : A ⁻¹' {x : ℝ | x ≠ 0} ∈ nhds (0 : ℝ) :=
    hAcont.preimage_mem_nhds (isOpen_ne.mem_nhds hA0)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let δ : ℝ := min ε ρ / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨ε, hε, z, hz0, hsol, hpair, hcenter, δ, hδ, ?_⟩
  intro t ht
  have htδ : t ≤ δ := ht.2
  have htlo : 0 ≤ t := ht.1
  have hδeps : δ < ε := by
    dsimp [δ]
    have : 0 < min ε ρ := lt_min hε hρ
    linarith [min_le_left ε ρ]
  have hδrho : δ < ρ := by
    dsimp [δ]
    have : 0 < min ε ρ := lt_min hε hρ
    linarith [min_le_right ε ρ]
  refine ⟨htlo, ?_⟩
  refine ⟨?_, ?_⟩
  · intro s hs
    have hslo : 0 ≤ s := hs.1
    have hshi : s ≤ t := hs.2
    have hslt : s < ε := lt_of_le_of_lt (le_trans hshi htδ) hδeps
    exact ⟨by linarith, hslt⟩
  · intro s hs
    have hslo : 0 ≤ s := hs.1
    have hshi : s ≤ t := hs.2
    have hslt : s < ρ := lt_of_le_of_lt (le_trans hshi htδ) hδrho
    have hdist : dist s (0 : ℝ) < ρ := by
      simpa [Real.dist_eq, abs_of_nonneg hslo] using hslt
    have hAs : A s ≠ 0 := by simpa [Set.mem_setOf_eq] using hball hdist
    simpa [A] using hAs

/-- If a given regular solution reaches a first syzygy at `T`, the two moments
are strictly decreasing on the entire preceding branch and have strictly
negative derivatives at `T`. The hypothesis records the first-event property;
regularity at `T` is supplied by the classical solution on `[a,T]`. This
theorem does not assert that such a time exists. -/
theorem q1_given_regular_firstSyzygy
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a T : ℝ} (ha : a ∈ I) (haT : a < T) (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hrest : ∀ i, (z a).2 i = 0)
    (hnonzero : ∀ s ∈ Set.Ico a T, signedDoubleArea (z s).1 ≠ 0)
    (hareaT : signedDoubleArea (z T).1 = 0) :
    StrictAntiOn (pairMomentCurve m (fun i s => (z s).1 i))
      (BeforeFirstCollinearity z I a) ∧
    StrictAntiOn (centerOfMassMomentCurve m (fun i s => (z s).1 i))
      (BeforeFirstCollinearity z I a) ∧
    deriv (fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s) T < 0 ∧
    deriv (fun s => centerOfMassMomentCurve m (fun i τ => (z τ).1 i) s) T < 0 := by
  have hsign := generalNewton_signedArea_hasConstantSign_before_endpoint
    hsol haT hIcc hnonzero
  have hpair := generalNewton_pairMomentCurve_strictAntiOn_initialBranch
    hsol hconn hm0 hm1 hm2 hG hrest
  have hcenter := generalNewton_centerOfMassMomentCurve_strictAntiOn_initialBranch
    hsol hconn hm0 hm1 hm2 hG hrest
  have hpairEnd := generalNewton_pairMomentCurve_deriv_neg_at_regular_syzygy_of_nonempty_interval
    hsol hconn ha haT hIcc hm0 hm1 hm2 hG hsign hareaT hrest
  have hcenterEnd := generalNewton_centerOfMassMomentCurve_deriv_neg_at_regular_syzygy_of_nonempty_interval
    hsol hconn ha haT hIcc hm0 hm1 hm2 hG hsign hareaT hrest
  exact ⟨hpair, hcenter, hpairEnd, hcenterEnd⟩

end


end DroppingThreeBodies
