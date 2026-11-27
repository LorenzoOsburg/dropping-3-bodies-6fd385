module

public import Dropping3Bodies.Dynamics.Newton
public import Dropping3Bodies.Dynamics.GeneralNewton
public import Dropping3Bodies.Dynamics.GeneralEnergy
public import Dropping3Bodies.Dynamics.ReflectionSymmetry
public import Dropping3Bodies.Dynamics.TranslationSymmetry
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic

@[expose] public section

/-! Coordinate-free Euclidean and body-label symmetries of equal-mass Newton
    dynamics. -/

namespace DroppingThreeBodies

noncomputable section

/-- Apply a fixed Euclidean linear isometry to every body coordinate. -/
def orthogonalConfiguration (O : Point ≃ₗᵢ[ℝ] Point)
    (q : Fin 3 → Point) : Fin 3 → Point := fun i => O (q i)

/-- Apply a fixed Euclidean linear isometry to positions and velocities. -/
def orthogonalPhase (O : Point ≃ₗᵢ[ℝ] Point) (z : Phase) : Phase :=
  (orthogonalConfiguration O z.1, orthogonalConfiguration O z.2)

/-- Pairwise distances, and hence inverse-cube kernels, are invariant under
    orthogonal coordinate changes. -/
theorem inverseCubeDistance_orthogonalConfiguration
    (O : Point ≃ₗᵢ[ℝ] Point) (q : Fin 3 → Point) (i j : Fin 3) :
    inverseCubeDistance (orthogonalConfiguration O q) i j =
      inverseCubeDistance q i j := by
  simp [inverseCubeDistance, orthogonalConfiguration,
    LinearIsometryEquiv.dist_map]

/-- Newton acceleration commutes with every linear isometry of the plane. -/
theorem unitAcceleration_orthogonalConfiguration
    (O : Point ≃ₗᵢ[ℝ] Point) (q : Fin 3 → Point) (i : Fin 3) :
    unitAcceleration (orthogonalConfiguration O q) i =
      O (unitAcceleration q i) := by
  fin_cases i <;>
    simp [unitAcceleration, orthogonalConfiguration,
      inverseCubeDistance_orthogonalConfiguration, O.map_sub, O.map_smul,
      O.map_add]

theorem unitNewtonField_orthogonalPhase
    (O : Point ≃ₗᵢ[ℝ] Point) (z : Phase) :
    unitNewtonField (orthogonalPhase O z) =
      orthogonalPhase O (unitNewtonField z) := by
  cases z with
  | mk q v =>
      apply Prod.ext
      · rfl
      · funext i
        exact unitAcceleration_orthogonalConfiguration O q i

/-- The phase-space action induced by an isometry is linear. -/
def orthogonalPhaseLinear (O : Point ≃ₗᵢ[ℝ] Point) : Phase →ₗ[ℝ] Phase where
  toFun := orthogonalPhase O
  map_add' z w := by
    rcases z with ⟨q, v⟩
    rcases w with ⟨q', v'⟩
    apply Prod.ext <;> funext i <;>
      simp [orthogonalPhase, orthogonalConfiguration, O.map_add]
  map_smul' c z := by
    rcases z with ⟨q, v⟩
    apply Prod.ext <;> funext i <;>
      simp [orthogonalPhase, orthogonalConfiguration, O.map_smul]

noncomputable def orthogonalPhaseCLM (O : Point ≃ₗᵢ[ℝ] Point) :
    Phase →L[ℝ] Phase := (orthogonalPhaseLinear O).toContinuousLinearMap

/-- Every classical equal-mass Newton solution remains a solution after an
    arbitrary fixed planar orthogonal transformation. -/
theorem classicalNewtonSolution_orthogonal
    {z : ℝ → Phase} {I : Set ℝ} (O : Point ≃ₗᵢ[ℝ] Point)
    (hsol : ClassicalNewtonSolution z I) :
    ClassicalNewtonSolution (fun t => orthogonalPhase O (z t)) I := by
  refine ⟨hsol.1, fun t ht => ?_⟩
  have hregular := hsol.2 t ht
  constructor
  · intro i j hij
    apply dist_pos.mp
    change 0 < dist (O ((z t).1 i)) (O ((z t).1 j))
    rw [LinearIsometryEquiv.dist_map]
    exact dist_pos.mpr (hregular.1 i j hij)
  · have hderiv :=
      (HasFDerivAt.comp t (orthogonalPhaseCLM O).hasFDerivAt
        hregular.2.hasFDerivAt).hasDerivAt
    have hderiv' : HasDerivAt (fun s => orthogonalPhase O (z s))
        (orthogonalPhase O (unitNewtonField (z t))) t := by
      simpa [orthogonalPhaseCLM, orthogonalPhaseLinear,
        Function.comp_def] using hderiv
    rw [← unitNewtonField_orthogonalPhase O (z t)] at hderiv'
    exact hderiv'

/-- A permutation of body labels, acting contravariantly on configurations. -/
def permuteConfiguration (σ : Equiv.Perm (Fin 3))
    (q : Fin 3 → Point) : Fin 3 → Point := fun i => q (σ i)

def permutePhase (σ : Equiv.Perm (Fin 3)) (z : Phase) : Phase :=
  (permuteConfiguration σ z.1, permuteConfiguration σ z.2)

def permuteMass (σ : Equiv.Perm (Fin 3)) (m : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => m (σ i)

def permutePhaseLinear (σ : Equiv.Perm (Fin 3)) : Phase →ₗ[ℝ] Phase where
  toFun := permutePhase σ
  map_add' z w := by
    rcases z with ⟨q, v⟩
    rcases w with ⟨q', v'⟩
    apply Prod.ext <;> funext i <;>
      simp [permutePhase, permuteConfiguration]
  map_smul' c z := by
    rcases z with ⟨q, v⟩
    apply Prod.ext <;> funext i <;>
      simp [permutePhase, permuteConfiguration]

noncomputable def permutePhaseCLM (σ : Equiv.Perm (Fin 3)) :
    Phase →L[ℝ] Phase := (permutePhaseLinear σ).toContinuousLinearMap

/-- Reindexing bodies and their masses together commutes with the general
    Newton field. -/
theorem generalNewtonField_permutePhase
    (G : ℝ) (m : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) (z : Phase) :
    generalNewtonField G (permuteMass σ m) (permutePhase σ z) =
      permutePhase σ (generalNewtonField G m z) := by
  cases z with
  | mk q v =>
      apply Prod.ext
      · rfl
      · funext i
        simp [generalNewtonField, permutePhase, permuteConfiguration,
          permuteMass, generalAcceleration, inverseCubeDistance]
        let f : Fin 3 → Point := fun k =>
          if k = σ i then 0 else
            (G * m k * (dist (q (σ i)) (q k) ^ 3)⁻¹) •
              (q k - q (σ i))
        have hleft :
            (∑ x : Fin 3, if x = i then (0 : Point) else
              (G * m (σ x) * (dist (q (σ i)) (q (σ x)) ^ 3)⁻¹) •
                (q (σ x) - q (σ i))) = ∑ x, f (σ x) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [f, σ.injective.eq_iff]
        have hright :
            (∑ x : Fin 3, if x = σ i then (0 : Point) else
              (G * m x * (dist (q (σ i)) (q x) ^ 3)⁻¹) •
                (q x - q (σ i))) = ∑ x, f x := by
          simp [f]
        have hsum := Equiv.sum_comp σ f
        calc
          _ = ∑ x, f (σ x) := hleft
          _ = ∑ x, f x := hsum
          _ = _ := hright.symm

/-- A classical solution remains a classical solution after relabeling bodies
    and relabeling their masses by the same permutation. -/
theorem generalClassicalNewtonSolution_permute
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (σ : Equiv.Perm (Fin 3))
    (hsol : GeneralClassicalNewtonSolution G m z I) :
    GeneralClassicalNewtonSolution G (permuteMass σ m)
      (fun t => permutePhase σ (z t)) I := by
  refine ⟨hsol.1, fun t ht => ?_⟩
  have hregular := hsol.2 t ht
  constructor
  · intro i j hij
    apply dist_pos.mp
    change 0 < dist ((z t).1 (σ i)) ((z t).1 (σ j))
    apply dist_pos.mpr
    exact hregular.1 (σ i) (σ j) (fun h => hij (σ.injective h))
  · have hderiv :=
      (HasFDerivAt.comp t (permutePhaseCLM σ).hasFDerivAt
        hregular.2.hasFDerivAt).hasDerivAt
    have hderiv' : HasDerivAt (fun s => permutePhase σ (z s))
        (permutePhase σ (generalNewtonField G m (z t))) t := by
      simpa [permutePhaseCLM, permutePhaseLinear,
        Function.comp_def] using hderiv
    rw [← generalNewtonField_permutePhase G m σ (z t)] at hderiv'
    exact hderiv'

/-- Equal-mass Newton solutions are invariant under any relabeling of the
    three bodies. -/
theorem classicalNewtonSolution_permute
    {z : ℝ → Phase} {I : Set ℝ} (σ : Equiv.Perm (Fin 3))
    (hsol : ClassicalNewtonSolution z I) :
    ClassicalNewtonSolution (fun t => permutePhase σ (z t)) I := by
  have hgeneral : GeneralClassicalNewtonSolution 1
      (fun _ : Fin 3 => 1) z I := by
    refine ⟨hsol.1, fun t ht => ?_⟩
    rcases hsol.2 t ht with ⟨hcf, hderiv⟩
    refine ⟨hcf, ?_⟩
    rw [generalNewtonField_one_eq_unit]
    exact hderiv
  have hresult := generalClassicalNewtonSolution_permute σ hgeneral
  have hmass : permuteMass σ (fun _ : Fin 3 => 1) =
      (fun _ : Fin 3 => 1) := by
    funext i
    rfl
  rw [hmass] at hresult
  refine ⟨hresult.1, fun t ht => ?_⟩
  rcases hresult.2 t ht with ⟨hcf, hderiv⟩
  refine ⟨hcf, ?_⟩
  rw [generalNewtonField_one_eq_unit] at hderiv
  exact hderiv

/-- For equal masses, relabeling the bodies preserves the Newton vector
    field. -/
theorem unitNewtonField_permutePhase
    (σ : Equiv.Perm (Fin 3)) (z : Phase) :
    unitNewtonField (permutePhase σ z) =
      permutePhase σ (unitNewtonField z) := by
  have hperm :=
    generalNewtonField_permutePhase 1 (fun _ : Fin 3 => 1) σ z
  change generalNewtonField 1 (fun _ : Fin 3 => 1) (permutePhase σ z) =
    permutePhase σ (generalNewtonField 1 (fun _ : Fin 3 => 1) z) at hperm
  calc
    unitNewtonField (permutePhase σ z) =
        generalNewtonField 1 (fun _ : Fin 3 => 1) (permutePhase σ z) :=
      (generalNewtonField_one_eq_unit (permutePhase σ z)).symm
    _ = permutePhase σ (generalNewtonField 1 (fun _ : Fin 3 => 1) z) := by
      exact hperm
    _ = permutePhase σ (unitNewtonField z) :=
      congrArg (permutePhase σ) (generalNewtonField_one_eq_unit z)

end

end DroppingThreeBodies
