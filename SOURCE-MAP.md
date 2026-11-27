# Frozen source map

Every proof module below was copied from Git commit `40164c309e448b6cae1a67542dc8be97bb17377f`. The `Definitions` column lists declarations moved into `PrincipiaThreeBodies/Definitions.lean` in the submission copy.

| Original and submission proof file | Definitions moved into the statement interface |
| --- | --- |
| `Dropping3Bodies.lean` |  |
| `Dropping3Bodies/Adapters/NBody.lean` |  |
| `Dropping3Bodies/Basic.lean` | `DroppingThreeBodies.Point`, `DroppingThreeBodies.cross`, `DroppingThreeBodies.signedDoubleArea`, `DroppingThreeBodies.massMoment` |
| `Dropping3Bodies/Dynamics/CentralForce.lean` | `DroppingThreeBodies.CentralForce.Coefficients`, `DroppingThreeBodies.CentralForce.Coefficients.Positive`, `DroppingThreeBodies.CentralForce.Coefficients.C1`, `DroppingThreeBodies.CentralForce.weight`, `DroppingThreeBodies.CentralForce.acceleration`, `DroppingThreeBodies.CentralForce.vectorField`, `DroppingThreeBodies.CentralForce.Solution` |
| `Dropping3Bodies/Dynamics/CommonMassMaximalFlow.lean` |  |
| `Dropping3Bodies/Dynamics/CompleteEqualMassResult.lean` |  |
| `Dropping3Bodies/Dynamics/ConservationAlgebra.lean` |  |
| `Dropping3Bodies/Dynamics/ConservationCalculus.lean` |  |
| `Dropping3Bodies/Dynamics/Domain.lean` | `DroppingThreeBodies.CollisionFree` |
| `Dropping3Bodies/Dynamics/Energy.lean` |  |
| `Dropping3Bodies/Dynamics/FirstSyzygyCertificate.lean` | `DroppingThreeBodies.FirstRegularSyzygy` |
| `Dropping3Bodies/Dynamics/FirstSyzygyPlacement.lean` |  |
| `Dropping3Bodies/Dynamics/GeneralEnergy.lean` |  |
| `Dropping3Bodies/Dynamics/GeneralNewton.lean` |  |
| `Dropping3Bodies/Dynamics/GeneralPairRotation.lean` |  |
| `Dropping3Bodies/Dynamics/GeneralReflectionSymmetry.lean` |  |
| `Dropping3Bodies/Dynamics/GeneralRegularDomain.lean` |  |
| `Dropping3Bodies/Dynamics/GravityRescaling.lean` |  |
| `Dropping3Bodies/Dynamics/Homothetic.lean` |  |
| `Dropping3Bodies/Dynamics/MaximalEuclideanSymmetry.lean` |  |
| `Dropping3Bodies/Dynamics/MaximalInterval.lean` |  |
| `Dropping3Bodies/Dynamics/MaximalReflection.lean` |  |
| `Dropping3Bodies/Dynamics/MaximalSolution.lean` |  |
| `Dropping3Bodies/Dynamics/MaximalTranslation.lean` |  |
| `Dropping3Bodies/Dynamics/Newton.lean` | `DroppingThreeBodies.Phase` |
| `Dropping3Bodies/Dynamics/OrthogonalSymmetry.lean` |  |
| `Dropping3Bodies/Dynamics/PhaseExtension.lean` |  |
| `Dropping3Bodies/Dynamics/PhaseLipschitz.lean` |  |
| `Dropping3Bodies/Dynamics/ReflectionSymmetry.lean` |  |
| `Dropping3Bodies/Dynamics/RegularDomain.lean` |  |
| `Dropping3Bodies/Dynamics/SolutionDerivatives.lean` |  |
| `Dropping3Bodies/Dynamics/SolutionMomentum.lean` |  |
| `Dropping3Bodies/Dynamics/SyzygyAngle.lean` |  |
| `Dropping3Bodies/Dynamics/SyzygyQuantitative.lean` |  |
| `Dropping3Bodies/Dynamics/TranslationSymmetry.lean` |  |
| `Dropping3Bodies/EqualMass/EquilateralMaximalEndpoint.lean` |  |
| `Dropping3Bodies/EqualMass/FrameCalculus.lean` |  |
| `Dropping3Bodies/EqualMass/GapIdentity.lean` |  |
| `Dropping3Bodies/EqualMass/GeneralIsoscelesException.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesBootstrap.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesComparison.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesCurveCalculus.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesHeightEndpoint.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesInitialSymmetry.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesMaximalEndpoint.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesRatioGeometry.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesReduction.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesSymmetry.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesTrajectoryBootstrap.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesTrajectoryODE.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesTrajectoryReduction.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesWronskian.lean` |  |
| `Dropping3Bodies/EqualMass/IsoscelesWronskianGeometry.lean` |  |
| `Dropping3Bodies/EqualMass/PowerLawCollision.lean` |  |
| `Dropping3Bodies/EqualMass/PowerLawComparison.lean` |  |
| `Dropping3Bodies/EqualMass/PowerLawCritical.lean` |  |
| `Dropping3Bodies/EqualMass/PowerLawEndpoint.lean` |  |
| `Dropping3Bodies/EqualMass/PowerLawEnergy.lean` |  |
| `Dropping3Bodies/EqualMass/PowerLawGeometry.lean` | `DroppingThreeBodies.CentralForce.orderedOppositeSides` |
| `Dropping3Bodies/EqualMass/PowerLawModel.lean` | `DroppingThreeBodies.CentralForce.commonCouplings`, `DroppingThreeBodies.CentralForce.EqualPowerSolution` |
| `Dropping3Bodies/EqualMass/SideFrame.lean` |  |
| `Dropping3Bodies/EqualMass/SolutionCooperativeSystem.lean` |  |
| `Dropping3Bodies/EqualMass/SolutionGapRatio.lean` |  |
| `Dropping3Bodies/EqualMass/SolutionPairRotation.lean` |  |
| `Dropping3Bodies/EqualMass/SolutionSideFrame.lean` |  |
| `Dropping3Bodies/EqualMass/SolutionSideOrdering.lean` |  |
| `Dropping3Bodies/EqualMass/Torque.lean` |  |
| `Dropping3Bodies/Geometry/Betweenness.lean` |  |
| `Dropping3Bodies/Geometry/BodyIndex.lean` |  |
| `Dropping3Bodies/Geometry/Coordinates.lean` |  |
| `Dropping3Bodies/Geometry/EuclideanAreaSymmetry.lean` |  |
| `Dropping3Bodies/Geometry/Inertia.lean` | `DroppingThreeBodies.weightedPosition`, `DroppingThreeBodies.totalMass` |
| `Dropping3Bodies/Geometry/InertiaCalculus.lean` |  |
| `Dropping3Bodies/Geometry/IsoscelesNormalization.lean` |  |
| `Dropping3Bodies/Geometry/IsoscelesNormalizationConsequences.lean` |  |
| `Dropping3Bodies/Geometry/Reflection.lean` |  |
| `Dropping3Bodies/Geometry/ScaleneSideSelection.lean` |  |
| `Dropping3Bodies/Geometry/SideOrderClassification.lean` |  |
| `Dropping3Bodies/Geometry/SyzygyMidpoint.lean` |  |
| `Dropping3Bodies/Geometry/Translation.lean` |  |
| `Dropping3Bodies/Inertia/AbstractJacobi.lean` |  |
| `Dropping3Bodies/Inertia/AbstractJacobiArea.lean` |  |
| `Dropping3Bodies/Inertia/AbstractJacobiContraction.lean` |  |
| `Dropping3Bodies/Inertia/AreaConcavity.lean` |  |
| `Dropping3Bodies/Inertia/AreaDerivative.lean` |  |
| `Dropping3Bodies/Inertia/CenterOfMassMoment.lean` | `DroppingThreeBodies.centerOfMassMoment`, `DroppingThreeBodies.centerOfMassMomentCurve` |
| `Dropping3Bodies/Inertia/CentralForceContraction.lean` | `DroppingThreeBodies.CentralForce.orientedArea` |
| `Dropping3Bodies/Inertia/CentralForceJacobi.lean` |  |
| `Dropping3Bodies/Inertia/CentralForceMaximal.lean` | `DroppingThreeBodies.CentralForce.maximalDomain`, `DroppingThreeBodies.CentralForce.maximalTrajectory`, `DroppingThreeBodies.CentralForce.initialNoncollinearEndpoint` |
| `Dropping3Bodies/Inertia/CentralForcePowerLaw.lean` | `DroppingThreeBodies.CentralForce.powerCoefficients` |
| `Dropping3Bodies/Inertia/InitialBranchFiniteness.lean` |  |
| `Dropping3Bodies/Inertia/InitialBranchMonotonicity.lean` | `DroppingThreeBodies.BeforeFirstCollinearity` |
| `Dropping3Bodies/Inertia/Jacobi.lean` |  |
| `Dropping3Bodies/Inertia/JacobiDynamics.lean` |  |
| `Dropping3Bodies/Inertia/JacobiNewton.lean` | `DroppingThreeBodies.matrixQuadratic` |
| `Dropping3Bodies/Inertia/JacobiRiccati.lean` |  |
| `Dropping3Bodies/Inertia/JacobiTensor.lean` | `DroppingThreeBodies.centeredSpatialMoment` |
| `Dropping3Bodies/Inertia/MaximalInitialBranch.lean` |  |
| `Dropping3Bodies/Inertia/RegularEndpointDerivative.lean` |  |
| `Dropping3Bodies/Inertia/Virial.lean` |  |
| `Dropping3Bodies/MainResults/CommonMassClassificationTransport.lean` |  |
| `Dropping3Bodies/MainResults/EqualMassClassification.lean` |  |
| `Dropping3Bodies/MainResults/EqualMassClassificationScaling.lean` |  |
| `Dropping3Bodies/MainResults/MontgomeryQ2.lean` |  |
| `Dropping3Bodies/MainResults/Q1.lean` |  |
| `Dropping3Bodies/MainResults/Q1Complete.lean` |  |
| `Dropping3Bodies/MainResults/Q2.lean` |  |
| `Dropping3Bodies/MainResults/Q2PowerLaw.lean` |  |
| `Dropping3Bodies/Support/CollisionBarrier.lean` |  |
| `Dropping3Bodies/Support/CooperativePair.lean` |  |
| `Dropping3Bodies/Support/CooperativeUniqueness.lean` |  |
| `Dropping3Bodies/Support/FirstZero.lean` |  |
| `Dropping3Bodies/Support/IntervalEndpoint.lean` |  |
| `Dropping3Bodies/Support/SecondOrderComparison.lean` |  |
| `NBody.lean` |  |
| `NBody/Basic.lean` | `NBody.Config`, `NBody.Phase`, `NBody.CollisionFree`, `NBody.regularPhaseSet` |
| `NBody/BlowUp/McGehee.lean` |  |
| `NBody/CentralConfiguration.lean` |  |
| `NBody/Configuration/MassPairing.lean` |  |
| `NBody/Configuration/Masses.lean` | `NBody.totalMass`, `NBody.weightedPosition`, `NBody.centerOfMass` |
| `NBody/Conservation/AbstractEnergy.lean` |  |
| `NBody/Conservation/Energy.lean` |  |
| `NBody/Conservation/Momentum.lean` |  |
| `NBody/Coordinates/TwoCluster.lean` |  |
| `NBody/LocalExistence.lean` |  |
| `NBody/MaximalSolution.lean` |  |
| `NBody/Newton.lean` |  |
| `NBody/ODE/Continuation.lean` |  |
| `NBody/ODE/LocalTheory.lean` |  |
| `NBody/ODE/Maximal.lean` | `NBody.InitialIntervalWitness`, `NBody.maximalUnionDomain`, `NBody.maximalUnionDomain_covered`, `NBody.maximalChosenWitness`, `NBody.maximalUnionTrajectory` |
| `NBody/ODE/Solution.lean` | `NBody.SolutionOn` |
| `NBody/ODE/TimeChange.lean` |  |
| `NBody/PairSums.lean` |  |
| `NBody/Phase/Momentum.lean` |  |
| `NBody/Potential/Homogeneous.lean` |  |
| `NBody/Potential/InversePower.lean` | `NBody.SymmetricCouplings` |
| `NBody/Potential/InversePowerGradient.lean` |  |
| `NBody/Potential/RadialPair.lean` |  |
| `NBody/Potential/RotationalSymmetry.lean` |  |
| `NBody/Regularity.lean` |  |
| `NBody/Regularization/LeviCivita.lean` |  |
| `NBody/Singularities/Clusters.lean` |  |
| `NBody/Singularities/Endpoints.lean` |  |
| `NBody/Solution.lean` |  |
| `NBody/Symmetry.lean` |  |
| `NBody/Symmetry/Time.lean` |  |
| `NBody/Variational/ActionModel.lean` |  |

## Submission addition

`DroppingThreeBodies.CentralForce.orientedArea_deriv_neg` in
`Dropping3Bodies/Inertia/CentralForceContraction.lean` is a new physical
corollary in the submission copy. See [the statement inventory](STATEMENTS.md)
for its signature and frozen proof dependencies.
