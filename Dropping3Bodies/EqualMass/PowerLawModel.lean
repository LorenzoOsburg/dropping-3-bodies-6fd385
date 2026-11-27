module

public import Dropping3Bodies.Inertia.CentralForcePowerLaw
public import PrincipiaThreeBodies.Definitions

@[expose] public section

namespace DroppingThreeBodies.CentralForce

@[simp] theorem commonCouplings_offDiag (g : ℝ) {i j : Fin 3} (h : i ≠ j) :
    (commonCouplings g).coeff i j = g := if_neg h

end DroppingThreeBodies.CentralForce
