import TS.Goldbach.Strong.TS264.ConcreteRiemannZetaZeroFamilyRealization
import TS.Goldbach.Strong.TS337.ConditionalReferenceTraceBudgetAssembly

namespace TS338
namespace Goldbach

noncomputable section

/-!
# TS338: concrete zeta-ledger reference budget bridge

This module closes only the abstract zero-family parameter of the TS337
reference template, using the concrete Riemann-zeta ledger supplied by TS264.
The finite linear and quadratic coefficient caps remain explicit premises.
-/

/--
The TS337 reference trace-budget template specialized to the concrete
Riemann-zeta zero-family ledger from TS264.
-/
noncomputable def concreteReferenceTraceBudgetTemplate
    (hL :
      TS322.Goldbach.finiteLinearCoefficientMass 1132490 <=
        (((1 : Rat) / 20 : Rat) : Real))
    (hQ :
      TS333.Goldbach.finiteQuadraticCoefficientMass 1132490 <=
        (((1 : Rat) / 10000 : Rat) : Real)) :
    TS330.Goldbach.RationalTraceBudgetTemplate
      1132490 ((1 : Rat) / 7500) :=
  TS337.Goldbach.referenceTraceBudgetTemplate
    TS264.Goldbach.concreteZetaZeroFamilyLedger
    hL hQ

end

end Goldbach
end TS338
