import ConcreteNTTRoots22
import FiniteFieldProjection22

/-! SOURCE ONLY. FiniteFieldProjection22 is the independently compiled module
of batch19 and must be imported through its preserved read-only olean, together
with its two batch17 dependencies. ConcreteNTTRoots22 is new SOURCE, to be judged
first in the same future lot. Each Fact below contains the proved Lucas theorem;
none is an added premise. These five projections are exact finite character
identities for the canonical A32 prime-power weights at N=100000000, K=2^27.
There is no machine execution, butterfly correctness or CRT theorem here.
-/

namespace GoldbachConcreteNTTA32Projection22

open GoldbachConcreteNTTRoots22 GoldbachFiniteFieldProjection22

def primeFact2013265921 : Fact (Nat.Prime 2013265921) := ⟨prime_2013265921⟩
def primeFact2281701377 : Fact (Nat.Prime 2281701377) := ⟨prime_2281701377⟩
def primeFact3221225473 : Fact (Nat.Prime 3221225473) := ⟨prime_3221225473⟩
def primeFact3489660929 : Fact (Nat.Prime 3489660929) := ⟨prime_3489660929⟩
def primeFact3892314113 : Fact (Nat.Prime 3892314113) := ⟨prime_3892314113⟩

attribute [local instance] primeFact2013265921 primeFact2281701377
  primeFact3221225473 primeFact3489660929 primeFact3892314113

theorem projection_2013265921 :
    fieldProjection (bankRoot 2013265921 31)
      (fun n => (GoldbachQuantizedCoefficient22.integerLambda n : ZMod 2013265921))
        100000000 100000000 (2 ^ 27) =
      (GoldbachQuantizedCoefficient22.integerCoefficient 100000000 : ZMod 2013265921) := by
  exact fixed_A32_projection primitive_2013265921 size_2013265921

theorem projection_2281701377 :
    fieldProjection (bankRoot 2281701377 3)
      (fun n => (GoldbachQuantizedCoefficient22.integerLambda n : ZMod 2281701377))
        100000000 100000000 (2 ^ 27) =
      (GoldbachQuantizedCoefficient22.integerCoefficient 100000000 : ZMod 2281701377) := by
  exact fixed_A32_projection primitive_2281701377 size_2281701377

theorem projection_3221225473 :
    fieldProjection (bankRoot 3221225473 5)
      (fun n => (GoldbachQuantizedCoefficient22.integerLambda n : ZMod 3221225473))
        100000000 100000000 (2 ^ 27) =
      (GoldbachQuantizedCoefficient22.integerCoefficient 100000000 : ZMod 3221225473) := by
  exact fixed_A32_projection primitive_3221225473 size_3221225473

theorem projection_3489660929 :
    fieldProjection (bankRoot 3489660929 3)
      (fun n => (GoldbachQuantizedCoefficient22.integerLambda n : ZMod 3489660929))
        100000000 100000000 (2 ^ 27) =
      (GoldbachQuantizedCoefficient22.integerCoefficient 100000000 : ZMod 3489660929) := by
  exact fixed_A32_projection primitive_3489660929 size_3489660929

theorem projection_3892314113 :
    fieldProjection (bankRoot 3892314113 3)
      (fun n => (GoldbachQuantizedCoefficient22.integerLambda n : ZMod 3892314113))
        100000000 100000000 (2 ^ 27) =
      (GoldbachQuantizedCoefficient22.integerCoefficient 100000000 : ZMod 3892314113) := by
  exact fixed_A32_projection primitive_3892314113 size_3892314113

end GoldbachConcreteNTTA32Projection22

#print axioms GoldbachConcreteNTTA32Projection22.primeFact2013265921
#print axioms GoldbachConcreteNTTA32Projection22.primeFact2281701377
#print axioms GoldbachConcreteNTTA32Projection22.primeFact3221225473
#print axioms GoldbachConcreteNTTA32Projection22.primeFact3489660929
#print axioms GoldbachConcreteNTTA32Projection22.primeFact3892314113
#print axioms GoldbachConcreteNTTA32Projection22.projection_2013265921
#print axioms GoldbachConcreteNTTA32Projection22.projection_2281701377
#print axioms GoldbachConcreteNTTA32Projection22.projection_3221225473
#print axioms GoldbachConcreteNTTA32Projection22.projection_3489660929
#print axioms GoldbachConcreteNTTA32Projection22.projection_3892314113
