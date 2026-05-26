import TS.Goldbach.Strong.TS15.PCB_Q1_Discharge
import TS.Goldbach.Strong.TS15.MellinJacksonFourier

namespace TS15
namespace Goldbach

structure OTSAResidualPackage where
  secondMoment : ShortIntervalPrimeSecondMoment
  C_le_one : secondMoment.C <= 1

theorem problem_E1_of_otsa_residual_decomposition
    (P : OTSAResidualPackage) :
    Problem_E1 :=
  Problem_E1_from_short_interval_second_moment P.secondMoment P.C_le_one

end Goldbach
end TS15
