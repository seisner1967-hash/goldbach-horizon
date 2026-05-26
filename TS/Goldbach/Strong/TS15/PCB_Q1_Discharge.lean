import TS.Goldbach.Strong.TS15.ProblemE1ShortIntervals

namespace TS15
namespace Goldbach

def PCB_Q1_Discharge : Prop :=
  forall H : ShortIntervalPrimeSecondMoment,
    H.C <= 1 ->
    Problem_E1

theorem pcb_q1_discharge_from_short_interval_second_moment :
    PCB_Q1_Discharge := by
  intro H hC
  exact Problem_E1_from_short_interval_second_moment H hC

end Goldbach
end TS15
