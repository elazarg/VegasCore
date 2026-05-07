import Vegas.Protocol.Backend

/-!
# Backend Refinement Theorems

Project-facing names for distribution preservation under stochastic machine
refinement and compatible backend block laws.
-/

namespace Vegas

open GameTheory

/-- Compatible backend block laws preserve blocked trace distributions after
projection to the specification machine. -/
theorem backend_blockTraceDist_project_eq
    {P : Type} {Impl Spec : Machine P}
    (R : Machine.StochasticStepRefinement Impl Spec)
    (lawSpec : Spec.BlockLaw) (lawImpl : Impl.BlockLaw)
    (compat : R.BlockLawCompatible lawImpl lawSpec)
    (horizon : Nat) (trace : Impl.BlockTrace) :
    PMF.map R.projectBlockTrace
        (Impl.blockTraceDistFrom lawImpl horizon trace) =
      Spec.blockTraceDistFrom lawSpec horizon (R.projectBlockTrace trace) :=
  R.blockTraceDist_project_eq lawSpec lawImpl compat horizon trace

end Vegas
