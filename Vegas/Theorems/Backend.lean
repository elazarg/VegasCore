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

/-- Compatible backend block laws preserve projected outcome distributions,
not only blocked trace distributions, when the outcome projection commutes on
all implementation states. -/
theorem backend_outcomeKernel_project_eq
    {P : Type} {Impl Spec : Machine P}
    (R : Machine.StochasticStepRefinement Impl Spec)
    (lawSpec : Spec.BlockLaw) (lawImpl : Impl.BlockLaw)
    (compat : R.BlockLawCompatible lawImpl lawSpec)
    (houtcome :
      ∀ state : Impl.State,
        R.projectOutcome (Impl.outcome state) =
          Spec.outcome (R.projectState state))
    (horizon : Nat) (trace : Impl.BlockTrace) :
    PMF.map (fun tr => R.projectOutcome (Impl.outcome tr.2))
        (Impl.blockTraceDistFrom lawImpl horizon trace) =
      PMF.map (fun tr => Spec.outcome tr.2)
        (Spec.blockTraceDistFrom lawSpec horizon
          (R.projectBlockTrace trace)) := by
  rw [← R.blockTraceDist_project_eq lawSpec lawImpl compat horizon trace]
  rw [PMF.map_comp]
  apply congrArg
    (fun f : Impl.BlockTrace → Spec.Outcome =>
      PMF.map f (Impl.blockTraceDistFrom lawImpl horizon trace))
  funext tr
  simpa [Function.comp_def] using houtcome tr.2

/-- Extra backend state and events cannot introduce projected public signals
under stochastic refinement. -/
theorem backend_cannot_introduce_public_signal_under_refinement
    {P : Type} {Impl Spec : Machine P}
    (R : Machine.StochasticStepRefinement Impl Spec)
    (state : Impl.State) :
    Spec.publicView (R.projectState state) =
      R.projectPublic (Impl.publicView state) :=
  R.publicView_project state

/- TODO:
theorem backend_nash_transport ...

Backend refinement plus compatible block-law lifts should transport Nash
equilibria from the canonical specification game to the backend game. The
statement needs a dedicated backend game morphism/equilibrium-transport
interface, rather than a placeholder predicate.
-/

end Vegas
