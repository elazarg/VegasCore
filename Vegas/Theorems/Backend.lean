import Vegas.Backend.KernelGame

/-!
# Backend Refinement Theorems

Project-facing names for distribution preservation under stochastic machine
refinement and compatible backend event-batch laws.
-/

namespace Vegas

open GameTheory

/-- Compatible backend event-batch laws preserve event-batch trace distributions after
projection to the specification machine. -/
theorem backend_eventBatchTraceDist_project_eq
    {P : Type} {Impl Spec : Machine P}
    (R : Machine.StochasticStepRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map R.projectEventBatchTrace
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
      Spec.eventBatchTraceDistFrom lawSpec horizon (R.projectEventBatchTrace trace) :=
  R.eventBatchTraceDist_project_eq lawSpec lawImpl compat horizon trace

/-- Compatible backend event-batch laws preserve projected outcome distributions,
not only event-batch trace distributions, when the outcome projection commutes on
all implementation states. -/
theorem backend_outcomeKernel_project_eq
    {P : Type} {Impl Spec : Machine P}
    (R : Machine.StochasticStepRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec)
    (houtcome :
      ∀ state : Impl.State,
        R.projectOutcome (Impl.outcome state) =
          Spec.outcome (R.projectState state))
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map (fun tr => R.projectOutcome (Impl.outcome tr.2))
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
      PMF.map (fun tr => Spec.outcome tr.2)
        (Spec.eventBatchTraceDistFrom lawSpec horizon
          (R.projectEventBatchTrace trace)) := by
  rw [← R.eventBatchTraceDist_project_eq lawSpec lawImpl compat horizon trace]
  rw [PMF.map_comp]
  apply congrArg
    (fun f : Impl.EventBatchTrace → Spec.Outcome =>
      PMF.map f (Impl.eventBatchTraceDistFrom lawImpl horizon trace))
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

/-- Backend refinement plus a compatible pure event-batch-law lift transports Nash
equilibria from the public pure specification game to the backend event-batch trace
game. -/
theorem backend_pure_nash_transport
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureEventBatchLawLift g R)
    {σ : pureProfileAt g}
    (h : (pureKernelGameAt g).IsNash σ) :
    (backendEventBatchTraceKernelGameAt g R lift).IsNash σ :=
  backendEventBatchTraceKernelGameAt_isNash_pullback g R lift h

/-- Backend refinement plus a compatible PMF-behavioral event-batch-law lift
transports Nash equilibria from the public PMF-behavioral specification game to
the backend event-batch trace game. -/
theorem backend_behavioral_nash_transport
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralEventBatchLawLift g R)
    {σ : behavioralProfilePMFAt g}
    (h : (pmfBehavioralKernelGameAt g).IsNash σ) :
    (backendPMFBehavioralEventBatchTraceKernelGameAt g R lift).IsNash σ :=
  backendPMFBehavioralEventBatchTraceKernelGameAt_isNash_pullback g R lift h

/-- A proved pure specification event-batch law gives the canonical identity-backend
lift. This is the reusable smoke-test instance for backend transport. -/
noncomputable def backend_pure_identity_lift
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    (g : WFProgram P L) [FiniteDomains g]
    (law : PureSpecEventBatchLaw g) :
    BackendPureEventBatchLawLift g
      (Machine.StochasticStepRefinement.refl (eventGraphMachine g)) :=
  PureSpecEventBatchLaw.identityBackendLift g law

/-- A proved PMF-behavioral specification event-batch law gives the canonical
identity-backend lift. -/
noncomputable def backend_behavioral_identity_lift
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    (g : WFProgram P L) [FiniteDomains g]
    (law : BehavioralSpecEventBatchLaw g) :
    BackendBehavioralEventBatchLawLift g
      (Machine.StochasticStepRefinement.refl (eventGraphMachine g)) :=
  BehavioralSpecEventBatchLaw.identityBackendLift g law

end Vegas
