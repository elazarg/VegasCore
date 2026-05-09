import Vegas.Backend.KernelGame

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

/-- Backend refinement plus a compatible pure block-law lift transports Nash
equilibria from the public pure specification game to the backend blocked-trace
game. -/
theorem backend_pure_nash_transport
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendPureBlockLawLift g R)
    {σ : pureProfileAt g}
    (h : (pureKernelGameAt g).IsNash σ) :
    (backendBlockedTraceKernelGameAt g R lift).IsNash σ :=
  backendBlockedTraceKernelGameAt_isNash_pullback_pure g R lift h

/-- Backend refinement plus a compatible PMF-behavioral block-law lift
transports Nash equilibria from the public PMF-behavioral specification game to
the backend blocked-trace game. -/
theorem backend_behavioral_nash_transport
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    (g : WFProgram P L) [FiniteDomains g]
    {Impl : Machine P}
    (R : Machine.StochasticStepRefinement Impl (eventGraphMachine g))
    (lift : BackendBehavioralBlockLawLift g R)
    {σ : behavioralProfilePMFAt g}
    (h : (pmfBehavioralKernelGameAt g).IsNash σ) :
    (backendPMFBehavioralBlockedTraceKernelGameAt g R lift).IsNash σ :=
  backendPMFBehavioralBlockedTraceKernelGameAt_isNash_pullback_behavioral
    g R lift h

end Vegas
