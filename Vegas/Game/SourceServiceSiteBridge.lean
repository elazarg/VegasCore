module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceAsyncStep
public import Vegas.Game.SourceServiceContinuation
public import Vegas.Source.DisclosureBehavioral

@[expose] public section

/-! # Ready sites and the initialized source law

A decision on the sequentialized graph is located by its ready site: the event
whose phase it lies in, that event's readiness, and that it is the only ready
event (`Vegas.ReadySite`). No plan position, roster or calendar is involved.

The source continuation from the initial boundary, averaged over the native
prior, is the source law (`Vegas.initialLaw_bind_sourceContinuation`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The position-free datum of a decision: the event whose phase the execution
is in, that event's readiness, and that it is the only ready event. -/
structure ReadySite (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup (Vegas.timeouts setup) leaks).Execution) where
  event : (graph setup).EventId
  ready : execution.application.config.cut.Ready event
  sole : execution.application.publicView.SoleReady event

/-! ## The initialized law -/

section Initialized

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The source continuation from the initial boundary, averaged over the
native prior, is the source law. -/
theorem initialLaw_bind_sourceContinuation (profile : BehavioralProfile setup.program) :
    (initialLaw setup).bind (fun state => sourceContinuation setup profile 0 state.config) =
      (setup.run profile).map some := by
  rw [initialLaw, serviceInitialLaw, PMF.bind_map, Setup.run, PMF.map_bind]
  congr 1
  funext initial
  simp only [Function.comp_apply, sourceContinuation, serviceSourcePrefix?_initial,
    Setup.continuationLaw, ProtocolState.continuationLaw_entry]
  rfl

variable {setup leaks} [Fintype Player]

end Initialized

/-- The complete clients preserve every observation of the original source's
typed state and public defaults once their first-turn source law holds. -/
theorem sourceServiceClientPolicy_outcome_law_of_firstTurn
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {duration : (serviceGraph setup mode).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
    {horizon turns : Nat} {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (original : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup mode duration leaks horizon scheduler bound turns
      (normalizeDisclosureProfile setup.program original))
    {Outcome : Type*}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    ((serviceApplication setup mode duration leaks).roundsFrom (serviceInitialLaw setup mode)
      scheduler (serviceClientPolicy setup mode duration leaks bound turns
        (firstTurnTiming setup turns mode) (normalizeDisclosureProfile setup.program original))
      horizon).map (fun execution =>
        (serviceSourceReadout setup mode duration leaks
          ((serviceApplication setup mode duration leaks).finished execution)).map
          (fun final => read (final.state, final.defaults))) =
      (setup.run original).map (fun final => some (read (final.state, final.defaults))) := by
  rw [sourceServiceClientPolicy_roundsFrom]
  have projected := congrArg
    (PMF.map (Option.map (fun final : Config Player L setup.program.terminalCtx =>
      read (final.state, final.defaults)))) terminal
  have normalized := congrArg (PMF.map (fun output => some (read output)))
    (setup.run_normalizeDisclosures_eq original)
  simp only [PMF.map_comp, Function.comp_def, Option.map_some]
    at projected normalized
  exact projected.trans normalized

variable [Finite Player]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Local native completion laws give the full first-turn source configuration law. -/
theorem firstTurnSourceLaw_of_completion_law
    {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (completes : (CompletesPlay timeouts) leaks (initialLaw setup) horizon scheduler)
    (completionLaw :
      let players := serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) profile
      let plan := (graph setup).policyPlan (compileEventProfile setup.program profile)
        (graph setup).canonicalScheduler
      let read := fun config : (graph setup).Config => decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
        config.history
      ∀ (event : (graph setup).EventId)
        (execution : (application setup timeouts leaks).Execution),
        CompletionBoundary setup leaks scheduler players event.val execution →
        execution.environmentRecall.length ≤ horizon →
        ((application setup timeouts leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
            (fun final => ((graph setup).runPlan plan final.application.config.remaining
              final.application.config).map read) =
          ((graph setup).runPlan plan execution.application.config.remaining
            execution.application.config).map read) :
    FirstTurnSourceLaw setup .sequential timeouts.duration leaks horizon scheduler bound turns
      profile := by
  classical
  let app := application setup timeouts leaks
  let players := serviceTurnPolicy setup .sequential timeouts.duration leaks bound turns
    (firstTurnTiming setup turns) profile
  let read := fun config : (graph setup).Config => decodeConfig? setup.program setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
    config.history
  have readEq (final : app.Execution) :
      sourceReadout setup timeouts leaks (app.finished final) = read final.application.config := by
    change serviceSourceReadout setup .sequential timeouts.duration leaks (some ⟨0, none,
      final⟩) = _
    rw [serviceSourceReadout_eq_decode]
  change (app.roundsFrom (initialLaw setup) scheduler players horizon).map
    (fun final => sourceReadout setup timeouts leaks (app.finished final)) = _
  rw [← initialLaw_bind_sourceContinuation setup profile, ReactiveApplication.roundsFrom,
    PMF.map_bind]
  apply bind_congr_on_support _
  intro native supported
  have nativeMember : native ∈
      (setup.initialLaw.map fun initial =>
        State.initial (graph := graph setup) (setup.eventInputs initial)).support := supported
  rw [PMF.support_map] at nativeMember
  obtain ⟨initial, _, sameNative⟩ := nativeMember
  subst native
  let execution := ReactiveApplication.Execution.initial app
    (State.initial (graph := graph setup) (setup.eventInputs initial))
  have boundary : CompletionBoundary setup leaks scheduler players 0 execution := by
    refine ⟨?_, EventOrder.Cut.empty_isPrefix _, ?_⟩
    · change execution ∈ (app.roundsFrom (initialLaw setup) scheduler players 0).support
      rw [ReactiveApplication.roundsFrom, PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨_, supported, by simp [ReactiveApplication.runRounds, execution]⟩
    · intro event _ observer entry member
      cases member
  have configLaw := CompletionBoundary.runToHorizon_law setup timeouts leaks
    (compileEventProfile setup.program profile) read completes completionLaw execution boundary
      (Nat.zero_le _)
  change (app.runRounds scheduler players horizon execution).map
      (fun final => read final.application.config) = _ at configLaw
  calc
    _ = (app.runRounds scheduler players horizon execution).map
        (fun final => read final.application.config) :=
      map_congr_on_support _ (fun final _ => readEq final)
    _ = ((graph setup).runPlan
        ((graph setup).policyPlan (compileEventProfile setup.program profile)
          (graph setup).canonicalScheduler)
        execution.application.config.remaining execution.application.config).map read := configLaw
    _ = sourceContinuation setup profile 0 execution.application.config :=
      (SourceResidual.initial setup profile initial).runPlan_readout_law

end Vegas
