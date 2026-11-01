/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceAsyncStep
import Vegas.Game.SourceServiceContinuation

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
    (execution : (application setup (Vegas.runtime setup) leaks).Execution) where
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

variable [Finite Player]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Local native completion laws give the full first-turn source configuration law. -/
theorem firstTurnSourceLaw_of_completion_law
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (completes : runtime.CompletesPlay leaks (initialLaw setup) horizon scheduler)
    (completionLaw :
      let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) profile
      let plan := (graph setup).policyPlan (compileEventProfile setup.program profile)
        (graph setup).canonicalScheduler
      let read := fun config : (graph setup).Config => decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
        config.history
      ∀ (event : (graph setup).EventId)
        (execution : (application setup runtime leaks).Execution),
        CompletionBoundary setup leaks scheduler players event.val execution →
        execution.environmentRecall.length ≤ horizon →
        ((application setup runtime leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
            (fun final => ((graph setup).runPlan plan final.application.config.remaining
              final.application.config).map read) =
          ((graph setup).runPlan plan execution.application.config.remaining
            execution.application.config).map read) :
    FirstTurnSourceLaw setup .sequential runtime.deadline leaks horizon scheduler bound turns
      profile := by
  classical
  let app := application setup runtime leaks
  let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
    (firstTurnTiming setup turns) profile
  let read := fun config : (graph setup).Config => decodeConfig? setup.program setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
    config.history
  have readEq (final : app.Execution) :
      sourceReadout setup runtime leaks (app.finished final) = read final.application.config := by
    change serviceSourceReadout setup .sequential runtime.deadline leaks (some ⟨0, none, final⟩) = _
    rw [serviceSourceReadout_eq_decode]
    simp only [read, show setup.eventGraph.fromModeCompletion .sequential = id from rfl,
      List.map_id]
  change (app.roundsFrom (initialLaw setup) scheduler players horizon).map
    (fun final => sourceReadout setup runtime leaks (app.finished final)) = _
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
  have configLaw := CompletionBoundary.runToHorizon_law setup runtime leaks
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
