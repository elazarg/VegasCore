/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceSettledEvidence
import Vegas.Pending.ReactiveSettledCollection

/-! # Final rejection of an opening whose public guards fail

Every guard input is available once the opening's event is ready. Arbitrary
later responses and scheduler commands retain those values, so the signed
opening's public guard verdict cannot change. At complete settlement a false
verdict defeats the actual settled content check, even for an exact certified
opening that the runtime accepted.

Authentic final-record coverage then supplies collection from the actual
persisted packet under arbitrary later policies. Neither source utility nor
private certificate capability is restricted by these results.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph
  GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

private def guardVerdict (event : (serviceGraph setup mode).EventId)
    (packet : WitnessedPacket (serviceGraph setup mode)) (verdict : Bool)
    (state : EventGraphRuntime.State (serviceGraph setup mode)) : Prop :=
  (∀ predecessor ∈ (serviceGraph setup mode).order.predecessors event,
    predecessor ∈ state.config.cut.completed) ∧
    state.publicView.openingGuardsAccepted packet = verdict

private theorem guardVerdict_step
    {before after : EventGraphRuntime.State (serviceGraph setup mode)}
    (step : ContractStep before after) (event : (serviceGraph setup mode).EventId)
    (packet : WitnessedPacket (serviceGraph setup mode))
    (named : packet.call.event? (serviceGraph setup mode) = some event)
    (verdict : Bool) (held : guardVerdict event packet verdict before) :
    guardVerdict event packet verdict after := by
  refine ⟨fun predecessor member => step.completed_mono (held.1 predecessor member), ?_⟩
  rw [State.openingGuardsAccepted_congr before after packet event named held.1
    (fun field value stored => step.store_retained field value stored)]
  exact held.2

private theorem guardVerdict_respond
    (execution : (serviceApplication setup mode deadline leaks).Execution) (responder : Player)
    (response : (serviceApplication setup mode deadline leaks).Action) (event :
        (serviceGraph setup mode).EventId)
    (packet : WitnessedPacket (serviceGraph setup mode)) (verdict : Bool)
    (held : guardVerdict event packet verdict execution.application) :
    guardVerdict event packet verdict
      (execution.respond
          (serviceApplication setup mode deadline leaks) responder response).application := by
  obtain ⟨configEq, publicEq⟩ :=
    (serviceRuntime setup mode deadline).reactive_respond_application leaks execution responder
        response
  refine ⟨fun predecessor member => configEq ▸ held.1 predecessor member, ?_⟩
  rw [publicEq]
  exact held.2

private def guardVerdictAtState (event : (serviceGraph setup mode).EventId)
    (packet : WitnessedPacket (serviceGraph setup mode)) (verdict : Bool) :
    (serviceApplication setup mode deadline leaks).ProtocolState → Prop
  | none => False
  | some control => guardVerdict event packet verdict control.execution.application

private theorem guardVerdictAtState_transition
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (event : (serviceGraph setup mode).EventId) (packet : WitnessedPacket (serviceGraph setup mode))
    (named : packet.call.event? (serviceGraph setup mode) = some event) (verdict : Bool)
    (before after : (serviceApplication setup mode deadline leaks).ProtocolState)
    (joint : Player → Option (serviceApplication setup mode deadline leaks).Action)
    (held : guardVerdictAtState event packet verdict before)
    (reached : after ∈ ((serviceApplication setup mode deadline leaks).transition
        (serviceInitialLaw setup mode) horizon
      scheduler before joint).support) : guardVerdictAtState event packet verdict after := by
  cases before with
  | none => exact held.elim
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some responder =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact guardVerdict_respond execution responder _ event packet verdict held
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact held
          | succ remaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              exact guardVerdict_step
                (contractStep_environment
                    (serviceRuntime setup mode deadline) leaks execution next command supported)
                event packet named verdict held

private theorem guardVerdictAtState_reaches
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {first last :
      ((serviceApplication setup mode deadline leaks).protocol
          (serviceInitialLaw setup mode) horizon scheduler).History}
    {fuel : Nat}
    (path : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).ReachesWithin
      fuel first last) (event : (serviceGraph setup mode).EventId) (packet : WitnessedPacket
          (serviceGraph setup mode))
    (named : packet.call.event? (serviceGraph setup mode) = some event) (verdict : Bool)
    (held : guardVerdictAtState event packet verdict first.state) :
    guardVerdictAtState event packet verdict last.state := by
  induction path with
  | refl => exact held
  | step joint legal reached rest ih =>
      exact ih (guardVerdictAtState_transition event packet named verdict _ _ joint held reached)

/-- Once an actual event is ready, the public guard verdict of a packet naming
it is fixed under arbitrary later player responses and scheduler commands.
The final event need not yet be completed. -/
theorem ready_openingGuardsAccepted_reaches
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {first last :
      ((serviceApplication setup mode deadline leaks).protocol
          (serviceInitialLaw setup mode) horizon scheduler).History}
    {fuel : Nat}
    (path : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).ReachesWithin
      fuel first last)
    (before after : (serviceApplication setup mode deadline leaks).Control)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (event : (serviceGraph setup mode).EventId)
        (ready : before.execution.application.config.cut.Ready event)
    (packet : WitnessedPacket (serviceGraph setup mode))
    (named : packet.call.event? (serviceGraph setup mode) = some event) :
    after.execution.application.publicView.openingGuardsAccepted packet =
      before.execution.application.publicView.openingGuardsAccepted packet := by
  have initial : guardVerdictAtState event packet
      (before.execution.application.publicView.openingGuardsAccepted packet) first.state := by
    rw [firstState]
    exact ⟨ready.2, rfl⟩
  have final := guardVerdictAtState_reaches path event packet named _ initial
  rw [lastState] at final
  exact final.2

/-- A false guard verdict defeats settled content at every complete actual
continuation, even when the opening is certified and has an accepting receipt.
Certification is unrestricted because guard failure alone suffices. -/
theorem guardFailingOpening_forbidden_reaches
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {first last :
      ((serviceApplication setup mode deadline leaks).protocol
          (serviceInitialLaw setup mode) horizon scheduler).History}
    {fuel : Nat}
    (path : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).ReachesWithin
      fuel first last)
    (before after : (serviceApplication setup mode deadline leaks).Control)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (event : (serviceGraph setup mode).EventId)
        (ready : before.execution.application.config.cut.Ready event)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (candidate : Handle (serviceGraph setup mode)) (raw : Raw L)
    (opened : message.payload.call = .opening event candidate raw)
    (rejected : before.execution.application.publicView.openingGuardsAccepted message.payload =
      false)
    (complete : after.execution.application.config.cut.Terminal) :
    ¬ ((serviceRuntime setup mode deadline).settledRecord leaks after.execution).SettledContent
        message ∧
      ((serviceRuntime setup mode deadline).settledRecord leaks after.execution).permits message =
          false := by
  have named : message.payload.call.event? (serviceGraph setup mode) = some event := by
    rw [opened]
    rfl
  have guarded := ready_openingGuardsAccepted_reaches path before after firstState lastState
    event ready message.payload named
  have contentFails : ¬
      ((serviceRuntime setup mode deadline).settledRecord leaks after.execution).SettledContent
      message := by
    intro content
    unfold SettledRecord.SettledContent at content
    rw [opened] at content
    have accepted := content.2
    change after.execution.application.publicView.openingGuardsAccepted message.payload = true
      at accepted
    rw [guarded, rejected] at accepted
    cases accepted
  refine ⟨contentFails, SettledRecord.permits_eq_false_of_settled _ message event named ?_
    (fun accepted => contentFails accepted.2)⟩
  apply (after.execution.application.config.history_exact event).mpr
  rw [complete]
  exact Finset.mem_univ event

variable [Fintype Player]

/-- Authentic final-record coverage collects for a persisted guard-failing
opening under every later behavioral policy. Complete play supplies the final
forbidden verdict from the actual ready prefix and preserved guard fields. -/
theorem guardFailingOpening_collection_continuation
    (menu : (serviceApplication setup mode deadline leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (completes : CompletesPlay (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler)
    (service : EvidenceReportService
      (SettledRecord (serviceGraph setup mode) × Message Player (WitnessedPacket
          (serviceGraph setup mode))))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage service observationRate deliveryRate)
    (profile : ∀ player,
      (menu.information (serviceInitialLaw setup mode) horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol
        (serviceInitialLaw setup mode) horizon scheduler).History)
    (long : 2 * horizon + 1 ≤ history.trace.length + fuel)
    (before : (serviceApplication setup mode deadline leaks).Control) (current : history.state =
        some before)
    (record : (serviceApplication setup mode deadline leaks).TrafficRecord)
    (present : record ∈ (serviceApplication setup mode deadline leaks).stateTraffic history.state)
    (event : (serviceGraph setup mode).EventId)
        (ready : before.execution.application.config.cut.Ready event)
    (candidate : Handle (serviceGraph setup mode)) (raw : Raw L)
    (opened : record.envelope.payload.call = .opening event candidate raw)
    (rejected : before.execution.application.publicView.openingGuardsAccepted
      record.envelope.payload = false) :
    observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
      expect ((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioralFrom
        profile fuel history)
        (fun final => TerminalAudit.charge
            ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
          ((serviceRuntime setup mode deadline).serviceAudit leaks fun settled =>
            (serviceApplication setup mode deadline leaks).sampledTrafficAudit
              (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
              (fun evidence => evidence.1.permits evidence.2) service.sample)
          final.state record.envelope.sender) := by
  let app := serviceApplication setup mode deadline leaks
  let model := menu.information (serviceInitialLaw setup mode) horizon scheduler
  let protocol := menu.protocol (serviceInitialLaw setup mode) horizon scheduler
  apply (serviceRuntime setup mode deadline).settledPacket_collection_continuation leaks menu
      (serviceInitialLaw setup mode)
    horizon scheduler service observationRate deliveryRate delivery_nonnegative coverage
    profile fuel history record present
  intro final supported after finalState
  have stopped : app.terminal final.state := by
    rcases protocol.runRandomizedFor_terminal_or_length (model.randomizedChooser profile)
        fuel history final supported with terminal | length
    · exact terminal
    · have traceBound := app.trace_bound (serviceInitialLaw setup mode) horizon scheduler
        (menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler final.trace)
      rw [menu.toRawTrace_length] at traceBound
      have exhausted : app.rank horizon final.state = 0 := by omega
      exact (app.rank_zero horizon final.state).mp exhausted
  have rawTrace : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some after) :=
    finalState ▸ menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler final.trace
  have complete := completes after rawTrace (finalState ▸ stopped)
  have path := protocol.runRandomizedFor_reachesWithin (model.randomizedChooser profile)
    fuel history final supported
  exact (guardFailingOpening_forbidden_reaches
    (menu.reaches_raw
        (serviceInitialLaw setup mode) horizon scheduler path) before after current finalState
    event ready record.envelope candidate raw opened rejected complete).2

end Vegas
