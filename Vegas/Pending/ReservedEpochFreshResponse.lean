/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochFirstAcceptance
import Vegas.Pending.PhaseBindingReceiptResolution
import Vegas.Pending.PhaseConsistentContinuation

/-! # An actual protected first response cannot later expire on its continuation -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The actual earliest counted SEND has protected delivery against arbitrary
foreign continuation. It cannot coexist with a later due request expiring in
that same physical coordinate. Both histories and all old unsafe episodes are
literal; no assumption of a surviving endpoint is made. -/
theorem first_ready_response_cannot_expire {length : Nat} (tape : Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (completionCycles runtime) activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) (executionHorizon runtime)
        (family runtime leaks (packetCapacity runtime) tape)).Trace
          (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨execution.application.attempt, event⟩ (execution.recall owner))
    (material : WitnessedSubmission graph)
    (certificate : ReadyCall execution.application material.call.packet event)
    (offered : (⟨some material⟩ : (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
      owner (execution.recall owner) (execution.observe (app) owner))
    (postTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime) (family runtime leaks (packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, execution.respond (app) owner ⟨some material⟩⟩))
    (dueControl : (app).Control)
    (dueTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime) (family runtime leaks (packetCapacity runtime) tape)).Trace
        (some dueControl))
    (dueRequest : dueControl.execution.application.SeedRequest owner
      ⟨execution.application.attempt, event⟩)
    (due : runtime.deadline event ≤ dueControl.execution.application.current.native.clock -
      (dueControl.execution.application.current.native.activatedAt event).getD
        dueControl.execution.application.current.native.clock)
    (expired : (app).Execution) (expiryRemaining : Nat)
    (expiry : expired ∈ (dueControl.execution.environmentStep (app)
      (.application (.expire event))).support)
    (expiryTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime) (family runtime leaks (packetCapacity runtime) tape)).Trace
        (some ⟨expiryRemaining, none, expired⟩))
    (kept : TracePrefix postTrace expiryTrace)
    (players : Player → (app).Policy)
    (consistent : ∀ who, (players who).Consistent (expired.recall who))
    (covered : ∀ past view action, action ∈ (players owner past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks owner past view action) : False := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := family runtime leaks (packetCapacity runtime) tape
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let after := execution.respond (app) owner ⟨some material⟩
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner),
      (app).packet ((app).submit execution.application owner material) owner
        (execution.network.known owner) material⟩
  obtain ⟨final, future⟩ :=
    ((app).runRounds scheduler players expiryRemaining expired).support_nonempty
  have atExpiry : (app).finished final ∈ ((app).finish initial (executionHorizon runtime)
      scheduler players (some ⟨expiryRemaining, none, expired⟩)).support := by
    simpa only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] using
      (PMF.mem_support_map_iff (app).finished _ _).mpr ⟨final, future, rfl⟩
  have atResponse := phase_finish_supported_of_consistent_prefix runtime leaks initial
    (executionHorizon runtime) scheduler players ⟨remaining, none, after⟩
      ⟨expiryRemaining, none, expired⟩ postTrace expiryTrace kept consistent _ atExpiry
  have fullFuture : final ∈ ((app).runRounds scheduler players remaining after).support := by
    change (app).finished final ∈
      ((((app).resume players none after).bind
        ((app).runRounds scheduler players remaining)).map (app).finished).support at atResponse
    simp only [ReactiveApplication.resume, PMF.pure_bind] at atResponse
    obtain ⟨chosen, chosenSupport, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp atResponse
    have controls : (⟨0, none, chosen⟩ : (app).Control) = ⟨0, none, final⟩ :=
      Option.some.inj equal
    have same : chosen = final :=
      congrArg (fun control : (app).Control => control.execution) controls
    exact same ▸ chosenSupport
  have raw := menu.toRawTrace initial (executionHorizon runtime) scheduler trace
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs
    (executionHorizon runtime) scheduler raw
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff event).mpr
      ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
  have permitted : PhaseCount.OnePacketResponse runtime leaks owner (execution.recall owner)
      (execution.observe (app) owner) ⟨some material⟩ := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp offered).2
      with silent | transmitted
    · cases silent
    · exact transmitted
  have countClean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial (executionHorizon runtime) (fun state _ => PhaseCount.countClean_initial runtime leaks
      state) trace
  have clean : PhaseCount.OwnCountClean runtime leaks owner execution :=
    ⟨countClean.1, fun packet present _ => countClean.2 packet present⟩
  have receipt := first_response_receipt runtime leaks tape activationGap processingGap gaps margin
    plan ordered maximal inputs remaining owner execution raw event entered request stamp first
      clean material certificate permitted players covered final fullFuture
  have input : message ∈ after.network.inputs :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have inputInvariant : (app).PolicyInvariant players (fun state =>
      message ∈ state.network.inputs) := {
    respond := by
      intro current actor action present _supported
      rcases action with ⟨_ | submission⟩
      · exact present
      · exact List.mem_append_left _ present
    environment := by
      intro current next command present moved
      rw [(app).environmentStep_inputs current next command moved]
      exact present }
  have finalInput := inputInvariant.runRounds scheduler remaining after final input fullFuture
  have forbidden := PhaseService.not_bindingAccepted_runRounds_after_expire runtime leaks plan
    inputs (executionHorizon runtime) scheduler dueTrace ⟨execution.application.attempt, event⟩
      owner dueRequest due expired expiry players expiryRemaining final future
  apply forbidden
  refine ⟨message, finalInput, rfl, rfl, ?_, receipt⟩
  change (PhaseRuntimeState.emit (execution.application.submit owner material) owner
    (execution.network.known owner) material).packet.call.event? graph = some event
  rw [phase_emit_call]
  cases certificate with
  | binding candidate call => rw [call]; rfl
  | opening owner payload binding checks outputEq codeEq node candidate raw call associated =>
      rw [call]
      rfl

end Vegas.EventGraphRuntime.ReservedEpoch
