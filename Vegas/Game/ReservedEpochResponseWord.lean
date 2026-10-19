/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochOriginalWord
import Vegas.Pending.ReservedEpochActiveSlot

/-! # The complete original word after an actual counted current response -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs


open scoped Classical in
/-- Any legal counted response at an actual reserved-service binding callback
has the complete anchor/tape word law. The processing-position premise is
derived from the selected activation, including WAIT and unusable responses. -/
theorem phaseProposalUnflagged_response_acceptance_word
    (complete : leaks = MessageNetwork.completePendingObservation)
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (remaining : Nat) (active : (app).Execution) (actor : Player) (response : (app).Action)
    (activeTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨remaining, some actor, active⟩))
    (available : response ∈ (menu).actions actor (active.recall actor) (active.observe app actor))
    (phase : RuntimePhase graph) (installed : phase ∈ active.application.phases.head?)
    (commitment : phase.kind = .commitment) :
    let anchor := active.respond app actor response
    ∃ trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨remaining, none, anchor⟩),
    let initial := (inputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := ReactiveApplication.anchoredPolicy anchor
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ anchor.application.attempt
    ∀ final ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, anchor⟩, trace⟩).support,
      ∃ (ending before : (app).Control)
        (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
        (joint : Player → Option (app).Action)
        (legal : ((menu).protocol initial horizon scheduler).Legal (some before) joint)
        (realized : some ending ∈ ((app).transition initial horizon scheduler
          (some before) joint).support) (raw : RecoveryState graph),
        final.state = some ending ∧ ending.actor = none ∧
        ending.execution.application.attempt ≠ anchor.application.attempt ∧
        TracePrefix trace prior ∧
        TracePrefix (prior.extend joint legal realized) final.trace ∧
        before.execution.application.attempt = anchor.application.attempt ∧
        phase ∈ before.execution.application.phases.head? ∧
        PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
        phase.Finished (phase.drain raw) ∧
        (phase.drain raw).native.accepted = raw.native.accepted ∧
        (phase.drain raw).native.candidates = raw.native.candidates ∧
        PhaseProposal.sourceArchive ending.execution.network.inputs =
          PhaseProposal.sourceArchive anchor.network.inputs ∧
        before.execution.application.retired = anchor.application.retired ∧
        ending.execution.application.retired = anchor.application.retired ++
          (if (((phase.drain raw).excluded \ anchor.application.entry.excluded) ∩
              phase.owners).Nonempty then
            [⟨anchor.application.attempt, (phase.drain raw).native⟩] else []) ∧
        (∀ event ∈ phase.events, ∀ owner payload,
          (graph).outputLayout event = .binding owner payload →
          (raw.native.accepted (.inr event) ≠ none ↔
            ReservedEpoch.ownedAcceptanceWord runtime leaks tape anchor owner event)) ∧
        (let failed := fun event : (graph).EventId =>
          if event.val < phase.low then anchor.application.entry.native.PublicFailure event
          else if event.val < phase.high then ∃ owner, (graph).actor? event = some owner ∧
            ¬ ReservedEpoch.ownedAcceptanceWord runtime leaks tape anchor owner event else False
         (phase.drain raw).native.sourceFailureFootprint =
          (fun rank => Finset.univ.filter fun owner => ∃ event : (graph).EventId,
            event.val < rank ∧ (graph).actor? event = some owner ∧ failed event,
           Finset.univ.filter fun owner => ∃ event : (graph).EventId,
            (graph).actor? event = some owner ∧ failed event)) := by
  classical
  intro anchor
  let initial := (inputs).map (PhaseRuntimeState.initial plan)
  let horizon := ReservedEpoch.executionHorizon runtime
  let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
  obtain ⟨trace⟩ := (menu).trace_respond initial horizon scheduler remaining active actor response
    activeTrace available
  have positioned := ReservedEpoch.active_after_processing runtime leaks
    (ReservedEpoch.packetCapacity runtime) tape initial horizon ⟨remaining, some actor, active⟩
      ((menu).toRawTrace initial horizon scheduler activeTrace) actor rfl
  have afterProcessing : ReservedEpoch.packetCapacity runtime ≤ anchor.environmentRecall.length %
      ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime) := by
    simpa only [anchor, (app).respond_environmentRecall] using positioned
  have installedAfter : phase ∈ anchor.application.phases.head? := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact installed
    | some material => exact installed
  refine ⟨trace, ?_⟩
  exact phaseProposalUnflagged_stopped_acceptance_word setup mode runtime leaks bounds plan
    complete coveredValues maximal ordered values fullValues tape activationGap processingGap gaps
      margin capacity remaining anchor trace phase installedAfter commitment afterProcessing

end Vegas
