/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochStoppedCoupling
import Vegas.Pending.PhaseAcceptedOrder

/-! # Owned accepting words in the original completed attempt image -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem closing_receipt_record (ordered : graph.RevealRelaxedOrdered)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (before : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some before))
    (after : (app).Execution) (raw : RecoveryState graph)
    (changed : after.application.attempt ≠ before.execution.application.attempt)
    (effect : PhaseClosingEffect runtime leaks before.execution after raw) :
    (⟨before.execution.application.phases, before.execution.application.generation,
      before.execution.application.entry, raw, before.execution.application.retired⟩ :
        PhaseRuntimeState graph).ReceiptRecord := by
  have valid := phaseReceiptRecord_history runtime leaks ordered plan inputs horizon scheduler trace
  rcases effect with included | applied
  · obtain ⟨id, message, native, found, stepped, handled, rfl⟩ := included
    have phaseHandled : ∃ following,
        before.execution.application.handle runtime message = some following := by
      cases result : before.execution.application.handle runtime message with
      | none =>
          have literal := stepped
          simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at literal
          have equal := congrArg (fun execution : (app).Execution => execution.application)
            ((PMF.mem_support_pure_iff _ _).mp literal)
          have unchanged : after.application = before.execution.application := by
            simpa only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found,
              show (app).handle before.execution.application message = none from result,
              Option.getD_none] using equal
          exact (changed (congrArg PhaseRuntimeState.attempt unchanged)).elim
      | some following => exact ⟨following, rfl⟩
    obtain ⟨following, actual⟩ := phaseHandled
    unfold PhaseRuntimeState.handle at actual
    split at actual
    · rename_i allowed
      have flags := Bool.and_eq_true_iff.mp allowed
      have authorized := (Bool.and_eq_true_iff.mp flags.1).2
      have active : before.execution.application.current.excludedCall
          message.payload.packet.call = false := by
        cases blocked : before.execution.application.current.excludedCall
            message.payload.packet.call with
        | false => rfl
        | true =>
            simp only [blocked, Bool.not_true, Bool.false_eq_true] at flags
            exact flags.2.elim
      exact valid.inclusionResult runtime before.execution.application
        ⟨message.id, message.payload.packet.call⟩ native authorized active handled ordered
    · cases actual
  · obtain ⟨command, native, stepped, moved, rfl⟩ := applied
    have authorized : before.execution.application.commandAllowed command = true := by
      cases allowed : before.execution.application.commandAllowed command with
      | true => rfl
      | false =>
          have literal := stepped
          simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at literal
          obtain ⟨state, supported, equal⟩ := PMF.support_map .. ▸ literal
          change state ∈ (before.execution.application.environment runtime command).support
            at supported
          simp only [PhaseRuntimeState.environment, allowed, Bool.false_eq_true, ite_false,
            PMF.mem_support_pure_iff _ _] at supported
          subst state
          have unchanged : after.application = before.execution.application :=
            (congrArg (fun execution : (app).Execution => execution.application) equal).symm
          exact (changed (congrArg PhaseRuntimeState.attempt unchanged)).elim
    exact valid.environmentResult runtime before.execution.application command native authorized
      moved

end Vegas.EventGraphRuntime.ReservedEpoch

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


/-- Each active owner's complete original accepting word is its inherited
owned prefix followed by the accepting bit of its literal old frontier. The
full actual image and failed-attempt address record remain available. -/
theorem phaseProposalUnflagged_stopped_owned_word
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
    (remaining : Nat) (anchor : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨remaining, none, anchor⟩))
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (commitment : phase.kind = .commitment) :
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
        final.state = some ending ∧ TracePrefix trace prior ∧
        TracePrefix (prior.extend joint legal realized) final.trace ∧
        before.execution.application.attempt = anchor.application.attempt ∧
        PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
        phase.Finished (phase.drain raw) ∧
        (phase.drain raw).native.accepted = raw.native.accepted ∧
        (phase.drain raw).native.candidates = raw.native.candidates ∧
        PhaseProposal.sourceArchive ending.execution.network.inputs =
          PhaseProposal.sourceArchive anchor.network.inputs ∧
        (∀ owner, owner ∉ anchor.application.current.excluded →
          (∀ event, ¬ anchor.application.SeedRequest owner ⟨anchor.application.attempt, event⟩) →
          ∀ event ∈ phase.events, ∀ payload,
            (graph).outputLayout event = .binding owner payload →
              raw.native.accepted (.inr event) ≠ none) ∧
        (∀ owner frontier,
          anchor.application.SeedRequest owner ⟨anchor.application.attempt, frontier⟩ →
          ∀ event ∈ phase.events, ∀ payload,
            (graph).outputLayout event = .binding owner payload →
            (raw.native.accepted (.inr event) ≠ none ↔
              event.val < frontier.val ∨ raw.native.accepted (.inr frontier) ≠ none)) ∧
        (∀ event ∈ phase.events, (phase.drain raw).native.PublicFailure event ↔
          raw.native.accepted (.inr event) = none) ∧
        ((((phase.drain raw).excluded \ before.execution.application.entry.excluded) ∩
          phase.owners).Nonempty →
          (⟨anchor.application.attempt, (phase.drain raw).native⟩ : RetiredCommitAttempt graph) ∈
            ending.execution.application.retired ∧
          (anchor.application.attempt, (phase.drain raw).native.sourceFailureFootprint) ∈
            PhaseRuntimeState.sourceControlRecords ending.execution.application.retired) := by
  classical
  intro initial horizon scheduler players profile stopped final supported
  obtain ⟨ending, before, prior, joint, legal, realized, raw, stateEq, _idle, changed,
    fromStart, toFinal, same, phaseInstalled, _normalized, effect, finished, _valid, coverage,
    excluded, tables, candidates, archive, _receipts, failures, origins, record⟩ :=
    phaseProposalUnflagged_stopped_binding_image setup mode runtime leaks bounds plan complete
      coveredValues maximal ordered values fullValues tape activationGap processingGap gaps margin
        capacity remaining anchor trace phase installed commitment final supported
  have changedNow : ending.execution.application.attempt ≠
      before.execution.application.attempt := by simpa only [same] using changed
  have rawRecord := EventGraphRuntime.ReservedEpoch.closing_receipt_record runtime leaks ordered
    plan inputs horizon scheduler before ((menu).toRawTrace initial horizon scheduler prior)
      ending.execution raw changedNow effect
  have receiptOrder : BindingReceiptOrder phase.low before.execution.application.entry.excluded
      raw.native.accepted := rawRecord.ordered phase phaseInstalled commitment
  have rawStart := (menu).toRawTrace initial horizon scheduler trace
  have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler (fun state positive => by
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
      exact PhaseRuntimeState.initial_ordered plan draw) rawStart
  have anchorRecord := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
    rawStart
  refine ⟨ending, before, prior, joint, legal, realized, raw, stateEq, fromStart, toFinal, same,
    effect, finished, tables, candidates, archive, ?_, ?_, failures, record⟩
  · intro owner active noRequest event inside payload binding missing
    have survives : owner ∉ ending.execution.application.current.excluded := by
      intro failed
      obtain ⟨missed, _inside, request, _recorded, _failure⟩ := origins owner active failed
      exact noRequest missed request
    have ownerFailed := coverage.covered event owner
      ((graph).actor?_of_outputLayout_binding binding) ((failures event inside).mpr missing)
    rw [excluded] at ownerFailed
    exact survives ownerFailed
  · intro owner frontier request event inside payload binding
    obtain ⟨requestPhase, requestInstalled, frontierInside⟩ := request.2.1
    have phaseEq : requestPhase = phase := Option.some.inj
      ((Option.mem_def.mp requestInstalled).symm.trans (Option.mem_def.mp installed))
    subst requestPhase
    obtain ⟨frontierOwner, frontierPayload, frontierBinding⟩ := commitment ▸
      phase.fields frontier ((phase.mem_events frontier).mp frontierInside).1
        ((phase.mem_events frontier).mp frontierInside).2
    have ownerEq : frontierOwner = owner := Option.some.inj
      (((graph).actor?_of_outputLayout_binding frontierBinding).symm.trans request.2.2.2.1)
    subst frontierOwner
    have earlierRows := (anchorRecord.installed phase installed).ready_binding_receipts ordered
      frontier request.2.2.1 owner frontierPayload frontierBinding request.2.2.2.2
    constructor
    · intro accepting
      by_cases earlier : event.val < frontier.val
      · exact Or.inl earlier
      · right
        intro missing
        obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp accepting
        rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt earlier) with equal | later
        · have eventEq : frontier = event := Fin.ext equal
          subst event
          rw [accepted] at missing
          cases missing
        · exact (receiptOrder event owner payload candidate
            ((phase.mem_events event).mp inside).1 binding accepted).2 frontier
            ((phase.mem_events frontier).mp frontierInside).1 later frontierPayload frontierBinding
              missing
    · rintro (earlier | frontierAccepted)
      · have present := earlierRows.2 event ((phase.mem_events event).mp inside).1 earlier payload
          binding
        obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
        have preserved := EventGraphRuntime.ReservedEpoch.original_snapshot_preserves_accepted
          runtime leaks (menu) initial horizon scheduler ⟨remaining, none, anchor⟩ before
            ending.execution trace prior fromStart anchorOrdered same.symm raw effect phase
              (.inr event) candidate accepted
        rw [tables] at preserved
        rw [preserved]
        exact Option.some_ne_none _
      · have survives : owner ∉ ending.execution.application.current.excluded := by
          intro failed
          obtain ⟨missed, missedInside, missedRequest, _recorded, failure⟩ :=
            origins owner request.2.2.2.2 failed
          have sameFrontier : missed = frontier := ordered.ready_actor_unique
            anchor.application.current.native.config.cut request.2.2.1 missedRequest.2.2.1
              request.2.2.2.1 missedRequest.2.2.2.1
          subst missed
          exact frontierAccepted ((failures frontier missedInside).mp failure)
        intro missing
        have failure := (failures event inside).mpr missing
        have ownerFailed := coverage.covered event owner
          ((graph).actor?_of_outputLayout_binding binding) failure
        rw [excluded] at ownerFailed
        exact survives ownerFailed
end Vegas
