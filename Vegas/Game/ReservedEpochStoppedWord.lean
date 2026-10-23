/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ReservedEpochStoppedUnsentBinding

/-! # Owned accepting words in the original completed attempt image -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem closing_receipt_record (ordered : graph.RevealRelaxedOrdered)
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

private theorem same_namespace_accepted_table (state : PhaseRuntimeState graph)
    (ordered : state.Ordered) (same : state.attempt = state.normalize.attempt) :
    state.normalize.current.native.accepted = state.current.native.accepted := by
  have settled := PhaseRuntimeState.settle_of_same_namespace state.phases state.generation
    state.entry state.current state.retired ordered same
  have currentEq := congrArg PhaseRuntimeState.current settled
  change (PhaseRuntimeState.settle state.phases state.generation state.entry state.current
    state.retired).current.native.accepted = state.current.native.accepted
  rw [currentEq]
  cases phases : state.phases with
  | nil => rfl
  | cons phase rest => exact (phase.drain_tables state.current).1

private theorem excluded_accepted_step (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : graph.outputLayout event = .binding owner payload) :
    (app).StepRelation (fun before after => before.Ordered →
      before.attempt = after.attempt → owner ∈ before.current.excluded →
      after.current.native.accepted (.inr event) =
        before.current.native.accepted (.inr event)) where
  refl _ _ _ _ := rfl
  submit state who material _ _ _ := by
    change (submitStep (material.call.register state.current.native who) who
      material.call.packet).accepted (.inr event) = _
    rw [submitStep_accepted, Submission.register_accepted]
  handle state message next accepted ordered same excluded := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      rw [same_namespace_accepted_table
        ({ state with current :=
          state.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph) ordered same]
      change native.accepted (.inr event) = _
      rcases handle_tables_cases runtime state.current.native native _ handled with
        ⟨selected, candidate, call, _candidates, table, _sender⟩ | ⟨table, _candidates⟩
      · change message.payload.packet.call = .commitment selected candidate at call
        have different : selected ≠ event := by
          intro equal
          subst selected
          have blocked : state.current.excludedCall message.payload.packet.call = true := by
            simp only [call, RecoveryState.excludedCall, Payload.event?,
              RecoveryState.excludedEvent, (graph).actor?_of_outputLayout_binding binding,
              Option.any_some, excluded, decide_true]
          simp only [blocked, Bool.not_true, Bool.and_false, Bool.false_eq_true] at allowed
        rw [table, Function.update_of_ne (by simpa using different.symm)]
      · rw [table]
    · cases accepted
  environment state command next reached ordered same _ := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      rw [same_namespace_accepted_table
        ({ state with current := state.current.environmentResult command native } :
          PhaseRuntimeState graph) ordered same]
      exact congrFun (environmentStep_tables runtime _ native command supported).1 (.inr event)
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl

/-- A literal same-namespace prefix keeps the prior archive and every inherited
excluded owner's accepted row. Namespace monotonicity rules out a restore. -/
private theorem same_namespace_record_prefix
    (menu : (app).ResponseMenu) (initial : PMF (app).State)
    (initialized : ∀ state ∈ initial.support, state.Ordered) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (final : (menu.protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior final) (ordered : before.execution.application.Ordered)
    (same : before.execution.application.attempt = after.execution.application.attempt) :
    after.execution.application.retired = before.execution.application.retired ∧
      before.execution.application.current.excluded ⊆ after.execution.application.current.excluded ∧
      ∀ owner ∈ before.execution.application.current.excluded, ∀ event payload,
        graph.outputLayout event = .binding owner payload →
        after.execution.application.current.native.accepted (.inr event) =
          before.execution.application.current.native.accepted (.inr event) := by
  have along : ∀ {target} {targetTrace : (menu.protocol initial horizon scheduler).Trace target},
      TracePrefix prior targetTrace → ∃ next : (app).Control, target = some next ∧
        next.execution.application.Ordered ∧
        before.execution.application.current.excluded ⊆
          next.execution.application.current.excluded ∧
        before.execution.application.attempt.generation ≤
          next.execution.application.attempt.generation ∧
        before.execution.application.attempt.phase ≤ next.execution.application.attempt.phase ∧
        (before.execution.application.attempt = next.execution.application.attempt →
          ∀ owner ∈ before.execution.application.current.excluded, ∀ event payload,
            graph.outputLayout event = .binding owner payload →
            next.execution.application.current.native.accepted (.inr event) =
              before.execution.application.current.native.accepted (.inr event)) := by
    intro target targetTrace retained
    induction retained with
    | refl =>
        exact ⟨before, rfl, ordered, Finset.Subset.refl _, le_rfl, le_rfl,
          fun _ _ _ _ _ _ => rfl⟩
    | @extend source target earlier retained joint legal reached ih =>
        obtain ⟨middle, rfl, middleOrdered, middleExcluded, lowerGen, lowerPhase, previous⟩ := ih
        have realized : target ∈ ((app).transition initial horizon scheduler (some middle)
            joint).support := reached
        obtain ⟨next, rfl, _⟩ := (app).transition_recall_prefix initial horizon scheduler
          middle target joint realized
        have nextOrdered := (phaseApplication_seedOrder runtime leaks).transition initial horizon
          scheduler initialized (some middle) (some next) joint middleOrdered realized
        have progress := (phaseApplication_namespace_progress runtime leaks).transition initial
          horizon scheduler middle next joint realized middleOrdered
        have nextExcluded := (phaseApplication_exclusion_monotone runtime leaks).transition initial
          horizon scheduler middle next joint realized
        refine ⟨next, rfl, nextOrdered, middleExcluded.trans nextExcluded,
          lowerGen.trans progress.1, lowerPhase.trans progress.2, ?_⟩
        intro finalSame
        have intermediate : before.execution.application.attempt =
            middle.execution.application.attempt := by
          have generation := congrArg CommitAttemptId.generation finalSame
          have phase := congrArg CommitAttemptId.phase finalSame
          cases first : before.execution.application.attempt with
          | mk firstPhase firstGeneration =>
              cases second : middle.execution.application.attempt with
              | mk secondPhase secondGeneration =>
                  simp only [first, second] at lowerGen lowerPhase progress generation phase ⊢
                  congr 1 <;> omega
        have priorRows := previous intermediate
        intro owner excluded event payload binding
        exact ((excluded_accepted_step runtime leaks owner event payload binding).transition
          initial horizon scheduler middle next joint realized middleOrdered
            (intermediate.symm.trans finalSame) (middleExcluded excluded)).trans
              (priorRows owner excluded event payload binding)
  obtain ⟨next, equal, _, excluded, _, _, result⟩ := along kept
  cases Option.some.inj equal
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized
    horizon scheduler before after prior final kept ordered same
  exact ⟨(congrArg Prod.snd metadata).symm, excluded, result same⟩

private theorem excluded_closing_accepted
    (before : (app).Control) (after : (app).Execution) (raw : RecoveryState graph)
    (changed : after.application.attempt ≠ before.execution.application.attempt)
    (effect : PhaseClosingEffect runtime leaks before.execution after raw)
    (owner : Player) (excluded : owner ∈ before.execution.application.current.excluded)
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) :
    raw.native.accepted (.inr event) =
      before.execution.application.current.native.accepted (.inr event) := by
  rcases effect with included | applied
  · obtain ⟨id, message, native, found, stepped, handled, rfl⟩ := included
    rcases handle_tables_cases runtime before.execution.application.current.native native _ handled
        with ⟨selected, candidate, call, _candidates, table, _sender⟩ | ⟨table, _candidates⟩
    · change message.payload.packet.call = .commitment selected candidate at call
      have different : selected ≠ event := by
        intro equal
        subst selected
        have blocked : before.execution.application.current.excludedCall
            message.payload.packet.call = true := by
          simp only [call, RecoveryState.excludedCall, Payload.event?,
            RecoveryState.excludedEvent, (graph).actor?_of_outputLayout_binding binding,
            Option.any_some, excluded, decide_true]
        have rejected : before.execution.application.handle runtime message = none := by
          simp only [PhaseRuntimeState.handle, blocked, Bool.not_true, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte]
        have literal := stepped
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at literal
        have executionEq := (PMF.mem_support_pure_iff _ _).mp literal
        have unchanged : after.application = before.execution.application := by
          have projected := congrArg (fun execution : (app).Execution => execution.application)
            executionEq
          simpa only [ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found,
            show (app).handle before.execution.application message = none from rejected,
            Option.getD_none] using projected
        exact changed (congrArg PhaseRuntimeState.attempt unchanged)
      change native.accepted (.inr event) = _
      rw [table, Function.update_of_ne (by simpa using different.symm)]
    · exact congrFun table (.inr event)
  · obtain ⟨command, native, _stepped, moved, rfl⟩ := applied
    exact congrFun (environmentStep_tables runtime _ native command moved).1 (.inr event)

private theorem settle_self_retired (phases : List (RuntimePhase graph))
    (generation : Nat) (state : RecoveryState graph) (retired : List (RetiredCommitAttempt graph)) :
    (PhaseRuntimeState.settle phases generation state state retired).retired = retired := by
  classical
  induction phases generalizing state with
  | nil => rfl
  | cons phase rest ih =>
      by_cases finished : phase.Finished (phase.drain state)
      · rw [PhaseRuntimeState.settle_clean phase rest generation state state retired finished
          (fun failed => PhaseRuntimeState.automatic_no_new_miss phase state failed.2)]
        exact ih (phase.drain state)
      · simp only [PhaseRuntimeState.settle, finished, ↓reduceIte]

private theorem closing_retired_word (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (installed : phase ∈ state.phases.head?)
    (commitment : phase.kind = .commitment) (raw : RecoveryState graph)
    (finished : phase.Finished (phase.drain raw)) :
    ({ state with current := raw } : PhaseRuntimeState graph).normalize.retired =
      state.retired ++
        (if (((phase.drain raw).excluded \ state.entry.excluded) ∩ phase.owners).Nonempty then
          [⟨state.attempt, (phase.drain raw).native⟩] else []) := by
  classical
  obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have address : state.attempt = ⟨phase.low, state.generation⟩ := by
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
      Option.getD_some]
  change (PhaseRuntimeState.settle state.phases state.generation state.entry raw
    state.retired).retired = _
  rw [phases]
  by_cases missed : (((phase.drain raw).excluded \ state.entry.excluded) ∩ phase.owners).Nonempty
  · by_cases survivors : (phase.owners \ (phase.drain raw).excluded).Nonempty
    · rw [PhaseRuntimeState.settle_retry phase rest state.generation state.entry raw state.retired
        finished commitment missed survivors]
      simp only [missed, ↓reduceIte, address]
    · rw [PhaseRuntimeState.settle_exhausted phase rest state.generation state.entry raw
        state.retired finished commitment missed survivors, settle_self_retired]
      simp only [missed, ↓reduceIte, address]
  · rw [PhaseRuntimeState.settle_clean phase rest state.generation state.entry raw state.retired
      finished (fun failed => missed failed.2), settle_self_retired]
    simp only [missed, ↓reduceIte, List.append_nil]

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


/-- Already excluded owners retain their literal accepted rows. Each active
owner's original accepting word is its inherited owned prefix followed by the
accepting bit of its literal old frontier; a completed chain stays accepting.
The actual image and failed-attempt address record remain available. -/
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
        final.state = some ending ∧ ending.actor = none ∧
        ending.execution.application.attempt ≠ anchor.application.attempt ∧
        TracePrefix trace prior ∧
        TracePrefix (prior.extend joint legal realized) final.trace ∧
        before.execution.application.attempt = anchor.application.attempt ∧
        phase ∈ before.execution.application.phases.head? ∧
        ending.execution.application =
          ({ before.execution.application with current := raw } :
            PhaseRuntimeState graph).normalize ∧
        PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
        phase.Finished (phase.drain raw) ∧
        (phase.drain raw).native.BindingInvariant ∧ (phase.drain raw).FailureCoverage ∧
        (phase.drain raw).excluded = ending.execution.application.current.excluded ∧
        (phase.drain raw).native.accepted = raw.native.accepted ∧
        (phase.drain raw).native.candidates = raw.native.candidates ∧
        PhaseProposal.sourceArchive ending.execution.network.inputs =
          PhaseProposal.sourceArchive anchor.network.inputs ∧
        before.execution.application.retired = anchor.application.retired ∧
        ending.execution.application.retired = anchor.application.retired ++
          (if (((phase.drain raw).excluded \ before.execution.application.entry.excluded) ∩
              phase.owners).Nonempty then
            [⟨anchor.application.attempt, (phase.drain raw).native⟩] else []) ∧
        (∀ event candidate, anchor.application.attempt.phase ≤ event.val →
          (phase.drain raw).native.accepted (.inr event) = some candidate →
          PhaseService.BindingAccepted runtime leaks
            ⟨anchor.application.attempt, event⟩ candidate.1 ending.execution) ∧
        (∀ owner, owner ∈ anchor.application.current.excluded → ∀ event payload,
          (graph).outputLayout event = .binding owner payload →
            raw.native.accepted (.inr event) =
              anchor.application.current.native.accepted (.inr event)) ∧
        (∀ owner, owner ∉ anchor.application.current.excluded →
          (∀ event, ¬ anchor.application.SeedRequest owner ⟨anchor.application.attempt, event⟩) →
          ∀ event ∈ phase.events, ∀ payload,
            (graph).outputLayout event = .binding owner payload →
              raw.native.accepted (.inr event) ≠ none) ∧
        (∀ owner frontier payload,
          (graph).outputLayout frontier = .binding owner payload →
          anchor.application.SeedRequest owner ⟨anchor.application.attempt, frontier⟩ →
          (∀ message ∈ (app).outputs (anchor.recall owner),
            PhaseCount.event? message.payload ≠ some ⟨anchor.application.attempt, frontier⟩) ∨
          ∃ message candidate, message ∈ anchor.network.inputs ∧ message.sender = owner ∧
            message.payload.packet.call = .commitment frontier candidate ∧
            message.payload.attempt = anchor.application.attempt ∧
            (message ∈ anchor.network.pending ∨ (message.id, false) ∈ anchor.receipts)) ∧
        (∀ owner frontier,
          anchor.application.SeedRequest owner ⟨anchor.application.attempt, frontier⟩ →
          ∀ event ∈ phase.events, ∀ payload,
            (graph).outputLayout event = .binding owner payload →
            (raw.native.accepted (.inr event) ≠ none ↔
              event.val < frontier.val ∨ raw.native.accepted (.inr frontier) ≠ none)) ∧
        (∀ message ∈ anchor.network.pending, ∀ frontier candidate,
          message.payload.packet.call = .commitment frontier candidate →
          anchor.application.SeedRequest message.sender ⟨message.payload.attempt, frontier⟩ →
          ∀ entered, anchor.application.current.native.activatedAt frontier = some entered →
          ReservedEpoch.packetCapacity runtime ≤ anchor.environmentRecall.length %
            ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime) →
          (raw.native.accepted (.inr frontier) ≠ none ↔
            ∃ epoch, tape.nextProcessingEpoch (anchor.environmentRecall.length /
                ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime) +
                1) = some epoch ∧ epoch < ReservedEpoch.completionCycles runtime ∧
              epoch - entered < runtime.deadline frontier)) ∧
        (∀ message ∈ anchor.network.inputs, ∀ frontier candidate,
          message.payload.packet.call = .commitment frontier candidate →
          anchor.application.SeedRequest message.sender ⟨message.payload.attempt, frontier⟩ →
          (message.id, false) ∈ anchor.receipts → raw.native.accepted (.inr frontier) = none) ∧
        (∀ owner frontier payload,
          (graph).outputLayout frontier = .binding owner payload →
          anchor.application.SeedRequest owner ⟨anchor.application.attempt, frontier⟩ →
          ∀ entered, anchor.application.current.native.activatedAt frontier = some entered →
          (∀ message ∈ (app).outputs (anchor.recall owner),
            PhaseCount.event? message.payload ≠ some ⟨anchor.application.attempt, frontier⟩) →
          (raw.native.accepted (.inr frontier) ≠ none ↔
            ReservedEpoch.UnsentQualification runtime leaks (ReservedEpoch.packetCapacity runtime)
              (ReservedEpoch.completionCycles runtime) tape anchor.environmentRecall.length
                entered owner frontier)) ∧
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
  obtain ⟨ending, before, prior, joint, legal, realized, raw, stateEq, idle, changed,
    fromStart, toFinal, same, phaseInstalled, normalized, effect, finished, valid, coverage,
    excluded, tables, candidates, archive, receipts, failures, origins, record⟩ :=
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
  have priorRecord := EventGraphRuntime.ReservedEpoch.same_namespace_record_prefix runtime leaks
    (menu) initial (fun state supported => by
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan draw) horizon scheduler
        ⟨remaining, none, anchor⟩ before trace prior fromStart anchorOrdered same.symm
  let endingTrace : ((menu).protocol initial horizon scheduler).Trace (some ending) :=
    stateEq ▸ final.trace
  have atEnding : TracePrefix trace endingTrace := by
    cases final with
    | mk state finalTrace =>
        change state = some ending at stateEq
        subst state
        exact (TracePrefix.extend fromStart joint legal realized).trans toFinal
  have idleEnding : ending = (⟨ending.remaining, none, ending.execution⟩ : (app).Control) := by
    cases ending with
    | mk left actor execution =>
        change actor = none at idle
        subst actor
        rfl
  let idleTrace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨ending.remaining, none, ending.execution⟩) :=
    (congrArg some idleEnding) ▸ endingTrace
  have atIdle : TracePrefix trace idleTrace := by
    cases ending with
    | mk left actor execution =>
        change actor = none at idle
        subst actor
        exact atEnding
  have rounds := stopped_prefix_roundsSupported (menu) initial horizon scheduler profile remaining
    anchor trace stopped final supported final
      ((TracePrefix.extend fromStart joint legal realized).trans toFinal) .refl
  have decoded : (menu).decodeProfile initial horizon scheduler profile = players := by
    funext who
    exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler who (players who)
      ((menu).anchoredPolicy_covered initial horizon scheduler ⟨remaining, none, anchor⟩ trace
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who
          (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values who))
  rw [stateEq, decoded] at rounds
  change (match ending.actor with
    | none => ∃ used, ending.execution ∈ ((app).runRounds scheduler players used anchor).support
    | some who => _) at rounds
  rw [idle] at rounds
  obtain ⟨used, path⟩ := rounds
  rw [ReactiveApplication.runRounds_anchoredPolicy] at path
  have cleanStart := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have cleanEnd := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) endingTrace
  have rawEnd := (menu).toRawTrace initial horizon scheduler endingTrace
  have frontierReceipt (owner : Player) (frontier : (graph).EventId)
      (request : anchor.application.SeedRequest owner ⟨anchor.application.attempt, frontier⟩)
      (accepting : raw.native.accepted (.inr frontier) ≠ none) :
      PhaseService.BindingAccepted runtime leaks ⟨anchor.application.attempt, frontier⟩ owner
        ending.execution := by
    obtain ⟨actual, head, inside⟩ := request.2.1
    have equal : actual = phase := Option.some.inj
      ((Option.mem_def.mp head).symm.trans (Option.mem_def.mp installed))
    have frontierInside : frontier ∈ phase.events := equal ▸ inside
    have lower : anchor.application.attempt.phase ≤ frontier.val := by
      have head := Option.mem_def.mp installed
      simpa only [PhaseRuntimeState.attempt, head, Option.map_some, Option.getD_some] using
        ((phase.mem_events frontier).mp frontierInside).1
    obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp accepting
    have drained : (phase.drain raw).native.accepted (.inr frontier) = some candidate := by
      rwa [tables]
    obtain ⟨_payload, binding⟩ := valid.accepted_typed (.inr frontier) candidate drained
    have ownerEq : candidate.1 = owner := Option.some.inj
      (((graph).actor?_of_outputLayout_binding binding).symm.trans request.2.2.2.1)
    simpa only [ownerEq] using receipts frontier candidate lower drained
  have packetLaw (message : Message Player (CommitAttemptPacket graph))
      (endInput : message ∈ ending.execution.network.inputs) (frontier : (graph).EventId)
      (candidate : Handle graph)
      (call : message.payload.packet.call = .commitment frontier candidate)
      (request : anchor.application.SeedRequest message.sender
        ⟨message.payload.attempt, frontier⟩) :
      raw.native.accepted (.inr frontier) ≠ none ↔
        (message.id, true) ∈ ending.execution.receipts := by
    have noReceipt := EventGraphRuntime.ReservedEpoch.request_binding_identifier_not_receipted
      runtime leaks (menu) plan inputs horizon scheduler ⟨remaining, none, anchor⟩ ending trace
        endingTrace atEnding message endInput frontier candidate call request
    constructor
    · intro accepting
      have attemptEq : message.payload.attempt = anchor.application.attempt := request.1
      have requested : anchor.application.SeedRequest message.sender
          ⟨anchor.application.attempt, frontier⟩ := by simpa only [attemptEq] using request
      obtain ⟨original, originalInput, originalSender, originalAttempt, originalNamed, received⟩ :=
        frontierReceipt message.sender frontier requested accepting
      have identical : original = message := PhaseCount.Permits.eq_of_same_event
        ((PhaseCount.permits_eq_true_iff _ _).mp (cleanEnd.2 original originalInput))
        ((PhaseCount.permits_eq_true_iff _ _).mp (cleanEnd.2 message endInput))
        originalInput endInput
        (fun first firstInput second secondInput ids =>
          (app).input_identifier_injective_history initial horizon scheduler ending rawEnd
            first second firstInput secondInput ids) originalSender (by
          change (original.payload.packet.call.event? graph).map
              (fun event => (⟨original.payload.attempt, event⟩ : CommitAttemptEvent graph)) =
            (message.payload.packet.call.event? graph).map
              (fun event => (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph))
          rw [originalNamed, call]
          simp only [Payload.event?, Option.map_some, originalAttempt]
          exact congrArg some (congrArg
            (fun attempt => (⟨attempt, frontier⟩ : CommitAttemptEvent graph))
            (show message.payload.attempt = anchor.application.attempt from request.1).symm))
      simpa only [identical] using received
    · intro received
      have accepted := EventGraphRuntime.ReservedEpoch.original_binding_receipt_accepted runtime
        leaks bounds plan inputs horizon scheduler ⟨remaining, none, anchor⟩ before ending trace
          prior joint legal realized fromStart same.symm raw effect message endInput frontier
            candidate call request.1 noReceipt received
      rw [accepted]
      exact Option.some_ne_none _
  refine ⟨ending, before, prior, joint, legal, realized, raw, stateEq, idle, changed,
    fromStart, toFinal, same,
    phaseInstalled, normalized, effect, finished, valid, coverage, excluded, tables, candidates,
    archive, priorRecord.1, ?_, receipts, ?_, ?_, ?_, ?_, ?_, ?_, ?_, failures, record⟩
  · rw [normalized]
    simpa only [priorRecord.1, same] using
      EventGraphRuntime.ReservedEpoch.closing_retired_word before.execution.application phase
        phaseInstalled commitment raw finished
  · intro owner inherited event payload binding
    exact (EventGraphRuntime.ReservedEpoch.excluded_closing_accepted runtime leaks before
      ending.execution raw changedNow effect owner (priorRecord.2.1 inherited) event payload
        binding).trans
        (priorRecord.2.2 owner inherited event payload binding)
  · intro owner active noRequest event inside payload binding missing
    have survives : owner ∉ ending.execution.application.current.excluded := by
      intro failed
      obtain ⟨missed, _inside, request, _recorded, _failure⟩ := origins owner active failed
      exact noRequest missed request
    have ownerFailed := coverage.covered event owner
      ((graph).actor?_of_outputLayout_binding binding) ((failures event inside).mpr missing)
    rw [excluded] at ownerFailed
    exact survives ownerFailed
  · intro owner frontier payload binding request
    by_cases unsent : ∀ message ∈ (app).outputs (anchor.recall owner),
        PhaseCount.event? message.payload ≠ some ⟨anchor.application.attempt, frontier⟩
    · exact Or.inl unsent
    · push Not at unsent
      obtain ⟨message, member, named⟩ := unsent
      have recalled := (app).history_inputRecall initial horizon scheduler rawStart owner
      rw [← recalled] at member
      obtain ⟨input, authoredBool⟩ := List.mem_filter.mp member
      have authored : message.sender = owner := of_decide_eq_true authoredBool
      have correct := ((PhaseCount.permits_eq_true_iff _ _).mp
        (cleanStart.2 message input)).2.1
      have packet : ∃ candidate, message.payload.packet.call = .commitment frontier candidate := by
        cases call : message.payload.packet.call with
        | malformed raw =>
            simp only [PhaseCount.event?, call, Payload.event?, Option.map_none] at named
            cases named
        | commitment other candidate =>
            have coordinate : (⟨message.payload.attempt, other⟩ : CommitAttemptEvent graph) =
                ⟨anchor.application.attempt, frontier⟩ := Option.some.inj (by
              simpa only [PhaseCount.event?, call, Payload.event?, Option.map_some] using named)
            have sameEvent : other = frontier := congrArg CommitAttemptEvent.event coordinate
            subst other
            exact ⟨candidate, rfl⟩
        | opening other candidate raw =>
            have coordinate : (⟨message.payload.attempt, other⟩ : CommitAttemptEvent graph) =
                ⟨anchor.application.attempt, frontier⟩ := Option.some.inj (by
              simpa only [PhaseCount.event?, call, Payload.event?, Option.map_some] using named)
            have sameEvent : other = frontier := congrArg CommitAttemptEvent.event coordinate
            subst other
            change CountCallCorrect _ (PhaseCount.nativeMessage message) at correct
            simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
            cases node : nodeView (graph) frontier with
            | bind actor ty kind code => simp only [node, and_false] at correct
            | resolve actor ty reference checks kind code => cases kind.symm.trans binding
            | sample ty law kind code => cases kind.symm.trans binding
      obtain ⟨candidate, call⟩ := packet
      have coordinate : (⟨message.payload.attempt, frontier⟩ : CommitAttemptEvent graph) =
          ⟨anchor.application.attempt, frontier⟩ := Option.some.inj (by
        simpa only [PhaseCount.event?, call, Payload.event?, Option.map_some] using named)
      have address : message.payload.attempt = anchor.application.attempt :=
        congrArg CommitAttemptEvent.attempt coordinate
      refine Or.inr ⟨message, candidate, input, authored, call, address, ?_⟩
      have retained := (app).pendingOrPublished_history scheduler initial horizon rawStart
      rcases retained.inputs message input with pending | published
      · exact Or.inl pending
      · have identifiers := (app).receipt_identifiers_history initial horizon scheduler
          ⟨remaining, none, anchor⟩ rawStart
        have recorded : message.id ∈ anchor.receipts.map Prod.fst := by
          rw [identifiers]
          exact List.mem_map.mpr ⟨message, published, rfl⟩
        obtain ⟨receipt, receiptMember, equalId⟩ := List.mem_map.mp recorded
        have actualReceipt : (message.id, receipt.2) ∈ anchor.receipts := by
          simpa only [← equalId, Prod.mk.eta] using receiptMember
        cases accepted : receipt.2 with
        | false => exact Or.inr (by rwa [accepted] at actualReceipt)
        | true =>
            rw [accepted] at actualReceipt
            have impossible := PhaseService.not_bindingAccepted_of_request runtime leaks plan
              inputs horizon scheduler rawStart ⟨anchor.application.attempt, frontier⟩ owner request
            exact (impossible ⟨message, input, authored, address,
              by rw [call]; rfl, actualReceipt⟩).elim
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
  · intro message pending frontier candidate call request entered stamp afterProcessing
    let future := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let cycles := ReservedEpoch.completionCycles runtime
    let budget := ReservedEpoch.packetCapacity runtime
    let width := ReservedEpoch.cycleWidth («graph» := graph) budget
    let sentCycle := anchor.environmentRecall.length / width
    let slot := anchor.environmentRecall.length % width
    have cursor : anchor.environmentRecall.length = sentCycle * width + slot := by
      have divided := Nat.mod_add_div anchor.environmentRecall.length width
      rw [Nat.mul_comm width] at divided
      simpa only [sentCycle, slot, Nat.add_comm] using divided.symm
    have clock := ReservedEpoch.clock_history runtime leaks budget tape plan inputs horizon
      ⟨remaining, none, anchor⟩ rawStart
    have ownClean : PhaseCount.OwnCountClean runtime leaks message.sender anchor :=
      ⟨cleanStart.1, fun packet member _ => cleanStart.2 packet member⟩
    have covered : ∀ past view action, action ∈ (future message.sender past view).support →
        action.transmission = none ∨
          PhaseCount.OnePacketResponse runtime leaks message.sender past view action := by
      intro past view action selected
      exact ((PhaseCount.mem_onePacketActions runtime leaks bounds message.sender past view
        action).mp
        (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values
          message.sender past view action selected)).2
    have law := EventGraphRuntime.ReservedEpoch.stopped_pending_receipt_iff_epoch runtime
      leaks cycles tape future (menu) plan ordered inputs remaining ending.remaining used sentCycle
        slot anchor ending.execution trace idleTrace atIdle changed path
          (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values)
            cursor afterProcessing clock message pending frontier (.binding candidate call) request
              entered stamp ownClean covered
    have input := ((app).retained_envelopes_mem_inputs anchor
      ((app).history_provenance initial horizon scheduler rawStart)
      ((app).history_inputRecall initial horizon scheduler rawStart)).pending message pending
    have endInput := EventGraphRuntime.ReservedEpoch.input_mem_prefix runtime leaks (menu) initial
      horizon scheduler ⟨remaining, none, anchor⟩ ending trace endingTrace atEnding message input
    exact (packetLaw message endInput frontier candidate call request).trans law
  · intro message input frontier candidate call request rejected
    have endInput := EventGraphRuntime.ReservedEpoch.input_mem_prefix runtime leaks (menu) initial
      horizon scheduler ⟨remaining, none, anchor⟩ ending trace endingTrace atEnding message input
    have keptReceipts := (app).reaches_receipts_prefix initial horizon scheduler
      ((menu).reaches_raw initial horizon scheduler atEnding.reachesWithin)
        ⟨remaining, none, anchor⟩ ending rfl rfl
    have impossible := EventGraphRuntime.ReservedEpoch.rejected_binding_not_accepted runtime leaks
      bounds plan inputs horizon scheduler ending endingTrace message endInput frontier candidate
        call (keptReceipts.subset rejected)
    have attemptEq : message.payload.attempt = anchor.application.attempt := request.1
    have currentRequest : anchor.application.SeedRequest message.sender
        ⟨anchor.application.attempt, frontier⟩ := by simpa only [attemptEq] using request
    by_contra present
    have receipt := frontierReceipt message.sender frontier currentRequest present
    exact impossible (by simpa only [attemptEq] using receipt)
  · intro owner frontier payload binding request entered stamp unsent
    let cycles := ReservedEpoch.completionCycles runtime
    let budget := ReservedEpoch.packetCapacity runtime
    let width := ReservedEpoch.cycleWidth («graph» := graph) budget
    have positive : 0 < runtime.deadline frontier := by
      have slack := margin frontier (by rw [request.2.2.2.1]; rfl)
      omega
    rcases phaseProposalUnflagged_stopped_unsent_binding setup mode runtime leaks bounds plan
      complete coveredValues maximal ordered values fullValues cycles tape capacity remaining
        ending.remaining used owner anchor ending.execution trace idleTrace atIdle changed
          frontier payload binding request entered stamp unsent positive path with
      ⟨cursor, lower, upper, expired, due, quiet, _open, failed⟩ |
      ⟨elapsed, tail, activeRemaining, offered, active, response, material, value, serial, lengths,
        initialPath, activation, moved, chosen, sent, prepared, call, sameAttempt, activeStamp,
        recalled, quiet, expiryOpen, _activeTrace, input, receipt⟩
    · have noQualification := ReservedEpoch.not_unsentQualification_of_due runtime leaks budget
        cycles tape anchor.environmentRecall.length entered cursor owner frontier
          (anchor.observeEnvironment app) lower expired due quiet
      exact iff_of_false
        (fun accepting => failed (frontierReceipt owner frontier request accepting)) noQualification
    · let message : Message Player (CommitAttemptPacket graph) :=
        ⟨(owner, active.network.nextSerial owner),
          (app).packet ((app).submit active.application owner material) owner
            (active.network.known owner) material⟩
      have named : message.payload.packet.call =
          .commitment frontier (owner, .prepared serial) := by
        change (PhaseRuntimeState.emit (active.application.submit owner material) owner
          (active.network.known owner) material).packet.call = _
        rw [phase_emit_call, call]
      have address : message.payload.attempt = anchor.application.attempt := sameAttempt
      have sender : message.sender = owner := rfl
      have messageRequest : anchor.application.SeedRequest message.sender
          ⟨message.payload.attempt, frontier⟩ := by simpa only [address, sender] using request
      have accepted := packetLaw message input frontier (owner, .prepared serial) named
        messageRequest
      have counted := (app).runRounds_environmentRecall_length scheduler
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) elapsed anchor
          offered initialPath
      have activationHere : ReservedEpoch.command runtime leaks budget tape
          offered.environmentRecall.length (offered.observeEnvironment app) = .activate owner :=
        activation
      have actor : (ReservedEpoch.command runtime leaks budget tape offered.environmentRecall.length
          (offered.observeEnvironment app)).actor? app = some owner := by
        rw [activationHere]
        rfl
      have offeredAll : ∀ view, (ReservedEpoch.command runtime leaks budget tape
          offered.environmentRecall.length view).actor? app = some owner := fun view =>
        (ReservedEpoch.command_actor_view_independent runtime leaks budget tape
          offered.environmentRecall.length view (offered.observeEnvironment app)).trans actor
      have pureBit := ReservedEpoch.unsentQualification_iff_first_offer runtime leaks budget cycles
        tape anchor.environmentRecall.length entered offered.environmentRecall.length owner frontier
          (offered.observeEnvironment app) (by omega) offeredAll
            (by
              intro earlier lower upper view
              exact quiet earlier lower (by omega) view)
            (by
              intro earlier lower upper view selected
              exact expiryOpen earlier lower (by omega) view selected)
      have activeLength := congrArg List.length ((app).environmentStep_environmentRecall offered
        active (.activate owner) moved)
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
        at activeLength
      have window := ReservedEpoch.command_activation_window runtime leaks budget tape
        offered.environmentRecall.length (offered.observeEnvironment app) owner actor
      change budget ≤ offered.environmentRecall.length % width ∧
        offered.environmentRecall.length % width < budget + Fintype.card Player at window
      have notLast : offered.environmentRecall.length % width ≠
          budget + Fintype.card Player + (graph).order.eventCount + 1 := by omega
      have cycle := ReservedEpoch.cycle_succ («graph» := graph) budget
        offered.environmentRecall.length
      change (offered.environmentRecall.length + 1) / width =
        offered.environmentRecall.length / width +
          if offered.environmentRecall.length % width =
            budget + Fintype.card Player + (graph).order.eventCount + 1 then 1 else 0 at cycle
      simp only [notLast, ↓reduceIte, Nat.add_zero] at cycle
      have sameCycle : active.environmentRecall.length / width =
          offered.environmentRecall.length / width := by rw [activeLength]; exact cycle
      change ((message.id, true) ∈ ending.execution.receipts ↔
        ∃ epoch, tape.nextProcessingEpoch (active.environmentRecall.length / width + 1) =
          some epoch ∧ epoch < cycles ∧ epoch - entered < runtime.deadline frontier) at receipt
      rw [sameCycle] at receipt
      exact accepted.trans (receipt.trans pureBit.symm)
end Vegas
