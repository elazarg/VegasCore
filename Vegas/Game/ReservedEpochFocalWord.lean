/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ReservedEpochBindingAliases

/-! # Earlier current binding responses preserve focal qualification -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem processing_epoch_of_unsent {length : Nat} (tape : Tape Player length)
    (start entered : Nat) (owner : Player) (event : graph.EventId)
    (qualified : UnsentQualification runtime leaks (packetCapacity runtime)
      (completionCycles runtime) tape start entered owner event) :
    ∃ epoch, tape.nextProcessingEpoch
        (start / cycleWidth (graph := graph) (packetCapacity runtime) + 1) = some epoch ∧
      epoch < completionCycles runtime ∧ epoch - entered < runtime.deadline event := by
  obtain ⟨cursor, later, lower, _offered, _first, _expiry, selected, bounded, timely⟩ := qualified
  have laterSpec := tape.nextProcessingEpoch_spec
    (cursor / cycleWidth (graph := graph) (packetCapacity runtime) + 1) later selected
  have starts : start / cycleWidth (graph := graph) (packetCapacity runtime) + 1 ≤
      cursor / cycleWidth (graph := graph) (packetCapacity runtime) + 1 :=
    Nat.add_le_add_right (Nat.div_le_div_right lower) 1
  have available : ∃ epoch,
      start / cycleWidth (graph := graph) (packetCapacity runtime) + 1 ≤ epoch ∧
        tape.processes epoch = true :=
    ⟨later, starts.trans laterSpec.1, laterSpec.2.1⟩
  have early : tape.nextProcessingEpoch
      (start / cycleWidth (graph := graph) (packetCapacity runtime) + 1) =
        some (Nat.find available) := by
    simp only [Tape.nextProcessingEpoch, available, ↓reduceDIte]
  have noLater := tape.nextProcessingEpoch_mono _ _ _ _ starts early selected
  exact ⟨Nat.find available, early, noLater.trans_lt bounded,
    (Nat.sub_le_sub_right noLater entered).trans_lt timely⟩

private theorem frontierQualification_wait_imp_binding {length : Nat}
    (tape : Tape Player length) (execution : (app).Execution) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (material : WitnessedSubmission graph)
    (call : material.call.packet = .commitment event candidate)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩) :
    frontierQualification runtime leaks tape (execution.respond app owner ⟨none⟩) owner event →
      frontierQualification runtime leaks tape (execution.respond app owner ⟨some material⟩)
        owner event := by
  classical
  let silent := execution.respond app owner ⟨none⟩
  let sent := execution.respond app owner ⟨some material⟩
  let message : Message Player (app).Payload :=
    ⟨(owner, execution.network.nextSerial owner),
      (app).packet ((app).submit execution.application owner material) owner
        (execution.network.known owner) material⟩
  have silentOutputs : (app).outputs (silent.recall owner) =
      (app).outputs (execution.recall owner) := by
    simp only [silent, ReactiveApplication.Execution.respond, ↓reduceIte,
      ReactiveApplication.outputs, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.append_nil]
  have silentUnsent : ∀ packet ∈ (app).outputs (silent.recall owner),
      PhaseCount.event? packet.payload ≠ some ⟨silent.application.attempt, event⟩ := by
    have attempt : silent.application.attempt = execution.application.attempt := rfl
    simpa only [silentOutputs, attempt] using unsent
  have pending : message ∈ sent.network.pending := by
    change message ∈ execution.network.pending ++ [message]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have emitted : message ∈ (app).outputs (sent.recall owner) := by
    simp [sent, ReactiveApplication.Execution.respond, MessageNetwork.submit,
      ReactiveApplication.outputs, message]
  have named : message.payload.packet.call = .commitment event candidate := by
    change (PhaseRuntimeState.emit (execution.application.submit owner material) owner
      (execution.network.known owner) material).packet.call = _
    rw [phase_emit_call, call]
  have addressed : message.payload.attempt = sent.application.attempt := rfl
  have sentUnsent : ¬ ∀ packet ∈ (app).outputs (sent.recall owner),
      PhaseCount.event? packet.payload ≠ some ⟨sent.application.attempt, event⟩ := by
    intro absent
    apply absent message emitted
    simp only [PhaseCount.event?, named, Payload.event?, Option.map_some, addressed]
  intro qualified
  change frontierQualification runtime leaks tape silent owner event at qualified
  change frontierQualification runtime leaks tape sent owner event
  unfold frontierQualification at qualified ⊢
  dsimp only at qualified ⊢
  obtain ⟨entered, stamp, later⟩ := qualified
  rw [ite_eq_left silentUnsent] at later
  have cursor : silent.environmentRecall.length = execution.environmentRecall.length :=
    congrArg List.length ((app).respond_environmentRecall execution owner ⟨none⟩)
  rw [cursor] at later
  obtain ⟨epoch, selected, bounded, timely⟩ :=
    processing_epoch_of_unsent runtime leaks tape _ entered owner event later
  have activated : sent.application.current.native.activatedAt =
      execution.application.current.native.activatedAt :=
    congrArg (fun view : PhasePublicView graph => view.native.activatedAt)
      (PhaseCount.submit_publicView execution.application owner material)
  refine ⟨entered, (congrFun activated event).trans stamp, ?_⟩
  rw [ite_eq_right sentUnsent]
  refine ⟨message, pending, candidate, rfl, named, addressed, epoch, ?_, bounded, timely⟩
  simpa only [sent, (app).respond_environmentRecall] using selected

private theorem ownedAcceptanceWord_wait_imp_binding {length : Nat}
    (tape : Tape Player length) (ordered : graph.RevealRelaxedOrdered)
    (execution : (app).Execution) (owner : Player) (frontier : graph.EventId)
    (candidate : Handle graph) (material : WitnessedSubmission graph)
    (call : material.call.packet = .commitment frontier candidate)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, frontier⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, frontier⟩)
    (event : graph.EventId) :
    ownedAcceptanceWord runtime leaks tape (execution.respond app owner ⟨none⟩) owner event →
      ownedAcceptanceWord runtime leaks tape (execution.respond app owner ⟨some material⟩)
        owner event := by
  classical
  have sentRequest := respond_request runtime leaks execution owner ⟨some material⟩ owner
    ⟨execution.application.attempt, frontier⟩ request
  have silentRequest := respond_request runtime leaks execution owner ⟨none⟩ owner
    ⟨execution.application.attempt, frontier⟩ request
  have sentActive : owner ∉
      (execution.respond app owner ⟨some material⟩).application.current.excluded :=
    request.2.2.2.2
  have silentActive : owner ∉ (execution.respond app owner ⟨none⟩).application.current.excluded :=
    request.2.2.2.2
  simp only [ownedAcceptanceWord, silentActive, sentActive, ↓reduceIte]
  intro survived other requested
  have same : other = frontier := ordered.ready_actor_unique _ sentRequest.2.2.1
    requested.2.2.1 sentRequest.2.2.2.1 requested.2.2.2.1
  subst other
  rcases survived frontier silentRequest with earlier | qualified
  · exact Or.inl earlier
  · exact Or.inr (frontierQualification_wait_imp_binding runtime leaks tape execution owner
      frontier candidate material call unsent qualified)

/-- At an actual binding callback, any available nonsilent counted response
weakly improves the entire focal accepting word over WAIT. The actual request,
unsent status and fresh binding packet shape are derived from the counted trace.
No future offer, horizon slack or qualification is supplied as a premise. -/
theorem ownedAcceptanceWord_wait_imp_available_binding
    {length : Nat} (tape : Tape Player length)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (material : WitnessedSubmission graph)
    (available : (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
        (execution.observe app owner))
    (phase : RuntimePhase graph) (installed : phase ∈ execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (event : graph.EventId) :
    ownedAcceptanceWord runtime leaks tape (execution.respond app owner ⟨none⟩) owner event →
      ownedAcceptanceWord runtime leaks tape (execution.respond app owner ⟨some material⟩)
        owner event := by
  classical
  obtain ⟨coordinate, requested⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks
    bounds plan inputs horizon scheduler remaining owner execution trace material available
  obtain ⟨currentPhase, present, inside⟩ := requested.2.1
  have equal : currentPhase = phase := Option.some.inj
    ((Option.mem_def.mp present).symm.trans (Option.mem_def.mp installed))
  subst currentPhase
  have ranks := (phase.mem_events coordinate.event).mp inside
  obtain ⟨actor, payload, binding⟩ :=
    commitment ▸ phase.fields coordinate.event ranks.1 ranks.2
  have sameOwner : actor = owner := Option.some.inj
    (((graph).actor?_of_outputLayout_binding binding).symm.trans requested.2.2.2.1)
  subst actor
  have request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, coordinate.event⟩ := ⟨rfl, requested.2⟩
  have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan ordered inputs horizon
    scheduler remaining owner execution trace ⟨execution.application.attempt, coordinate.event⟩
      request material available
  obtain ⟨serial, _preparation, _evidence, shape, _bounded, _fresh⟩ :=
    PhaseCount.onePacket_binding_shape runtime leaks bounds plan ordered inputs horizon scheduler
      remaining owner execution trace coordinate.event payload binding request material available
  exact ownedAcceptanceWord_wait_imp_binding runtime leaks tape ordered execution owner
    coordinate.event (owner, .prepared serial) material (by rw [shape]) request unsent event

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


open scoped Classical in
/-- At the same actual current binding callback, an available SEND preserves
every focal row that any current response preserves, on every pair of actual stopped
supported futures of the same tape. On that branch the complete original
failure footprint and retired control/address word coincide. -/
theorem phaseProposalUnflagged_available_send_stopped_word
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
    (remaining : Nat) (active : (app).Execution) (actor : Player)
    (leftResponse rightResponse : (app).Action)
    (activeTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨remaining, some actor, active⟩))
    (leftAvailable : leftResponse ∈ (menu).actions actor
      (active.recall actor) (active.observe app actor))
    (rightAvailable : rightResponse ∈ (menu).actions actor
      (active.recall actor) (active.observe app actor))
    (leftSends : leftResponse.transmission ≠ none)
    (phase : RuntimePhase graph) (installed : phase ∈ active.application.phases.head?)
    (commitment : phase.kind = .commitment) :
    let initial := (inputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let anchor := fun response : (app).Action => active.respond app actor response
    ∃ leftTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, anchor leftResponse⟩),
    ∃ rightTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, anchor rightResponse⟩),
    TracePrefix activeTrace leftTrace ∧ TracePrefix activeTrace rightTrace ∧
    let law := fun response (trace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, anchor response⟩)) =>
      let players := ReactiveApplication.anchoredPolicy (anchor response)
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
      let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
      let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
        match history.state with
        | none => False
        | some control =>
            control.execution.application.attempt ≠ (anchor response).application.attempt
      ((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, anchor response⟩, trace⟩
    ∀ leftFinal ∈ (law leftResponse leftTrace).support,
    ∀ rightFinal ∈ (law rightResponse rightTrace).support,
      ∃ (leftEnding rightEnding leftBefore rightBefore : (app).Control)
        (leftPrior : ((menu).protocol initial horizon scheduler).Trace (some leftBefore))
        (rightPrior : ((menu).protocol initial horizon scheduler).Trace (some rightBefore))
        (leftJoint rightJoint : Player → Option (app).Action)
        (leftLegal : ((menu).protocol initial horizon scheduler).Legal (some leftBefore) leftJoint)
        (rightLegal : ((menu).protocol initial horizon scheduler).Legal
          (some rightBefore) rightJoint)
        (leftRealized : some leftEnding ∈ ((app).transition initial horizon scheduler
          (some leftBefore) leftJoint).support)
        (rightRealized : some rightEnding ∈ ((app).transition initial horizon scheduler
          (some rightBefore) rightJoint).support)
        (leftRaw rightRaw : RecoveryState graph),
        leftFinal.state = some leftEnding ∧ rightFinal.state = some rightEnding ∧
        TracePrefix leftTrace leftPrior ∧ TracePrefix rightTrace rightPrior ∧
        TracePrefix (leftPrior.extend leftJoint leftLegal leftRealized) leftFinal.trace ∧
        TracePrefix (rightPrior.extend rightJoint rightLegal rightRealized) rightFinal.trace ∧
        leftBefore.execution.application.attempt = active.application.attempt ∧
        rightBefore.execution.application.attempt = active.application.attempt ∧
        PhaseClosingEffect runtime leaks leftBefore.execution leftEnding.execution leftRaw ∧
        PhaseClosingEffect runtime leaks rightBefore.execution rightEnding.execution rightRaw ∧
        phase ∈ leftBefore.execution.application.phases.head? ∧
        phase ∈ rightBefore.execution.application.phases.head? ∧
        phase.Finished (phase.drain leftRaw) ∧ phase.Finished (phase.drain rightRaw) ∧
        leftEnding.actor = none ∧ rightEnding.actor = none ∧
        leftEnding.execution.application.attempt ≠ active.application.attempt ∧
        rightEnding.execution.application.attempt ≠ active.application.attempt ∧
        leftEnding.execution.application =
          ({ leftBefore.execution.application with current := leftRaw } :
            PhaseRuntimeState graph).normalize ∧
        rightEnding.execution.application =
          ({ rightBefore.execution.application with current := rightRaw } :
            PhaseRuntimeState graph).normalize ∧
        (phase.drain leftRaw).FailureCoverage ∧
        (phase.drain rightRaw).FailureCoverage ∧
        (phase.drain leftRaw).excluded = leftEnding.execution.application.current.excluded ∧
        (phase.drain rightRaw).excluded = rightEnding.execution.application.current.excluded ∧
        PhaseProposal.sourceArchive leftEnding.execution.network.inputs =
          PhaseProposal.sourceArchive rightEnding.execution.network.inputs ∧
        (∀ event ∈ phase.events, ∀ owner payload,
          (graph).outputLayout event = .binding owner payload →
          (leftRaw.native.accepted (.inr event) ≠ none ↔
            ReservedEpoch.ownedAcceptanceWord runtime leaks tape
              (anchor leftResponse) owner event)) ∧
        (∀ event ∈ phase.events, ∀ owner payload,
          (graph).outputLayout event = .binding owner payload →
          (rightRaw.native.accepted (.inr event) ≠ none ↔
            ReservedEpoch.ownedAcceptanceWord runtime leaks tape
              (anchor rightResponse) owner event)) ∧
        (∀ event ∈ phase.events, ∀ owner payload, owner ≠ actor →
          (graph).outputLayout event = .binding owner payload →
          (leftRaw.native.accepted (.inr event) ≠ none ↔
            rightRaw.native.accepted (.inr event) ≠ none)) ∧
        (actor ∉ rightEnding.execution.application.current.excluded →
          actor ∉ leftEnding.execution.application.current.excluded ∧
          (∀ event ∈ phase.events, ∀ payload,
            (graph).outputLayout event = .binding actor payload →
            rightRaw.native.accepted (.inr event) ≠ none) ∧
          (∀ event ∈ phase.events, ∀ payload,
            (graph).outputLayout event = .binding actor payload →
            leftRaw.native.accepted (.inr event) ≠ none) ∧
          (phase.drain leftRaw).native.sourceFailureFootprint =
            (phase.drain rightRaw).native.sourceFailureFootprint ∧
          (phase.drain leftRaw).excluded = (phase.drain rightRaw).excluded ∧
          PhaseRuntimeState.sourceControlRecords leftEnding.execution.application.retired =
            PhaseRuntimeState.sourceControlRecords rightEnding.execution.application.retired) := by
  classical
  intro initial horizon scheduler anchor
  obtain ⟨leftTrace, rightTrace, leftResponsePrefix, rightResponsePrefix, paired⟩ :=
    phaseProposalUnflagged_paired_response_word setup mode runtime leaks bounds plan complete
      coveredValues maximal ordered values fullValues tape activationGap processingGap gaps
        margin capacity remaining active actor leftResponse rightResponse activeTrace
          leftAvailable rightAvailable phase installed commitment
  refine ⟨leftTrace, rightTrace, leftResponsePrefix, rightResponsePrefix, ?_⟩
  intro law leftFinal leftSupported rightFinal rightSupported
  obtain ⟨leftEnding, rightEnding, leftBefore, rightBefore, leftPrior, rightPrior, leftJoint,
    rightJoint, leftLegal, rightLegal, leftRealized, rightRealized, leftRaw, rightRaw,
    leftState, rightState, leftPrefix, rightPrefix, leftEndPrefix, rightEndPrefix,
    leftAttempt, rightAttempt, leftEffect, rightEffect, leftInstalled, rightInstalled,
    leftFinished, rightFinished, leftIdle, rightIdle, leftChanged, rightChanged,
    leftNormalized, rightNormalized, leftCoverage, rightCoverage, leftExcluded,
    rightExcluded, archive, leftWord, rightWord, foreignWord, sameRecord⟩ :=
      paired leftFinal leftSupported rightFinal rightSupported
  refine ⟨leftEnding, rightEnding, leftBefore, rightBefore, leftPrior, rightPrior, leftJoint,
    rightJoint, leftLegal, rightLegal, leftRealized, rightRealized, leftRaw, rightRaw,
    leftState, rightState, leftPrefix, rightPrefix, leftEndPrefix, rightEndPrefix,
    leftAttempt, rightAttempt, leftEffect, rightEffect, leftInstalled, rightInstalled,
    leftFinished, rightFinished, leftIdle, rightIdle, leftChanged, rightChanged,
    leftNormalized, rightNormalized, leftCoverage, rightCoverage, leftExcluded,
    rightExcluded, archive, leftWord, rightWord, foreignWord, ?_⟩
  intro rightSurvives
  have rightImageSurvives : actor ∉ (phase.drain rightRaw).excluded := by
    rw [rightExcluded]
    exact rightSurvives
  have rightAccepted : ∀ event ∈ phase.events, ∀ payload,
      (graph).outputLayout event = .binding actor payload →
        rightRaw.native.accepted (.inr event) ≠ none := by
    intro event inside payload binding omitted
    apply rightImageSurvives
    apply rightCoverage.covered event actor
      ((graph).actor?_of_outputLayout_binding binding)
    apply ((phase.drain rightRaw).native.publicFailure_iff_accepted_none
      event actor payload binding (rightFinished inside)).mpr
    rw [(phase.drain_tables rightRaw).1]
    exact omitted
  obtain ⟨material, sent⟩ : ∃ material : WitnessedSubmission graph,
      leftResponse = ⟨some material⟩ := by
    rcases leftResponse with ⟨transmission⟩
    cases transmission with
    | none => exact (leftSends rfl).elim
    | some material => exact ⟨material, rfl⟩
  have sendAvailable : (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds actor (active.recall actor)
        (active.observe app actor) := by
    have actual : leftResponse ∈ PhaseCount.onePacketActions runtime leaks bounds actor
        (active.recall actor) (active.observe app actor) := leftAvailable
    simpa only [sent] using actual
  have focalWord (event : (graph).EventId) :
      ReservedEpoch.ownedAcceptanceWord runtime leaks tape (anchor rightResponse) actor event →
        ReservedEpoch.ownedAcceptanceWord runtime leaks tape (anchor leftResponse) actor event := by
    dsimp only [anchor]
    rw [sent]
    cases rightResponse with
    | mk transmission =>
        cases transmission with
        | none =>
            exact ReservedEpoch.ownedAcceptanceWord_wait_imp_available_binding runtime leaks tape
              bounds plan ordered inputs horizon scheduler remaining actor active activeTrace
                material sendAvailable phase installed commitment event
        | some other =>
            exact (ReservedEpoch.ownedAcceptanceWord_available_bindings_eq runtime leaks tape
              bounds plan ordered inputs horizon scheduler remaining actor active activeTrace
                material other sendAvailable rightAvailable phase installed commitment event).mpr
  have leftSurvives : ∀ event ∈ phase.events, ∀ payload,
      (graph).outputLayout event = .binding actor payload →
        leftRaw.native.accepted (.inr event) ≠ none := by
    intro event inside payload binding
    apply (leftWord event inside actor payload binding).mpr
    exact focalWord event ((rightWord event inside actor payload binding).mp
      (rightAccepted event inside payload binding))
  have record := sameRecord (fun event inside payload binding =>
    ⟨leftSurvives event inside payload binding, rightAccepted event inside payload binding⟩)
  refine ⟨?_, rightAccepted, leftSurvives, record⟩
  intro excluded
  apply rightImageSurvives
  rw [← record.2.1, leftExcluded]
  exact excluded

end Vegas
