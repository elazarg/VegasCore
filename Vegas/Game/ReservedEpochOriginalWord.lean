/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochStoppedFootprint

/-! # The original accepting word as a function of the anchor and service tape -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The literal initial frontier either remains unsent until its first eligible
owner offer, or already has a queued packet. Its qualification is determined
by the original entered stamp and the finite reserved processing epochs. -/
def frontierQualification (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    {length : Nat} (tape : Tape Player length) (anchor : (phaseApplication runtime leaks).Execution)
    (owner : Player) (frontier : graph.EventId) : Prop := by
  classical
  let unsent := ∀ message ∈ (phaseApplication runtime leaks).outputs (anchor.recall owner),
    PhaseCount.event? message.payload ≠ some ⟨anchor.application.attempt, frontier⟩
  exact ∃ entered, anchor.application.current.native.activatedAt frontier = some entered ∧
    if unsent then
      UnsentQualification runtime leaks (packetCapacity runtime) (completionCycles runtime) tape
        anchor.environmentRecall.length entered owner frontier
    else ∃ message ∈ anchor.network.pending, ∃ candidate,
      message.sender = owner ∧ message.payload.packet.call = .commitment frontier candidate ∧
      message.payload.attempt = anchor.application.attempt ∧
      ∃ epoch, tape.nextProcessingEpoch (anchor.environmentRecall.length /
          cycleWidth (graph := graph) (packetCapacity runtime) + 1) = some epoch ∧
        epoch < completionCycles runtime ∧ epoch - entered < runtime.deadline frontier

/-- Inherited exclusion preserves the old accepting row. Otherwise the old
owned prefix survives, and the literal frontier bit controls the whole suffix;
an owner with no remaining request has a completely accepted chain. -/
def ownedAcceptanceWord (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    {length : Nat} (tape : Tape Player length) (anchor : (phaseApplication runtime leaks).Execution)
    (owner : Player) (event : graph.EventId) : Prop := by
  classical
  exact if owner ∈ anchor.application.current.excluded then
    anchor.application.current.native.accepted (.inr event) ≠ none
  else ∀ frontier,
    anchor.application.SeedRequest owner ⟨anchor.application.attempt, frontier⟩ →
      event.val < frontier.val ∨ frontierQualification runtime leaks tape anchor owner frontier

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
/-- The actual stopped original image realizes the entire anchor/tape
acceptance word. Old UNSENT, queued and rejected frontiers are classified by
the actual counted trace; no corresponding endpoint or bit is supplied. -/
theorem phaseProposalUnflagged_stopped_acceptance_word
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
    (commitment : phase.kind = .commitment)
    (afterProcessing : ReservedEpoch.packetCapacity runtime ≤ anchor.environmentRecall.length %
      ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime)) :
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
  intro initial horizon scheduler players profile stopped final supported
  obtain ⟨ending, before, prior, joint, legal, realized, raw, stateEq, idle, changed,
    fromStart, toFinal, same, phaseInstalled, normalized, effect, finished, valid, coverage,
    excluded, tables, candidates, archive, retiredBefore, retiredAfter, receipts, inherited,
    completed, classified, suffix, pending, rejected, unsentBit, failures, record⟩ :=
    phaseProposalUnflagged_stopped_owned_word setup mode runtime leaks bounds plan complete
      coveredValues maximal ordered values fullValues tape activationGap processingGap gaps margin
        capacity remaining anchor trace phase installed commitment final supported
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized ((menu).toRawTrace initial horizon scheduler trace)
  have saved : before.execution.application.entry = anchor.application.entry :=
    ((phase_attempt_progress_of_prefix runtime leaks (menu) initial initialized horizon scheduler
      ⟨remaining, none, anchor⟩ before trace prior fromStart anchorOrdered).2.2 same.symm).symm
  have retiredActual := retiredAfter
  rw [saved] at retiredActual
  have frontierLaw (owner : Player) (frontier : (graph).EventId) (payload : L.Ty)
      (binding : (graph).outputLayout frontier = .binding owner payload)
      (request : anchor.application.SeedRequest owner ⟨anchor.application.attempt, frontier⟩) :
      raw.native.accepted (.inr frontier) ≠ none ↔
        ReservedEpoch.frontierQualification runtime leaks tape anchor owner frontier := by
    let unsent := ∀ message ∈ (app).outputs (anchor.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨anchor.application.attempt, frontier⟩
    obtain ⟨_draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
      scheduler ((menu).toRawTrace initial horizon scheduler trace)
    obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
      ((native.active.activated_iff frontier).mpr
        ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
    change anchor.application.current.native.activatedAt frontier = some entered at stamp
    unfold ReservedEpoch.frontierQualification
    change raw.native.accepted (.inr frontier) ≠ none ↔
      ∃ time, anchor.application.current.native.activatedAt frontier = some time ∧
        if unsent then _ else _
    by_cases quiet : unsent
    · simp only [quiet, ↓reduceIte]
      constructor
      · intro accepted
        exact ⟨entered, stamp,
          (unsentBit owner frontier payload binding request entered stamp quiet).mp accepted⟩
      · rintro ⟨time, found, qualifies⟩
        have equal : entered = time := Option.some.inj (stamp.symm.trans found)
        subst time
        exact (unsentBit owner frontier payload binding request entered stamp quiet).mpr qualifies
    · simp only [quiet, ↓reduceIte]
      constructor
      · intro accepted
        obtain priorQuiet | ⟨message, candidate, input, sender, call, attempt, status⟩ :=
          classified owner frontier payload binding request
        · exact (quiet priorQuiet).elim
        · have actualRequest : anchor.application.SeedRequest message.sender
              ⟨message.payload.attempt, frontier⟩ := by simpa only [sender, attempt] using request
          rcases status with queued | failed
          · exact ⟨entered, stamp, message, queued, candidate, sender, call, attempt,
              (pending message queued frontier candidate call actualRequest entered stamp
                afterProcessing).mp accepted⟩
          · exact (accepted
              (rejected message input frontier candidate call actualRequest failed)).elim
      · rintro ⟨time, found, message, queued, candidate, sender, call, attempt, qualifies⟩
        have actualRequest : anchor.application.SeedRequest message.sender
            ⟨message.payload.attempt, frontier⟩ := by simpa only [sender, attempt] using request
        exact (pending message queued frontier candidate call actualRequest time found
          afterProcessing).mpr qualifies
  have wordLaw : ∀ event ∈ phase.events, ∀ owner payload,
      (graph).outputLayout event = .binding owner payload →
      (raw.native.accepted (.inr event) ≠ none ↔
        ReservedEpoch.ownedAcceptanceWord runtime leaks tape anchor owner event) := by
    intro event member owner payload binding
    unfold ReservedEpoch.ownedAcceptanceWord
    by_cases blocked : owner ∈ anchor.application.current.excluded
    · simp only [blocked, ↓reduceIte]
      rw [inherited owner blocked event payload binding]
    · simp only [blocked, ↓reduceIte]
      constructor
      · intro accepted frontier request
        obtain ⟨actual, present, inside⟩ := request.2.1
        have equal : actual = phase := Option.some.inj
          ((Option.mem_def.mp present).symm.trans (Option.mem_def.mp installed))
        subst actual
        have ranks := (phase.mem_events frontier).mp inside
        obtain ⟨frontierOwner, frontierPayload, frontierBinding⟩ :=
          commitment ▸ phase.fields frontier ranks.1 ranks.2
        have sameOwner : frontierOwner = owner := by
          have actor := (graph).actor?_of_outputLayout_binding frontierBinding
          exact Option.some.inj (actor.symm.trans request.2.2.2.1)
        subst frontierOwner
        rcases (suffix owner frontier request event member payload binding).mp accepted with
          earlier | acceptedFrontier
        · exact Or.inl earlier
        · exact Or.inr ((frontierLaw owner frontier frontierPayload frontierBinding request).mp
            acceptedFrontier)
      · intro allFrontiers
        by_cases remainingRequest : ∃ frontier,
            anchor.application.SeedRequest owner ⟨anchor.application.attempt, frontier⟩
        · obtain ⟨frontier, request⟩ := remainingRequest
          obtain ⟨actual, present, inside⟩ := request.2.1
          have equal : actual = phase := Option.some.inj
            ((Option.mem_def.mp present).symm.trans (Option.mem_def.mp installed))
          subst actual
          obtain ⟨frontierOwner, frontierPayload, frontierBinding⟩ :=
            commitment ▸ phase.fields frontier ((phase.mem_events frontier).mp inside).1
              ((phase.mem_events frontier).mp inside).2
          have sameOwner : frontierOwner = owner := by
            have actor := (graph).actor?_of_outputLayout_binding frontierBinding
            exact Option.some.inj (actor.symm.trans request.2.2.2.1)
          subst frontierOwner
          apply (suffix owner frontier request event member payload binding).mpr
          rcases allFrontiers frontier request with earlier | qualifies
          · exact Or.inl earlier
          · exact Or.inr ((frontierLaw owner frontier frontierPayload frontierBinding request).mpr
              qualifies)
        · exact completed owner blocked (fun frontier request =>
            remainingRequest ⟨frontier, request⟩) event member payload binding
  refine ⟨ending, before, prior, joint, legal, realized, raw, stateEq, idle, changed, fromStart,
    toFinal, same, phaseInstalled, effect, finished, tables, candidates, archive, retiredBefore,
    retiredActual, wordLaw, ?_⟩
  intro failed
  have verdict (event : (graph).EventId) :
      (phase.drain raw).native.PublicFailure event ↔ failed event := by
    rw [ReservedEpoch.original_binding_publicFailure_iff runtime leaks ordered plan inputs horizon
      scheduler before ((menu).toRawTrace initial horizon scheduler prior) ending.execution raw
      (by simpa only [same] using changed) effect phase phaseInstalled commitment finished event]
    rw [saved]
    change (if _ then _ else if _ then _ else False) ↔ failed event
    dsimp only [failed]
    by_cases old : event.val < phase.low
    · simp only [old, ↓reduceIte]
    · by_cases current : event.val < phase.high
      · simp only [old, current, ↓reduceIte]
        have member := (phase.mem_events event).mpr ⟨by omega, current⟩
        obtain ⟨owner, payload, binding⟩ := commitment ▸ phase.fields event (by omega) current
        rw [(graph).actor?_of_outputLayout_binding binding]
        simp only [Option.some.injEq]
        have absent : raw.native.accepted (.inr event) = none ↔
            ¬ ReservedEpoch.ownedAcceptanceWord runtime leaks tape anchor owner event := by
          simpa only [not_not] using not_congr (wordLaw event member owner payload binding)
        constructor
        · intro missing
          exact ⟨owner, rfl, absent.mp missing⟩
        · rintro ⟨other, owned, missing⟩
          subst other
          exact absent.mpr missing
      · simp only [old, current, ↓reduceIte]
  apply Prod.ext
  · funext rank
    ext owner
    simp only [State.sourceFailureFootprint, State.failureOwnersBefore, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact exists_congr fun event => and_congr_right fun _ =>
      and_congr_right fun _ => verdict event
  · ext owner
    simp only [State.sourceFailureFootprint, State.failureOwners, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact exists_congr fun event => and_congr_right fun _ => verdict event

end Vegas
