/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochResponseWord
import Vegas.Game.ReservedEpochResponseFrame

/-! # Joint original attempt records after two actual current responses -/

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
/-- Two legal current responses at the same actual callback have identical
foreign accepting words on EVERY pair of stopped supported continuations of
the same reserved tape. If both focal rows survive, their complete original
failure footprints and retired control/address words agree as well. -/
theorem phaseProposalUnflagged_paired_response_word
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
        ((∀ event ∈ phase.events, ∀ payload,
          (graph).outputLayout event = .binding actor payload →
          leftRaw.native.accepted (.inr event) ≠ none ∧
            rightRaw.native.accepted (.inr event) ≠ none) →
          (phase.drain leftRaw).native.sourceFailureFootprint =
            (phase.drain rightRaw).native.sourceFailureFootprint ∧
          (phase.drain leftRaw).excluded = (phase.drain rightRaw).excluded ∧
          PhaseRuntimeState.sourceControlRecords leftEnding.execution.application.retired =
            PhaseRuntimeState.sourceControlRecords rightEnding.execution.application.retired) := by
  classical
  intro initial horizon scheduler anchor
  have responseArchive (response : (app).Action)
      (available : response ∈ (menu).actions actor
        (active.recall actor) (active.observe app actor)) :
      PhaseProposal.sourceArchive (anchor response).network.inputs =
        PhaseProposal.sourceArchive active.network.inputs := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        have offered : (⟨some material⟩ : (app).Action) ∈
            PhaseCount.onePacketActions runtime leaks bounds actor
              (active.recall actor) (active.observe app actor) := available
        obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks
          bounds plan inputs horizon scheduler remaining actor active activeTrace material offered
        obtain ⟨actualPhase, present, inside⟩ := request.2.1
        have equal : actualPhase = phase := Option.some.inj
          ((Option.mem_def.mp present).symm.trans (Option.mem_def.mp installed))
        subst actualPhase
        have ranks := (phase.mem_events coordinate.event).mp inside
        obtain ⟨owner, payload, binding⟩ :=
          commitment ▸ phase.fields coordinate.event ranks.1 ranks.2
        have sameOwner : owner = actor := Option.some.inj
          (((graph).actor?_of_outputLayout_binding binding).symm.trans request.2.2.2.1)
        subst owner
        have requested : active.application.SeedRequest actor
            ⟨active.application.attempt, coordinate.event⟩ := ⟨rfl, request.2⟩
        obtain ⟨serial, preparation, evidence, shape, _bounded, _fresh⟩ :=
          PhaseCount.onePacket_binding_shape runtime leaks bounds plan ordered inputs horizon
            scheduler remaining actor active activeTrace coordinate.event payload binding requested
              material offered
        exact PhaseProposal.commitment_response_archive runtime leaks active actor material
          coordinate.event (actor, .prepared serial) (by rw [shape])
  obtain ⟨leftTrace, leftResponsePrefix, leftLaw⟩ :=
    phaseProposalUnflagged_response_acceptance_word setup mode runtime leaks bounds plan complete
      coveredValues maximal ordered values fullValues tape activationGap processingGap gaps margin
        capacity remaining active actor leftResponse activeTrace leftAvailable phase installed
          commitment
  obtain ⟨rightTrace, rightResponsePrefix, rightLaw⟩ :=
    phaseProposalUnflagged_response_acceptance_word setup mode runtime leaks bounds plan complete
      coveredValues maximal ordered values fullValues tape activationGap processingGap gaps margin
        capacity remaining active actor rightResponse activeTrace rightAvailable phase installed
          commitment
  refine ⟨leftTrace, rightTrace, leftResponsePrefix, rightResponsePrefix, ?_⟩
  intro law leftFinal leftSupported rightFinal rightSupported
  obtain ⟨leftEnding, leftBefore, leftPrior, leftJoint, leftLegal, leftRealized, leftRaw,
    leftState, leftIdle, leftChanged, leftPrefix, leftEndPrefix, leftSame, leftInstalled,
    leftEffect, leftFinished, leftNormalized, leftCoverage, leftExcluded, leftTables,
    leftCandidates, leftArchive, leftRetired,
    leftAppend, leftWord, leftFootprint⟩ := leftLaw leftFinal leftSupported
  obtain ⟨rightEnding, rightBefore, rightPrior, rightJoint, rightLegal, rightRealized, rightRaw,
    rightState, rightIdle, rightChanged, rightPrefix, rightEndPrefix, rightSame, rightInstalled,
    rightEffect, rightFinished, rightNormalized, rightCoverage, rightExcluded,
    rightTables, rightCandidates, rightArchive, rightRetired,
    rightAppend, rightWord, rightFootprint⟩ := rightLaw rightFinal rightSupported
  have attempt (response : (app).Action) :
      (active.respond app actor response).application.attempt = active.application.attempt := by
    rcases response with ⟨transmission⟩
    cases transmission <;> rfl
  have saved (response : (app).Action) :
      (active.respond app actor response).application.entry = active.application.entry := by
    rcases response with ⟨transmission⟩
    cases transmission <;> rfl
  have retired (response : (app).Action) :
      (active.respond app actor response).application.retired = active.application.retired := by
    rcases response with ⟨transmission⟩
    cases transmission <;> rfl
  have foreignWord : ∀ event ∈ phase.events, ∀ owner payload, owner ≠ actor →
      (graph).outputLayout event = .binding owner payload →
      (leftRaw.native.accepted (.inr event) ≠ none ↔
        rightRaw.native.accepted (.inr event) ≠ none) := by
    intro event inside owner payload foreign binding
    rw [leftWord event inside owner payload binding, rightWord event inside owner payload binding]
    exact (ReservedEpoch.ownedAcceptanceWord_respond_foreign runtime leaks tape active actor owner
      foreign leftResponse event).trans
        (ReservedEpoch.ownedAcceptanceWord_respond_foreign runtime leaks tape active actor owner
          foreign rightResponse event).symm
  have archive := leftArchive.trans
    ((responseArchive leftResponse leftAvailable).trans
      ((responseArchive rightResponse rightAvailable).symm.trans rightArchive.symm))
  refine ⟨leftEnding, rightEnding, leftBefore, rightBefore, leftPrior, rightPrior, leftJoint,
    rightJoint, leftLegal, rightLegal, leftRealized, rightRealized, leftRaw,
    rightRaw, leftState, rightState, leftPrefix, rightPrefix, leftEndPrefix, rightEndPrefix,
    leftSame.trans (attempt leftResponse),
    rightSame.trans (attempt rightResponse), leftEffect, rightEffect, leftInstalled, rightInstalled,
    leftFinished, rightFinished, leftIdle, rightIdle,
    (by simpa only [attempt leftResponse] using leftChanged),
    (by simpa only [attempt rightResponse] using rightChanged),
    leftNormalized, rightNormalized,
    leftCoverage, rightCoverage, leftExcluded, rightExcluded,
    archive, leftWord, rightWord, foreignWord, ?_⟩
  intro focal
  have savedLeft : leftBefore.execution.application.entry = active.application.entry := by
    have initialized : ∀ state ∈ initial.support, state.Ordered := by
      intro state supported
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan draw
    have orderedLeft := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized ((menu).toRawTrace initial horizon scheduler leftTrace)
    exact ((phase_attempt_progress_of_prefix runtime leaks (menu) initial initialized horizon
      scheduler
      ⟨remaining, none, anchor leftResponse⟩ leftBefore leftTrace leftPrior leftPrefix
        orderedLeft).2.2 leftSame.symm).symm.trans (saved leftResponse)
  have savedRight : rightBefore.execution.application.entry = active.application.entry := by
    have initialized : ∀ state ∈ initial.support, state.Ordered := by
      intro state supported
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan draw
    have orderedRight := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized ((menu).toRawTrace initial horizon scheduler rightTrace)
    exact ((phase_attempt_progress_of_prefix runtime leaks (menu) initial initialized horizon
      scheduler
      ⟨remaining, none, anchor rightResponse⟩ rightBefore rightTrace rightPrior rightPrefix
        orderedRight).2.2 rightSame.symm).symm.trans (saved rightResponse)
  have verdict : ∀ event : (graph).EventId,
      (phase.drain leftRaw).native.PublicFailure event ↔
        (phase.drain rightRaw).native.PublicFailure event := by
    intro event
    rw [ReservedEpoch.original_binding_publicFailure_iff runtime leaks ordered plan inputs horizon
      scheduler leftBefore ((menu).toRawTrace initial horizon scheduler leftPrior)
      leftEnding.execution leftRaw (by simpa only [leftSame] using leftChanged)
      leftEffect phase leftInstalled commitment leftFinished event,
      ReservedEpoch.original_binding_publicFailure_iff runtime leaks ordered plan inputs horizon
      scheduler rightBefore ((menu).toRawTrace initial horizon scheduler rightPrior)
      rightEnding.execution rightRaw (by simpa only [rightSame] using rightChanged)
      rightEffect phase rightInstalled commitment rightFinished event]
    rw [savedLeft, savedRight]
    by_cases old : event.val < phase.low
    · simp only [old, ↓reduceIte]
    · by_cases current : event.val < phase.high
      · simp only [old, current, ↓reduceIte]
        have inside := (phase.mem_events event).mpr ⟨by omega, current⟩
        obtain ⟨owner, payload, binding⟩ := commitment ▸ phase.fields event (by omega) current
        by_cases equal : owner = actor
        · subst owner
          obtain ⟨leftAccepted, rightAccepted⟩ := focal event inside payload binding
          simp only [leftAccepted, rightAccepted]
        · simpa only [not_not] using
            not_congr (foreignWord event inside owner payload equal binding)
      · simp only [old, current, ↓reduceIte]
  have footprint : (phase.drain leftRaw).native.sourceFailureFootprint =
      (phase.drain rightRaw).native.sourceFailureFootprint := by
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
  have leftRecord := ReservedEpoch.closing_receipt_record runtime leaks ordered plan inputs horizon
    scheduler leftBefore ((menu).toRawTrace initial horizon scheduler leftPrior)
      leftEnding.execution
      leftRaw (by simpa only [leftSame] using leftChanged) leftEffect
  have rightRecord := ReservedEpoch.closing_receipt_record runtime leaks ordered plan inputs horizon
    scheduler rightBefore ((menu).toRawTrace initial horizon scheduler rightPrior)
      rightEnding.execution
      rightRaw (by simpa only [rightSame] using rightChanged) rightEffect
  have leftExcluded :=
    ((leftRecord.exclusion.installed phase leftInstalled).phase_drain phase).excluded
  have rightExcluded :=
    ((rightRecord.exclusion.installed phase rightInstalled).phase_drain phase).excluded
  have exclusions : (phase.drain leftRaw).excluded = (phase.drain rightRaw).excluded := by
    ext owner
    rw [leftExcluded owner, rightExcluded owner, savedLeft, savedRight]
    exact or_congr Iff.rfl (exists_congr fun event => and_congr_right fun _ =>
      and_congr_right fun _ => verdict event)
  refine ⟨footprint, exclusions, ?_⟩
  rw [leftAppend, rightAppend]
  simp only [saved, retired, attempt, exclusions, PhaseRuntimeState.sourceControlRecords,
    List.map_append]
  split_ifs <;> simp only [List.map_cons, List.map_nil, footprint]

end Vegas
