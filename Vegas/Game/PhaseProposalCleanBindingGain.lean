/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalQualifiedBinding
import Vegas.Game.PhaseCommitmentProposalArchive
import Vegas.Game.PhaseProposalAttemptArchive
import Vegas.Game.PhaseProposalCoupledQuery
import Vegas.EventGraph.ReadySemanticStability
import Vegas.EventGraph.PrivateInputs
import Vegas.Pending.PhaseSemanticProgress

/-! # Clean binding comparisons at the original native information

The native continuation uses the original scheduler and ordinary value table.
An owner waiting at a retained ready binding reads the same normalized source
query when offered that binding again. Foreign receipt opportunities are read
from the actual reserved-service word, independently of the inserted value.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
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
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan) inputs

private theorem binding_waiting_semantics
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before after : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior trace)
    (same : before.execution.application.attempt = after.execution.application.attempt)
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (readyBefore : before.execution.application.current.native.config.cut.Ready event)
    (readyAfter : after.execution.application.current.native.config.cut.Ready event) :
    (graph).playerStore who after.execution.application.current.native.config.store =
        (graph).playerStore who before.execution.application.current.native.config.store ∧
      (graph).ownCompletions who after.execution.application.current.native.config.history =
        (graph).ownCompletions who before.execution.application.current.native.config.history := by
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have rawBefore := (menu).toRawTrace initial horizon scheduler prior
  have rawAfter := (menu).toRawTrace initial horizon scheduler trace
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized rawBefore
  have progress := phase_prefix_semantic_extension runtime leaks menu initial horizon scheduler
    before after prior trace kept ordered same
  obtain ⟨first, firstValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler rawBefore
  obtain ⟨last, lastValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler rawAfter
  have inputEq : before.execution.application.current.native.config.inputs =
      after.execution.application.current.native.config.inputs := by
    funext input
    exact (Option.some.inj (progress.1 (.inl input)
      (before.execution.application.current.native.config.inputs input) rfl)).symm
  have firstReached : before.execution.application.current.native.config.Reachable
      before.execution.application.current.native.config.inputs := by
    simpa only [firstValid.active.reachable.inputs_eq] using firstValid.active.reachable
  have lastReached : after.execution.application.current.native.config.Reachable
      before.execution.application.current.native.config.inputs := by
    rw [inputEq]
    simpa only [lastValid.active.reachable.inputs_eq] using lastValid.active.reachable
  have notPublication : ¬ ((graph).outputLayout event).IsPublication := by
    change ¬ (setup.eventGraph.outputLayout event).IsPublication
    have semanticBinding : setup.eventGraph.outputLayout event = .binding who payload := binding
    rw [semanticBinding]
    exact id
  exact (serviceGraph_revealRelaxedOrdered setup mode).ready_semantics_eq_of_extension
    before.execution.application.current.native.config
    after.execution.application.current.native.config firstReached lastReached who event
    readyBefore readyAfter ((graph).actor?_of_outputLayout_binding binding) notPublication
      progress.1 progress.2

/-- At two actual offers of the same still-ready binding, every argument of
the ordinary source getter is unchanged. New in-attempt foreign misses are
normalized at the saved boundary, including misses learned between the offers.
No equality of raw recall, physical clocks or private catalogues is required. -/
theorem phaseProposal_query_eq_at_retained_binding
    (complete : leaks = MessageNetwork.completePendingObservation)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before after : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior trace)
    (same : before.execution.application.attempt = after.execution.application.attempt)
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (activeBefore : before.actor = some who) (activeAfter : after.actor = some who)
    (requestBefore : before.execution.application.SeedRequest who
      ⟨before.execution.application.attempt, event⟩)
    (requestAfter : after.execution.application.SeedRequest who
      ⟨after.execution.application.attempt, event⟩) :
    phaseProposalQuery? setup mode runtime leaks plan who event
        (after.execution.recall who) (after.execution.observe app who) =
      phaseProposalQuery? setup mode runtime leaks plan who event
        (before.execution.recall who) (before.execution.observe app who) := by
  classical
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have rawBefore := (menu).toRawTrace initial horizon scheduler prior
  have rawAfter := (menu).toRawTrace initial horizon scheduler trace
  have orderedBefore := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized rawBefore
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler before after prior trace kept orderedBefore same
  have retired := congrArg Prod.snd metadata
  change before.execution.application.retired = after.execution.application.retired at retired
  have saved := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
    scheduler before after prior trace kept orderedBefore).2.2 same
  obtain ⟨phase, rest, installed, commitment, _inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler rawBefore
      who event payload binding requestBefore.2.2.1
  have frontier := (phaseApplication_frontier runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_frontier plan draw) rawBefore
  have savedPrefix : before.execution.application.entry.native.config.cut.IsPrefix phase.low := by
    have positioned := frontier.positioned
    rw [installed] at positioned
    exact positioned.1
  have low : before.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have failuresBefore := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
    scheduler rawBefore
  have failuresAfter := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
    scheduler rawAfter
  have failedPrefix : ∀ rank ≤ before.execution.application.attempt.phase,
      before.execution.application.current.native.failureOwnersBefore rank =
        after.execution.application.current.native.failureOwnersBefore rank := by
    intro rank bounded
    have first := failuresBefore.failureOwnersBefore_eq_below phase.low
      (fun event earlier => (savedPrefix.2 event).mpr earlier) rank (by omega)
    have second := failuresAfter.failureOwnersBefore_eq_below phase.low
      (fun event earlier => by rw [← saved]; exact (savedPrefix.2 event).mpr earlier)
      rank (by omega)
    rw [← first, ← second, ← saved]
  have semantics := binding_waiting_semantics setup mode runtime leaks bounds plan horizon
    scheduler before after prior trace kept same who event payload binding requestBefore.2.2.1
      requestAfter.2.2.1
  have archive := PhaseProposal.phase_commitment_prefix_sourceArchive runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler before prior phase
      (by simp only [installed, List.head?_cons, Option.mem_some_iff]) commitment trace kept (by
        intro middle middleTrace first last _strict
        have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
          initialized ((menu).toRawTrace initial horizon scheduler middleTrace)
        have lower := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
          horizon scheduler before middle prior middleTrace first orderedBefore
        have upper := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
          horizon scheduler middle after middleTrace trace last ordered
        have sameGeneration := congrArg CommitAttemptId.generation same
        have samePhase := congrArg CommitAttemptId.phase same
        cases firstAttempt : before.execution.application.attempt with
        | mk firstPhase firstGeneration =>
          cases middleAttempt : middle.execution.application.attempt with
          | mk middlePhase middleGeneration =>
            cases finalAttempt : after.execution.application.attempt with
            | mk finalPhase finalGeneration =>
              simp only [firstAttempt, middleAttempt, finalAttempt]
                at lower upper sameGeneration samePhase ⊢
              congr 1 <;> omega)
  obtain ⟨ending, endingEq, archiveEq⟩ := archive
  cases Option.some.inj endingEq
  have beforeArchive := PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete
    initial horizon scheduler before rawBefore who activeBefore
  have afterArchive := PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete
    initial horizon scheduler after rawAfter who activeAfter
  apply phaseProposalQuery?_eq_of_masked_prefix setup mode runtime leaks plan who event
    (after.execution.recall who) (before.execution.recall who)
    (after.execution.observe app who) (before.execution.observe app who) rfl rfl
  · exact semantics.1
  · exact same.symm
  · change after.execution.application.retired.map _ =
      before.execution.application.retired.map _
    rw [← retired]
  · intro rank bounded
    change rank ≤ after.execution.application.attempt.phase at bounded
    change after.execution.application.current.native.publicView.sourceFailureFootprint.1 rank =
      before.execution.application.current.native.publicView.sourceFailureFootprint.1 rank
    rw [State.sourceFailureFootprint_read, State.sourceFailureFootprint_read]
    exact (failedPrefix rank (by rw [same]; exact bounded)).symm
  · rw [beforeArchive, afterArchive, archiveEq]

/-- The later ordinary declaration uses the literal same value law as an
immediate declaration. Raw handle and certificate choices are retained on the
native side; this equality projects only the prepared typed value. -/
theorem phaseProposal_unflagged_value_law_at_retained_binding
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (horizon : Nat) (scheduler : (app).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (before after : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior trace)
    (same : before.execution.application.attempt = after.execution.application.attempt)
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (activeBefore : before.actor = some who) (activeAfter : after.actor = some who)
    (requestBefore : before.execution.application.SeedRequest who
      ⟨before.execution.application.attempt, event⟩)
    (requestAfter : after.execution.application.SeedRequest who
      ⟨after.execution.application.attempt, event⟩)
    (unsentBefore : ∀ message ∈ (app).outputs (before.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, event⟩)
    (unsentAfter : ∀ message ∈ (app).outputs (after.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨after.execution.application.attempt, event⟩) :
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
      (after.execution.recall who) (after.execution.observe app who)).map
        (fun response => response.transmission.bind PhaseProposal.bindingPreparation) =
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
        (before.execution.recall who) (before.execution.observe app who)).map
          (fun response => response.transmission.bind PhaseProposal.bindingPreparation) := by
  have beforeCallback : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨before.remaining, some who, before.execution⟩) := by
    simpa only [← activeBefore] using prior
  have afterCallback : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨after.remaining, some who, after.execution⟩) := by
    simpa only [← activeAfter] using trace
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  obtain ⟨first, firstQuery, firstLaw⟩ := phaseProposalUnflaggedBinding_preparation_law setup mode
    runtime leaks bounds plan complete covered maximal values fullValues horizon scheduler capacity
      before.remaining who before.execution (initialEq ▸ beforeCallback) event payload binding
        requestBefore unsentBefore
  obtain ⟨last, lastQuery, lastLaw⟩ := phaseProposalUnflaggedBinding_preparation_law setup mode
    runtime leaks bounds plan complete covered maximal values fullValues horizon scheduler capacity
      after.remaining who after.execution (initialEq ▸ afterCallback) event payload binding
        requestAfter unsentAfter
  have query := phaseProposal_query_eq_at_retained_binding setup mode runtime leaks bounds plan
    complete maximal horizon scheduler before after prior trace kept same who event payload binding
      activeBefore activeAfter requestBefore requestAfter
  have keys : last = first := Option.some.inj
    (lastQuery.symm.trans (query.trans firstQuery))
  cases keys
  exact lastLaw.trans firstLaw.symm

end Vegas
