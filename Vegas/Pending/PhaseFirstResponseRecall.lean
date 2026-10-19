/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSuccessorRecall
import Interaction.ReactiveAnchoredPolicy
import Interaction.ReactiveRecordedResponseAfter
import Vegas.Pending.PhaseRecordedCountedRequest
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseAttemptCheckpoint
import Interaction.ReactiveProvenance
import Vegas.Pending.PhaseReadyRequests
import Vegas.Pending.PhaseReadiness

/-! # The first actual remembered response at a physical request -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A recorded request has an actual earliest callback, with the entire prior
own word and no earlier WAIT at that physical coordinate. This selects a real
occurrence and its initialized prefix, rather than reconstructing a view. -/
theorem phase_first_recorded_request_prefix (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some control))
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (recorded : PhaseCount.ResponseRecorded runtime leaks owner coordinate
      (control.execution.recall owner)) :
    ∃ (before : (app).Control)
      (prior : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some before)) (entry : (app).PlayerEntry),
      TracePrefix prior trace ∧ before.actor = some owner ∧
      entry ∈ control.execution.recall owner ∧
      entry.beforeView = before.execution.observe (app) owner ∧
      entry.action ∈ menu.actions owner (before.execution.recall owner)
        (before.execution.observe (app) owner) ∧
      before.execution.application.SeedRequest owner coordinate ∧
      ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate
        (before.execution.recall owner) ∧
      (∃ later, control.execution.recall owner =
        before.execution.recall owner ++ entry :: later) ∧
      ∃ postTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
          scheduler).Trace (some ⟨before.remaining, none,
            before.execution.respond (app) owner entry.action⟩),
        TracePrefix postTrace trace := by
  classical
  have first : ∀ past : List (app).PlayerEntry,
      PhaseCount.ResponseRecorded runtime leaks owner coordinate past →
      ∃ earlier entry later, past = earlier ++ entry :: later ∧
        PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate ∧
        ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate earlier := by
    intro past
    induction past with
    | nil =>
        rintro ⟨entry, impossible, _requested⟩
        cases impossible
    | cons entry rest ih =>
        intro found
        by_cases requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
            coordinate
        · exact ⟨[], entry, rest, rfl, requested, by
            rintro ⟨old, impossible, _⟩
            cases impossible⟩
        · have later : PhaseCount.ResponseRecorded runtime leaks owner coordinate rest := by
            obtain ⟨old, member, request⟩ := found
            rcases List.mem_cons.mp member with rfl | member
            · exact (requested request).elim
            · exact ⟨old, member, request⟩
          obtain ⟨earlier, selected, later, split, request, absent⟩ := ih later
          refine ⟨entry :: earlier, selected, later, by simp only [split, List.cons_append],
            request, ?_⟩
          rintro ⟨old, member, oldRequest⟩
          rcases List.mem_cons.mp member with rfl | member
          · exact requested oldRequest
          · exact absent ⟨old, member, oldRequest⟩
  obtain ⟨earlier, entry, later, split, requested, absent⟩ := first _ recorded
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨remaining, execution, prior, postTrace, postKept, past, viewed, allowed,
    priorPost, _length⟩ := menu.recorded_response_after initial horizon scheduler control trace
      owner earlier entry later split
  let before : (app).Control := ⟨remaining, some owner, execution⟩
  have kept : TracePrefix prior trace := priorPost.trans postKept
  have raw := menu.toRawTrace initial horizon scheduler prior
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have actualRequest : before.execution.application.SeedRequest owner coordinate := by
    rw [viewed] at requested
    exact (PhaseRuntimeState.requests_publicView _ valid owner coordinate).mp requested
  refine ⟨before, prior, entry, kept, rfl, ?_, viewed, ?_, actualRequest, ?_⟩
  · rw [split]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  · exact allowed
  · refine ⟨?_, ⟨later, ?_⟩, postTrace, postKept⟩
    · change ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate
        (execution.recall owner)
      rwa [past]
    · change control.execution.recall owner = execution.recall owner ++ entry :: later
      rwa [past]

/-- A previously offered coordinate in the current namespace, if still
unfinished, is the actual current request. Thus historical callbacks cannot
create additional unresolved owned episodes behind the current frontier. -/
theorem phase_recorded_unfinished_request (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId)
    (recorded : PhaseCount.ResponseRecorded runtime leaks owner
      ⟨control.execution.application.attempt, event⟩ (control.execution.recall owner))
    (unfinished : event ∉ control.execution.application.current.native.config.cut.completed) :
    control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩ := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨before, prior, _entry, kept, _acting, _member, _viewed, _offered, requested,
    _rest⟩ := phase_first_recorded_request_prefix runtime leaks menu plan inputs horizon scheduler
      control trace owner ⟨control.execution.application.attempt, event⟩ recorded
  have priorRaw := menu.toRawTrace initial horizon scheduler prior
  have raw := menu.toRawTrace initial horizon scheduler trace
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state positive
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
    exact PhaseRuntimeState.initial_ordered plan draw
  have beforeOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized priorRaw
  have extension := phase_prefix_semantic_extension runtime leaks menu initial horizon scheduler
    before control prior trace kept beforeOrdered requested.1.symm
  have ready : control.execution.application.current.native.config.cut.Ready event :=
    ⟨unfinished, fun _ predecessor =>
      completed_subset_of_history_prefix _ _ extension.2 (requested.2.2.1.2 predecessor)⟩
  have living := (phaseApplication_live runtime leaks).history initial horizon scheduler
    (fun state positive => by
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
      exact ⟨PhaseRuntimeState.initial_frontier plan draw,
        PhaseRuntimeState.initial_live plan draw⟩) raw
  have geometry := (phaseApplication_quiescent runtime leaks ordered).history initial horizon
    scheduler (fun state positive => by
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
      exact phaseApplication_initial_quiescent plan ordered maximal draw) raw
  exact control.execution.application.request_of_ready ordered living.1 living.2 geometry.2.1
    geometry.2.2 event ready owner requested.2.2.2.1

/-- Replaying a fixed physical past cannot override the prescribed law at a
request absent from that past, even when old idle/unsafe episodes are retained. -/
theorem phase_anchoredPolicy_eq_of_unrecorded (anchor : (app).Execution)
    (players : Player → (app).Policy) (owner : Player) (coordinate : CommitAttemptEvent graph)
    (absent : ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate (anchor.recall owner))
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (requested : PhaseRuntimeState.requests view.application.2 owner coordinate) :
    ReactiveApplication.anchoredPolicy anchor players owner past view =
      players owner past view := by
  classical
  unfold ReactiveApplication.anchoredPolicy
  cases found : (anchor.recall owner)[past.length]? with
  | none => rfl
  | some entry =>
      by_cases replayed : past ++ [entry] <+: anchor.recall owner ∧ entry.beforeView = view
      · exact (absent ⟨entry, replayed.1.subset
          (List.mem_append_right _ (List.mem_singleton_self _)),
          by rw [replayed.2]; exact requested⟩).elim
      · simp only [replayed, ↓reduceIte]

/-- At a remembered request absent from the anchored past, actual consistency
selects the continuing prescription. No old unsafe response is overwritten. -/
theorem phase_recorded_prescribed_response (anchor final : (app).Execution)
    (players : Player → (app).Policy) (owner : Player) (coordinate : CommitAttemptEvent graph)
    (absent : ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate (anchor.recall owner))
    (past later : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (recalled : final.recall owner = past ++ entry :: later)
    (consistent : (ReactiveApplication.anchoredPolicy anchor players owner).Consistent
      (final.recall owner))
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) :
    entry.action ∈ (players owner past entry.beforeView).support := by
  have faithful := recalled ▸ consistent
  rw [← List.singleton_append, ← List.append_assoc] at faithful
  have sampled := ((ReactiveApplication.anchoredPolicy anchor players owner).consistent_snoc_iff
    past entry).mp (ReactiveApplication.Policy.Consistent.of_append faithful)
  rw [phase_anchoredPolicy_eq_of_unrecorded runtime leaks anchor players owner coordinate absent
    past entry.beforeView requested] at sampled
  exact sampled.2

/-- On an actual counted history no remembered callback for a coordinate also
excludes every earlier emitted packet for it. Pending/retired packets are
retained and addressed by their real emitting observation. -/
theorem phase_unrecorded_request_unsent [Fintype Player] (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (absent : ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate
      (control.execution.recall owner)) :
    ∀ message ∈ (app).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have origins := (app).history_provenance initial horizon scheduler raw
  intro message output named
  have ownOutput := output
  rw [← clean.1.1 owner] at ownOutput
  obtain ⟨input, authored⟩ := List.mem_filter.mp ownOutput
  have authoredEq : message.sender = owner := of_decide_eq_true authored
  obtain ⟨entry, member, material, sent, emitted, _packet⟩ := origins.inputs message input
  rw [authoredEq] at member
  obtain ⟨actual, requested, actualAttempt, materialEvent⟩ :=
    PhaseCount.recorded_material_request runtime leaks bounds plan ordered inputs horizon scheduler
      control trace owner entry member material sent
  obtain ⟨other, otherEmitted, _otherOwner, call⟩ :=
    PhaseCount.recalled_submission_emitted runtime leaks initial horizon scheduler raw owner entry
      member material sent
  have otherEq : other = message := Option.some.inj (otherEmitted.symm.trans emitted)
  subst other
  have emissionAttempt := phase_recalled_emission_attempt runtime leaks initial horizon scheduler
    raw owner entry member message emitted
  have namedCoordinate : (⟨message.payload.attempt, actual.event⟩ : CommitAttemptEvent graph) =
      coordinate := by
    simpa only [PhaseCount.event?, call, materialEvent, Option.map_some, Option.some.injEq]
      using named
  have actualEq : actual = coordinate := by
    have sameAttempt := actualAttempt.trans emissionAttempt.symm
    have literal : actual = (⟨message.payload.attempt, actual.event⟩ :
        CommitAttemptEvent graph) := by
      cases actual with
      | mk attempt event =>
          exact congrArg (fun next => (⟨next, event⟩ : CommitAttemptEvent graph)) sameAttempt
    exact literal.trans namedCoordinate
  exact absent ⟨entry, member, actualEq ▸ requested⟩

end Vegas.EventGraphRuntime
