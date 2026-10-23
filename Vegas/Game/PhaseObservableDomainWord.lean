/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseObservableSourceQuery

/-! # Foreign domain queries from the retained native prefix

Current-phase failure masks and physical candidate catalogues are absent from
the binding query comparison. Its current typed input is the actual masked
store; the complete older public word is read below the saved phase boundary.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The observable public address word ignores current-phase failures. Only
the immutable retired images and failure prefixes below the saved cut matter. -/
theorem PhasePublicView.sourcePublicAddressWord_eq_of_prefix
    (plan : RuntimePhasePlan graph) (first second : PhasePublicView graph)
    (attempt : first.attempt = second.attempt) (archives : first.retired = second.retired)
    (same : ∀ rank ≤ first.attempt.phase,
      first.native.sourceFailureFootprint.1 rank = second.native.sourceFailureFootprint.1 rank)
    (eventRank : Nat) :
    first.sourcePublicAddressWord plan eventRank =
      second.sourcePublicAddressWord plan eventRank := by
  have scanned := plan.sourceArchiveAddresses_congr
    first.native.sourceFailureFootprint.1 second.native.sourceFailureFootprint.1
    first.attempt.generation first.attempt.phase
    (first.retired.map fun record => (record.1, record.2.sourceFailureFootprint)) 0 ∅ same
  have boundary := same first.attempt.phase le_rfl
  simp only [PhasePublicView.sourcePublicAddressWord]
  rw [← attempt, ← archives, ← boundary, ← scanned]

end Vegas.EventGraphRuntime

namespace Vegas.EventGraph

open EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- At two ready cuts of the same commitment event, only the old visible
prefix and preceding declarations of its own owner can affect the masked
store. Foreign completion order and hidden declarations are immaterial. -/
theorem RevealRelaxedOrdered.ready_binding_store_eq
    (ordered : graph.RevealRelaxedOrdered) (phase : RuntimePhase graph)
    (commitment : phase.kind = .commitment) (who : Player) (event : graph.EventId)
    (inside : event ∈ phase.events) (actor : graph.actor? event = some who)
    (left right : graph.Config)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (inputs : ∀ input, graph.fieldVisibleTo who (.inl input) →
      left.store (.inl input) = right.store (.inl input))
    (older : ∀ prior : graph.EventId, prior.val < phase.low →
      graph.fieldVisibleTo who (.inr prior) → left.store (.inr prior) = right.store (.inr prior))
    (ownEarlier : ∀ prior ∈ phase.events, prior.val < event.val →
      graph.actor? prior = some who → left.store (.inr prior) = right.store (.inr prior)) :
    graph.playerStore who left.store = graph.playerStore who right.store := by
  have ranks := (phase.mem_events event).mp inside
  obtain ⟨owner, payload, binding⟩ := commitment ▸ phase.fields event ranks.1 ranks.2
  have notPublication : ¬ (graph.outputLayout event).IsPublication := by
    simp only [binding, EventField.IsPublication, not_false_eq_true]
  apply graph.playerStore_congr
  intro field visible
  cases field with
  | inl input => exact inputs input visible
  | inr prior =>
      by_cases earlier : prior.val < event.val
      · by_cases old : prior.val < phase.low
        · exact older prior old visible
        · have priorInside := (phase.mem_events prior).mpr ⟨by omega, by omega⟩
          obtain ⟨priorOwner, priorPayload, priorBinding⟩ :=
            commitment ▸ phase.fields prior (by omega) (by omega)
          have sameOwner : priorOwner = who := by
            change (graph.outputLayout prior).VisibleTo who at visible
            simpa only [priorBinding, EventField.VisibleTo] using visible
          subst priorOwner
          exact ownEarlier prior priorInside earlier (actor?_of_outputLayout_binding graph
            priorBinding)
      · have absent (config : graph.Config) (ready : config.cut.Ready event) :
            config.outputs prior = none := by
          cases found : config.outputs prior with
          | none => rfl
          | some value =>
              exfalso
              apply earlier
              apply (ordered.ready_visible_iff config.cut ready actor visible
                (IndependentReveals.not_of_not_publication_right notPublication)
                (IndependentReveals.not_of_not_publication_left notPublication)).mp
              exact (config.output_available prior).mp (by simp only [found, Option.isSome_some])
        rw [Config.store_output, Config.store_output, absent left leftReady,
          absent right rightReady]

end Vegas.EventGraph

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

omit [Fintype Player] in
private theorem transported_store (who : Player)
    (view : EventGraphRuntime.PlayerView (serviceGraph setup mode)) (same : view.who = who) :
    (same ▸ view.observation).store = view.observation.store := by
  cases same
  rfl

/-- The exact native getter depends on the masked typed store and the saved
public prefix. It ignores changes in current exclusion masks, fresh handles,
transport identifiers, leaks and physical clock interleavings. -/
theorem phaseVirtualSourceQuery?_eq_of_masked_prefix
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (first second : (phaseApplication runtime leaks).PlayerView)
    (firstOwner : first.application.1.who = who)
    (secondOwner : second.application.1.who = who)
    (stores : first.application.1.observation.store = second.application.1.observation.store)
    (attempt : first.application.2.attempt = second.application.2.attempt)
    (archives : first.application.2.retired = second.application.2.retired)
    (same : ∀ rank ≤ first.application.2.attempt.phase,
      first.application.2.native.sourceFailureFootprint.1 rank =
        second.application.2.native.sourceFailureFootprint.1 rank) :
    phaseVirtualSourceQuery? setup mode runtime leaks plan who event first =
      phaseVirtualSourceQuery? setup mode runtime leaks plan who event second := by
  have typed : phaseVirtualSourceView? setup mode runtime leaks who event first =
      phaseVirtualSourceView? setup mode runtime leaks who event second := by
    simp only [phaseVirtualSourceView?, firstOwner, secondOwner, ↓reduceDIte]
    congr 2
    rw [transported_store, transported_store]
    exact stores
  have addresses := PhasePublicView.sourcePublicAddressWord_eq_of_prefix plan
    first.application.2 second.application.2 attempt archives same event.val
  have boundary := same first.application.2.attempt.phase le_rfl
  unfold phaseVirtualSourceQuery?
  dsimp only
  rw [typed]
  congr 1
  funext view
  rw [addresses]
  congr 2
  simp only [← attempt, ← archives, ← boundary]

omit [DecidableEq Player] [Fintype Player] in
private theorem saved_prefix {graph : Vegas.EventGraph Player L}
    (state : PhaseRuntimeState graph) (frontier : state.Frontier) (phase : RuntimePhase graph)
    (installed : phase ∈ state.phases.head?) :
    state.entry.native.config.cut.IsPrefix phase.low := by
  obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have positioned := frontier.positioned
  rw [phases] at positioned
  exact positioned.1

/-- The physical query comparison reduces to preceding own declarations at
the same saved native entry. Stored-checkpoint and public-failure invariants
derive every older typed field and public exclusion prefix; they are not
supplied as equal source observations. -/
theorem phaseVirtualSourceQuery?_eq_of_ready_saved
    (left right : (phaseApplication runtime leaks).Execution)
    (phase : RuntimePhase (serviceGraph setup mode)) (commitment : phase.kind = .commitment)
    (leftInstalled : phase ∈ left.application.phases.head?)
    (rightInstalled : phase ∈ right.application.phases.head?)
    (leftFrontier : left.application.Frontier) (rightFrontier : right.application.Frontier)
    (leftStored : left.application.StoredCheckpoint)
    (rightStored : right.application.StoredCheckpoint)
    (leftFailures : left.application.PublicFailureCheckpoint)
    (rightFailures : right.application.PublicFailureCheckpoint)
    (entry : left.application.entry = right.application.entry)
    (attempt : left.application.attempt = right.application.attempt)
    (archives : left.application.retired = right.application.retired)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (inside : event ∈ phase.events)
    (leftRequest : left.application.SeedRequest who ⟨left.application.attempt, event⟩)
    (rightRequest : right.application.SeedRequest who ⟨right.application.attempt, event⟩)
    (ownEarlier : ∀ prior ∈ phase.events, prior.val < event.val →
      (serviceGraph setup mode).actor? prior = some who →
        left.application.current.native.config.store (.inr prior) =
          right.application.current.native.config.store (.inr prior)) :
    phaseVirtualSourceQuery? setup mode runtime leaks plan who event
        (left.observe (phaseApplication runtime leaks) who) =
      phaseVirtualSourceQuery? setup mode runtime leaks plan who event
        (right.observe (phaseApplication runtime leaks) who) := by
  have firstPrefix := saved_prefix left.application leftFrontier phase leftInstalled
  have secondPrefix := saved_prefix right.application rightFrontier phase rightInstalled
  have firstCompleted (prior : (serviceGraph setup mode).EventId)
      (earlier : prior.val < phase.low) :
      prior ∈ left.application.entry.native.config.cut.completed :=
    (firstPrefix.2 prior).mpr earlier
  have low : left.application.attempt.phase = phase.low := by
    change (left.application.phases.head?.map RuntimePhase.low).getD
      (serviceGraph setup mode).order.eventCount = phase.low
    rw [Option.mem_def.mp leftInstalled]
    rfl
  change KeepsStore left.application.entry.native left.application.current.native at leftStored
  have rightKept : KeepsStore left.application.entry.native
      right.application.current.native := by
    change KeepsStore right.application.entry.native right.application.current.native at rightStored
    rw [← entry] at rightStored
    exact rightStored
  have inputs (input : (serviceGraph setup mode).InputId) :
      left.application.current.native.config.store (.inl input) =
        right.application.current.native.config.store (.inl input) := by
    exact (leftStored (.inl input) _ rfl).trans (rightKept (.inl input) _ rfl).symm
  have older (prior : (serviceGraph setup mode).EventId) (earlier : prior.val < phase.low) :
      left.application.current.native.config.store (.inr prior) =
        right.application.current.native.config.store (.inr prior) := by
    obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp
      ((left.application.entry.native.config.output_available prior).mpr
        (firstCompleted prior earlier))
    have stored : left.application.entry.native.config.store (.inr prior) = some value := found
    exact (leftStored (.inr prior) value stored).trans
      (rightKept (.inr prior) value stored).symm
  apply phaseVirtualSourceQuery?_eq_of_masked_prefix setup mode runtime leaks plan who event
    _ _ rfl rfl
  · change (serviceGraph setup mode).playerStore who
        left.application.current.native.config.store =
      (serviceGraph setup mode).playerStore who right.application.current.native.config.store
    exact (serviceGraph_revealRelaxedOrdered setup mode).ready_binding_store_eq phase commitment
      who event inside leftRequest.2.2.2.1 _ _ leftRequest.2.2.1 rightRequest.2.2.1
      (fun input _ => inputs input) (fun prior bound _ => older prior bound) ownEarlier
  · exact attempt
  · change left.application.retired.map _ = right.application.retired.map _
    rw [archives]
  · intro rank bounded
    change left.application.current.native.publicView.sourceFailureFootprint.1 rank =
      right.application.current.native.publicView.sourceFailureFootprint.1 rank
    rw [State.sourceFailureFootprint_read, State.sourceFailureFootprint_read]
    have leftEq := leftFailures.failureOwnersBefore_eq_below phase.low firstCompleted rank
      (by rwa [← low])
    have rightCompleted (prior : (serviceGraph setup mode).EventId)
        (earlier : prior.val < phase.low) := (secondPrefix.2 prior).mpr earlier
    have rightEq := rightFailures.failureOwnersBefore_eq_below phase.low rightCompleted rank
      (by rwa [← low])
    change left.application.current.native.failureOwnersBefore rank =
      right.application.current.native.failureOwnersBefore rank
    rw [← leftEq, ← rightEq, entry]

end Vegas
