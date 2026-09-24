/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningService
import VegasTests.SelectiveAssociationResponses
import Vegas.Pending.ReactiveBindingOrigin
import Vegas.Pending.ReactiveSelectionObservation

/-! # Older opening envelopes at native publication decisions

There are at most two earlier owner responses. A successful binding accounts
for one commitment envelope, leaving at most one distinct envelope addressed
to the owner's publication. All earlier response choices remain unrestricted.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

private theorem unique_of_two_with_excluded {α : Type} (entries : List α)
    (bounded : entries.length ≤ 2) (qualifies : α → Prop)
    (excluded : ∃ entry ∈ entries, ¬qualifies entry) :
    ∀ first ∈ entries, ∀ second ∈ entries, qualifies first → qualifies second → first = second := by
  rcases entries with _ | ⟨a, rest⟩
  · simp at excluded
  rcases rest with _ | ⟨b, rest⟩
  · intro first firstMem second secondMem _ _
    exact (List.mem_singleton.mp firstMem).trans (List.mem_singleton.mp secondMem).symm
  have empty : rest = [] := by
    have zero : rest.length = 0 := by simp only [List.length_cons] at bounded; omega
    simpa only [List.length_eq_zero_iff] using zero
  subst rest
  obtain ⟨entry, member, no⟩ := excluded
  intro first firstMem second secondMem firstGood secondGood
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member firstMem secondMem
  rcases member with rfl | rfl <;> rcases firstMem with rfl | rfl <;>
    rcases secondMem with rfl | rfl <;> first | rfl | exact (no firstGood).elim |
      exact (no secondGood).elim

theorem native_accepted_recall (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) :
    nativeRuntime.AcceptedRecall nativeLeaks control.execution := by
  have raw := nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace
  exact nativeRuntime.acceptedRecall_history nativeLeaks (FinDist.pure nativeInputs)
    nativeHorizon nativeScheduler (by rw [FinDist.map_pure]; exact raw)

/-- Every compatible legal history has at most one older publication envelope.
The conclusion even allows foreign envelopes recalled from earlier replays. -/
theorem native_old_publication_unique (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (who : Player)
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (bit : Bool)
    (stored : (nativeBindingRef who).get? control.execution.application.config.store =
      some (.success bit)) :
    ∀ first ∈ nativeApp.outputs (control.execution.recall who),
      ∀ second ∈ nativeApp.outputs (control.execution.recall who),
        first.payload.call.event? nativeGraph = some (nativePublicationEvent who) →
        second.payload.call.event? nativeGraph = some (nativePublicationEvent who) →
          first = second := by
  have raw := nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace
  have binding := (nativeRuntime.reactiveBindingInvariant nativeLeaks).history
    (FinDist.pure nativeInitial) nativeHorizon nativeScheduler (by
      intro state member
      cases FinDist.mem_support_pure.mp member
      exact State.initial_bindingInvariant nativeInputs) raw
  obtain ⟨candidate, accepted, owner, _⟩ := binding.success_provenance (nativeBindingRef who)
    bit stored
  obtain ⟨event, field, different⟩ : ∃ event : nativeGraph.EventId,
      (nativeBindingRef who).field = .inr event ∧ event ≠ nativePublicationEvent who := by
    fin_cases who
    · exact ⟨aliceBinding, rfl, by decide⟩
    · exact ⟨bobBinding, rfl, by decide⟩
    · exact ⟨carolBinding, rfl, by decide⟩
  rw [field] at accepted
  obtain ⟨message, output, _, packet⟩ :=
    native_accepted_recall control trace event candidate accepted
  rw [owner] at output
  have count := native_decision_recall_count (nativePublicationEvent who) control trace who
    active granted who
  have bounded : (control.execution.recall who).length ≤ 2 := by
    rw [count]
    fin_cases who <;> decide
  apply unique_of_two_with_excluded (nativeApp.outputs (control.execution.recall who))
    ((List.length_filterMap_le _ _).trans bounded)
    (fun envelope => envelope.payload.call.event? nativeGraph = some (nativePublicationEvent who))
  refine ⟨message, output, ?_⟩
  rw [packet]
  exact fun same => different (Option.some.inj same)

theorem native_transport_history (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (who : Player)
    (active : control.actor = some who) :
    control.execution.Provenance nativeApp ∧ control.execution.InputRecall nativeApp ∧
      control.execution.network.PendingOrPublished ∧ control.execution.network.SerialsBeforeNext ∧
      control.execution.application.remembered = nativeInitial.remembered ∧
      ∀ response, (control.execution.respond nativeApp who response).SubmissionAudit nativeApp
        ReactivePlayerView.publicView := by
  have raw := nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace
  have remembered := (nativeRuntime.reactiveRememberedInvariant nativeLeaks
    (fun table => table = nativeInitial.remembered)).history (FinDist.pure nativeInitial)
      nativeHorizon nativeScheduler (by
        intro state member
        cases FinDist.mem_support_pure.mp member
        rfl) raw
  have audit := nativeApp.submissionAudit_history ReactivePlayerView.publicView
    (fun _ _ => rfl) (FinDist.pure nativeInitial) nativeHorizon nativeScheduler raw
  refine ⟨nativeApp.history_provenance (FinDist.pure nativeInitial)
      nativeHorizon nativeScheduler raw,
    nativeApp.history_inputRecall (FinDist.pure nativeInitial) nativeHorizon nativeScheduler raw,
    nativeApp.pendingOrPublished_history nativeScheduler (FinDist.pure nativeInitial)
      nativeHorizon raw,
    nativeApp.serialsBeforeNext_history nativeScheduler (FinDist.pure nativeInitial)
      nativeHorizon raw, remembered, ?_⟩
  intro response
  exact nativeApp.submissionAudit_respond ReactivePlayerView.publicView (fun _ _ => rfl)
    control.execution who response audit.1
    (nativeApp.submissionOrigin_next_none_history (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler control raw who) (audit.2 who active)

/-- Every raw response has the same publication-owner view after its reserved
inclusion at all legal histories with the same owner input. -/
theorem native_opening_reserved_local (left right : nativeApp.Control)
    (leftTrace : nativeArena.Trace (some left)) (rightTrace : nativeArena.Trace (some right))
    (who : Player) (leftActive : left.actor = some who) (rightActive : right.actor = some who)
    (sameInput : (left.execution.recall who, left.execution.observe nativeApp who) =
      (right.execution.recall who, right.execution.observe nativeApp who))
    (granted : left.execution.application.serviceGrant = some (nativePublicationEvent who))
    (bit : Bool)
    (stored : (nativeBindingRef who).get? left.execution.application.config.store =
      some (.success bit))
    (response : nativeApp.Action) (players : Player → nativeApp.Policy)
    (afterLeft afterRight : nativeApp.Execution)
    (leftMem : afterLeft ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest (nativePublicationEvent who) who)
      (left.execution.respond nativeApp who response)).support)
    (rightMem : afterRight ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest (nativePublicationEvent who) who)
      (right.execution.respond nativeApp who response)).support) :
    afterLeft.application.playerView who = afterRight.application.playerView who := by
  have recalls := congrArg Prod.fst sameInput
  have views := congrArg Prod.snd sameInput
  have applicationViews := congrArg ReactiveApplication.PlayerView.application views
  have ledgers := congrArg (fun view : nativeApp.PlayerView => view.messages.ledger) views
  have grants := congrArg (fun view : nativeApp.PlayerView =>
    view.application.publicView.serviceGrant) views
  have rightGrant : right.execution.application.serviceGrant =
      some (nativePublicationEvent who) := grants.symm.trans granted
  have rightStored : (nativeBindingRef who).get? right.execution.application.config.store =
      some (.success bit) := by
    have bindingViews := congrArg (fun view : nativeApp.PlayerView =>
      (nativeBindingRef who).get? view.application.observation.store) views
    change (nativeBindingRef who).get? (nativeGraph.playerStore who
      left.execution.application.config.store) = (nativeBindingRef who).get?
        (nativeGraph.playerStore who right.execution.application.config.store) at bindingViews
    rw [(nativeBindingRef who).get?_playerStore who _ rfl,
      (nativeBindingRef who).get?_playerStore who _ rfl, stored] at bindingViews
    exact bindingViews.symm
  obtain ⟨leftOrigins, leftRecall, leftRetained, leftSerials, leftMemory, leftAudit⟩ :=
    native_transport_history left leftTrace who leftActive
  obtain ⟨rightOrigins, rightRecall, rightRetained, rightSerials, rightMemory, rightAudit⟩ :=
    native_transport_history right rightTrace who rightActive
  have ownerViews := nativeRuntime.reactive_playerView_congr nativeLeaks left.execution.application
    right.execution.application who applicationViews (leftMemory.trans rightMemory.symm)
  have law := nativeRuntime.reactive_reserved_playerView_congr nativeLeaks who
    (nativePublicationEvent who) left.execution right.execution response ownerViews recalls ledgers
    leftOrigins rightOrigins leftRecall rightRecall leftRetained rightRetained
    (fun first firstMem second secondMem _ _ firstAt secondAt =>
      native_old_publication_unique left leftTrace who leftActive granted bit stored
        first firstMem second secondMem firstAt secondAt)
    (fun first firstMem second secondMem _ _ firstAt secondAt =>
      native_old_publication_unique right rightTrace who rightActive rightGrant bit rightStored
        first firstMem second secondMem firstAt secondAt)
    leftSerials rightSerials (leftAudit response) (rightAudit response)
  dsimp only at law
  rw [nativeRuntime.interaction_includeLatest_environment] at leftMem rightMem
  obtain ⟨next, pureStep⟩ := nativeRuntime.reactiveLatest_step_pure nativeLeaks who
    (nativePublicationEvent who) (left.execution.respond nativeApp who response)
  rw [pureStep] at leftMem
  have firstEq := FinDist.mem_support_pure.mp leftMem
  subst afterLeft
  rw [pureStep, FinDist.map_pure] at law
  have mapped : afterRight.application.playerView who ∈
      (FinDist.pure (next.application.playerView who)).support := by
    rw [law]
    rw [FinDist.support_map]
    exact ⟨afterRight, rightMem, rfl⟩
  exact (FinDist.mem_support_pure.mp mapped).symm

theorem native_publication_playerView_congr (left right : State nativeGraph) (who : Player)
    (views : left.playerView who = right.playerView who) :
    (nativePublicationRef who).get? left.config.store =
      (nativePublicationRef who).get? right.config.store := by
  have observed := congrArg (fun view : PlayerView nativeGraph =>
    (nativePublicationRef who).get? view.observation.store) views
  change (nativePublicationRef who).get? (nativeGraph.playerStore who left.config.store) =
    (nativePublicationRef who).get? (nativeGraph.playerStore who right.config.store) at observed
  rwa [(nativePublicationRef who).get?_playerStore who _ trivial,
    (nativePublicationRef who).get?_playerStore who _ trivial] at observed

end VegasTests.SelectiveAssociation
