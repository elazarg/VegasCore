/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCanonicalAcceptance
import Vegas.Game.OnePacketFreshSlots
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! # Retention of first canonical packets from bounds adequacy

**What is retained.** A decision of the effective opening is a successful
binding value at a binding and the disclosure at a reveal
(`Vegas.EffectiveDecision`). The canonical menu retains every transmitting
canonical decision of that kind, at a first turn within its inclusion window,
at every history of the one-packet game (`Vegas.RetainsCoveredCanonical`).

**Bounds adequacy.** Retention follows from two conditions on the message
bounds (`Vegas.retainsCoveredCanonical_of_adequate`): every value of every
binding and publication type is a bounded value (`CoversOutputValues`), and the
candidate capacity exceeds every player's number of binding events.

The capacity suffices because, along every one-packet history, a player's
canonical slot is at most its number of binding events: its completed bindings
are distinct binding events of its own, and its commitments name pairwise
distinct binding events of its own, since the count verdict permits one packet
per event (`Vegas.canonicalFreshSlot_le_bindingEvents`). Every packet a player
of the one-packet game emits is allowed by the bounds
(`Vegas.onePacket_outputsAllowed`), so every accepted handle is within
capacity.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Generic

variable {graph : EventGraph Player L}

variable (graph) in
/-- The number of binding events owned by `who`. -/
def bindingEventCount (who : Player) : Nat :=
  (Finset.univ.filter fun event => bindingOwnedBy graph who event = true).card

/-- A decision of the effective opening at an event: a successful binding value
at a binding, and either disclosure choice at a reveal. -/
def EffectiveDecision (event : graph.EventId) (action : graph.Action event) : Prop :=
  match nodeView graph event with
  | .bind _ payload outputEq _ => ∃ value : L.Val payload,
      action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (PublicationResult.success value)
  | .resolve .. | .sample .. => True

/-- A player's completed bindings are distinct binding events of its own. -/
theorem bindingCount_le_bindingEventCount (state : EventGraphRuntime.State graph)
    (who : Player) :
    state.publicView.bindingCount who ≤ bindingEventCount graph who := by
  have nodup := state.config.history_nodup
  change (state.config.history.map EventGraph.Completion.event).countP _ ≤ _
  generalize state.config.history.map EventGraph.Completion.event = order at nodup
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (nodup.filter _)]
  apply Finset.card_le_card
  intro event member
  rw [List.mem_toFinset, List.mem_filter] at member
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  unfold bindingOwnedBy
  exact member.2

/-- In count-clean traffic with unique identifiers, the committed prepared
slots of `who` name pairwise distinct binding events of its own: if its first
`count` slots are all committed, it owns at least `count` binding events. -/
theorem committedSlots_le_bindingEventCount
    {inputs : List (Message Player (WitnessedPacket graph))}
    (clean : ∀ message ∈ inputs, countPermits inputs message = true)
    (unique : ∀ message ∈ inputs, ∀ other ∈ inputs, other.id = message.id → other = message)
    (who : Player) (count : Nat)
    (committed : ∀ serial < count, SlotCommitted inputs who serial) :
    count ≤ bindingEventCount graph who := by
  classical
  have bound := Finset.card_le_card_of_forall_subsingleton
    (s := Finset.range count)
    (t := Finset.univ.filter fun event => bindingOwnedBy graph who event = true)
    (fun serial event => ∃ message ∈ inputs, message.sender = who ∧
      message.payload.call = .commitment event (who, .prepared serial))
    (fun serial member => by
      obtain ⟨message, present, owner, event, call⟩ :=
        committed serial (Finset.mem_range.mp member)
      have correct := ((countPermits_eq_true_iff _ _).mp (clean message present)).2.1
      unfold CountCallCorrect at correct
      rw [call] at correct
      exact ⟨event, Finset.mem_filter.mpr ⟨Finset.mem_univ _, owner ▸ correct.1⟩,
        message, present, owner, call⟩)
    (fun event _ serial ⟨_, first, firstIn, firstOwner, firstCall⟩
        other ⟨_, second, secondIn, secondOwner, secondCall⟩ => by
      by_cases same : first = second
      · subst same
        rw [firstCall] at secondCall
        obtain ⟨_, slotEq⟩ := Payload.commitment.inj secondCall
        exact Slot.prepared.inj (Prod.mk.inj slotEq).2
      · exfalso
        have idNe : first.id ≠ second.id := fun idEq =>
          same (unique second secondIn first firstIn idEq)
        have serialNe : first.id.2 ≠ second.id.2 := fun serialEq =>
          idNe (Prod.ext (firstOwner.trans secondOwner.symm) serialEq)
        rcases Nat.lt_or_gt_of_ne serialNe with earlier | later
        · have fresh := ((countPermits_eq_true_iff _ _).mp (clean second secondIn)).2.2
          apply fresh first ⟨firstIn, firstOwner.trans secondOwner.symm, earlier⟩
          rw [firstCall, secondCall]
          rfl
        · have fresh := ((countPermits_eq_true_iff _ _).mp (clean first firstIn)).2.2
          apply fresh second ⟨secondIn, secondOwner.trans firstOwner.symm, later⟩
          rw [firstCall, secondCall]
          rfl)
  simpa [bindingEventCount] using bound

/-- In count-clean traffic with unique identifiers, the public canonical slot
of `who` is at most its number of binding events when its completed bindings
are. -/
theorem publicFreshSlot_le_bindingEventCount
    {inputs : List (Message Player (WitnessedPacket graph))}
    (clean : ∀ message ∈ inputs, countPermits inputs message = true)
    (unique : ∀ message ∈ inputs, ∀ other ∈ inputs, other.id = message.id → other = message)
    (who : Player) {count serial : Nat} (counted : count ≤ bindingEventCount graph who)
    (selected : publicFreshSlot inputs who count = some serial) :
    serial ≤ bindingEventCount graph who := by
  classical
  unfold publicFreshSlot at selected
  split at selected
  · cases Option.some.inj selected
    exact counted
  · split at selected
    · rename_i uncommitted
      cases Option.some.inj selected
      by_contra exceeds
      have filled := committedSlots_le_bindingEventCount clean unique who
        (bindingEventCount graph who + 1) fun slot below =>
          not_not.mp (Nat.find_min uncommitted (by omega))
      omega
    · cases selected

end Generic

variable {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Allowed

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- An offered response transmits a packet the bounds allow. -/
theorem offered_packet_allowed (who : Player)
    (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView) (response : (application setup runtime
      leaks).Action)
    (member : response ∈ (bounds.menu runtime leaks).actions who past view)
    (material : (application setup runtime leaks).Submission)
    (sends : response.transmission = some material) :
    bounds.AllowsPacket material.call.packet := by
  obtain ⟨original, rawMember, normalized⟩ :=
    ((runtime.reactiveNormalization leaks).menu_mem
      (bounds.rawMenu runtime leaks) who past view response).mp member
  rcases original with ⟨_ | originalMaterial⟩
  · subst normalized
    cases sends
  · subst normalized
    change some _ = some material at sends
    cases Option.some.inj sends
    exact ((bounds.submissions_mem _ _).mp
      ((ReactiveApplication.ResponseMenu.fromSubmissions_mem _ who past view _).mp
        rawMember)).1.1

variable (setup runtime leaks) in
/-- Every packet a player recalls emitting is allowed by the bounds. -/
def OutputsAllowed (execution : (application setup runtime leaks).Execution) : Prop :=
  ∀ who, ∀ message ∈ (application setup runtime leaks).outputs (execution.recall who),
    bounds.AllowsPacket message.payload.call

/-- **Emitted packets are allowed** along every history of the one-packet game,
under every scheduler. -/
theorem onePacket_outputsAllowed (scheduler : (application setup runtime leaks).Scheduler) :
    (bounds.onePacketMenu runtime leaks).ServiceInvariant scheduler
      (OutputsAllowed setup runtime leaks bounds) where
  respond execution who action allowed member := by
    intro observer message output
    obtain ⟨entry, entryMember, emitted⟩ := List.mem_filterMap.mp output
    rw [respond_recall] at entryMember
    split at entryMember
    · rename_i same
      subst same
      rcases List.mem_append.mp entryMember with old | new
      · exact allowed observer message (List.mem_filterMap.mpr ⟨entry, old, emitted⟩)
      · obtain rfl := List.mem_singleton.mp new
        rcases action with ⟨_ | material⟩
        · cases emitted
        · cases Option.some.inj emitted
          exact offered_packet_allowed (runtime := runtime) bounds observer _ _ ⟨some material⟩
            ((bounds.mem_onePacketActions runtime leaks observer _ _ _).mp member).1
            material rfl
    · exact allowed observer message (List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩)
  environment execution next command allowed _ reached := by
    intro who message output
    rw [(application setup runtime leaks).environmentStep_recall execution next command reached]
      at output
    exact allowed who message output

end Allowed

section History

variable [Fintype Player] (bounds : MessageBounds (graph setup)) {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler} {control : (application setup runtime
    leaks).Control}

/-- **The canonical slot is within the binding events.** Along every history of
the one-packet game, the canonical slot of a player is at most its number of
binding events. -/
theorem canonicalFreshSlot_le_bindingEvents
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) {serial : Nat}
    (selected : canonicalFreshSlot who (control.execution.application.playerView who) =
      some serial) :
    serial ≤ bindingEventCount (graph setup) who := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have clean := (bounds.onePacketMenu_countClean runtime leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => runtime.countClean_initial leaks state) trace
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  rw [canonicalFreshSlot_eq_publicFreshSlot (preparedFresh_history (runtime := runtime) horizon
    scheduler rawTrace)]
    at selected
  exact publicFreshSlot_le_bindingEventCount clean.2
    (fun message member other otherMember => (facts.unique.inputs message member).inputs other
      otherMember)
    who (bindingCount_le_bindingEventCount control.execution.application who) selected

/-- **Accepted handles are allowed** along every history of the one-packet
game: input handles always are, and every other accepted handle is committed by
a packet its owner emitted. -/
theorem onePacket_accepted_allowed
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (field : (graph setup).Field) (candidate : Handle (graph setup))
    (accepted : control.execution.application.accepted field = some candidate) :
    bounds.AllowsHandle candidate := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have signed := signedCommitments_history runtime leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler rawTrace
  cases field with
  | inl input =>
      unfold MessageBounds.AllowsHandle
      rw [signed.inputHandles input candidate accepted]
      trivial
  | inr event =>
      obtain ⟨message, output, call⟩ := signed.acceptedSigned event candidate accepted
      have allowed := ((onePacket_outputsAllowed (runtime := runtime) bounds scheduler).history
        (initialLaw setup)
        horizon (fun _ _ _ _ output => (List.not_mem_nil output).elim) trace) candidate.1 message
        output
      rw [call] at allowed
      exact allowed

variable (setup runtime leaks) in
/-- **Retention of first covered canonical packets.** At every history of the
one-packet game, at an owner's turn at an event its recall has not submitted
for, while a fresh call still fits the deadline, every transmitting canonical
decision of the effective opening is retained by the canonical menu. -/
def RetainsCoveredCanonical (horizon : Nat) (scheduler : (application setup runtime
  leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) : Prop :=
  ∀ {control : (application setup runtime leaks).Control},
    ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) →
    ∀ who (event : (graph setup).EventId) (action : (graph setup).Action event),
    control.execution.application.publicView.ownTurn? who = some event →
    runtime.eventRecorded leaks (control.execution.recall who) event = false →
    control.execution.application.publicView.InclusionFitsDeadline runtime bound event →
    EffectiveDecision event action →
    (runtime.canonicalServiceDecision leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who) event action).transmission ≠
        none →
    runtime.canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who) event action ∈
      bounds.canonicalActions runtime leaks who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who)

/-- **Retention from bounds adequacy.** If every value of every binding and
publication type is a bounded value and the candidate capacity exceeds every
player's number of binding events, the canonical menu retains every first
covered canonical packet, under every scheduler and inclusion bound. -/
theorem retainsCoveredCanonical_of_adequate (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) :
    RetainsCoveredCanonical setup runtime leaks bounds horizon scheduler bound := by
  intro control trace who event action turn unsent fits effective transmits
  have ready := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      exfalso
      apply transmits
      simp only [canonicalServiceDecision, canonicalReactiveDecision, node]
      rfl
  | bind owner payload outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((EventGraph.actor?_of_outputLayout_binding _ outputEq).symm.trans owned)
      subst ownerEq
      simp only [EffectiveDecision, node] at effective
      obtain ⟨value, rfl⟩ := effective
      have values := covers event
      rw [outputEq] at values
      cases selected : canonicalFreshSlot owner
          (control.execution.observe (application setup runtime leaks) owner).application with
      | none =>
          exfalso
          apply transmits
          simp only [canonicalServiceDecision, canonicalReactiveDecision, node, selected,
            Option.map_none]
          rfl
      | some serial =>
          exact bounds.canonical_binding_value_retained runtime leaks owner _ _ event
            payload outputEq codeEq node turn owned ready fits.withinDeadline unsent serial
            selected
            (lt_of_le_of_lt (canonicalFreshSlot_le_bindingEvents (runtime := runtime) bounds trace
              owner selected)
              (capacity owner))
            value (values value)
  | resolve actor payload binding checks outputEq codeEq =>
      have values := covers event
      rw [outputEq] at values
      have choiceEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) := by
        simp
      rw [choiceEq]
      exact bounds.canonical_resolution_retained runtime leaks who _ _ event actor
        payload binding checks outputEq codeEq node turn owned ready fits.withinDeadline unsent _
        fun packet sent => bounds.resolutionPacket_allowed who event payload binding checks
          outputEq _ _ values
          (fun field candidate accepted =>
            onePacket_accepted_allowed (runtime := runtime) bounds trace field candidate accepted)
          packet sent

end History

end Vegas
