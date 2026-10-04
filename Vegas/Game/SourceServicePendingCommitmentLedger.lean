/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalSlots
import Vegas.Game.SourceServicePendingPacketOrigin
import Vegas.Pending.ReactiveBindingCommitmentProvenance
import Vegas.Pending.ReactiveBindingRiskRecall

/-! # Actual owner commitment provenance at pending settlement

At an unrecorded owned opportunity every earlier at-turn call addresses an
event already completed. During the actual pending segment the owner sends
only its anchor and later silent responses. When that event completes, every
authentic owner commitment in the current traffic is therefore inert by actual
completion. This argument does not equate private candidate meanings.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The frame's actual activation and event-name records transfer the
at-turn property, without assuming equality of old private before-views. -/
theorem sourceServiceFrame_ownSubmissionsAtTurn
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Control) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original.execution repaired.execution)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some original))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some repaired))
    (atTurn : OwnSubmissionsAtTurn setup leaks repaired.execution who) :
    OwnSubmissionsAtTurn setup leaks original.execution who := by
  intro entry member event named
  have same := frame.submissionRiskRecords (runtime setup) leaks leftTrace rightTrace
  have present : (runtime setup).submissionRiskRecord leaks entry ∈
      (repaired.execution.recall who).map ((runtime setup).submissionRiskRecord leaks) := by
    rw [← same]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  obtain ⟨other, recalled, recordEq⟩ := List.mem_map.mp present
  have views := congrArg (fun record : Player × PublicView (graph setup) ×
    Option (graph setup).EventId => record.2.1) recordEq
  have names := congrArg (fun record : Player × PublicView (graph setup) ×
    Option (graph setup).EventId => record.2.2) recordEq
  change other.beforeView.application.publicView = entry.beforeView.application.publicView
    at views
  change (runtime setup).submittedEvent? leaks other.action =
    (runtime setup).submittedEvent? leaks entry.action at names
  rw [← views]
  exact atTurn other recalled event (names.trans named)

/-- Earlier at-turn submissions have completed when a new owned opportunity
is ready and still unrecorded. This applies to every constructor of a named call. -/
theorem ownSubmissionsAtTurn_earlier_completed
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (atTurn : OwnSubmissionsAtTurn setup leaks control.execution who)
    (pending : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some pending)
    (unrecorded : (runtime setup).eventRecorded leaks (control.execution.recall who) pending =
      false)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ control.execution.recall who)
    (event : (graph setup).EventId)
    (named : (runtime setup).submittedEvent? leaks entry.action = some event) :
    event ∈ control.execution.application.config.cut.completed := by
  by_contra unfinished
  have facts := legalFacts setup leaks horizon scheduler control trace
  have beforeReady := (PublicView.ownTurn?_spec _ who event (atTurn entry member event named)).1
  have current := (entry_view_current setup leaks control.execution facts.stable who entry member
    event beforeReady unfinished).1
  have ready : control.execution.application.publicView.EventReady event := by
    unfold PublicView.EventReady at beforeReady ⊢
    rw [← current]
    exact beforeReady
  have pendingReady := (PublicView.ownTurn?_spec _ who pending turn).1
  have same := (soleReady_of_ready setup control.execution.application
    ((control.execution.application.publicView_eventReady pending).mp pendingReady)).2 event ready
  subst event
  have recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) pending =
      true := List.any_eq_true.mpr ⟨entry, member, decide_eq_true named⟩
  rw [unrecorded] at recorded
  cases recorded

/-- Initialized traffic provenance recovers every actual owner commitment.
If the earlier named responses and the anchor event have really completed,
the silent tail contributes no further commitment; all actual owner commitments
are inert by completion, independent of private candidate meanings. -/
theorem sourceService_silent_tail_completed_commitment_ledger
    {horizon afterRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (after repaired : (application setup leaks).Execution) (who : Player)
    (afterTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨afterRemaining, none, after⟩))
    (earlier : List (application setup leaks).PlayerEntry)
    (anchor : (application setup leaks).PlayerEntry)
    (pending : (graph setup).EventId)
    (named : (runtime setup).submittedEvent? leaks anchor.action = some pending)
    (later : List (application setup leaks).PlayerEntry)
    (split : after.recall who = earlier ++ anchor :: later)
    (silent : ∀ entry ∈ later, entry.action.transmission = none)
    (earlierCompleted : ∀ entry ∈ earlier, ∀ event,
      (runtime setup).submittedEvent? leaks entry.action = some event →
        event ∈ after.application.config.cut.completed)
    (completed : pending ∈ after.application.config.cut.completed) :
    OwnerCommitmentsInertOrMatching who after repaired := by
  have facts := legalFacts setup leaks horizon scheduler _ afterTrace
  intro message member authored event candidate committed _valid
  obtain ⟨entry, recalled, material, transmission, _emitted, _state, _known, issued⟩ :=
    facts.provenance.inputs message member
  change entry ∈ after.recall message.id.1 at recalled
  change message.id.1 = who at authored
  rw [authored, split] at recalled
  have submitted : (runtime setup).submittedEvent? leaks entry.action = some event :=
    (submittedEvent_of_issued transmission issued).trans (by rw [committed]; rfl)
  left
  rcases List.mem_append.mp recalled with earlier | recent
  · exact earlierCompleted entry earlier event submitted
  · rcases List.mem_cons.mp recent with current | latest
    · subst entry
      have same : pending = event := Option.some.inj (named.symm.trans submitted)
      rwa [← same]
    · rw [silent entry latest] at transmission
      cases transmission

/-- The actual anchor and silent recall tail close the commitment ledger at
settlement. The real original run supplies completed-cut monotonicity; initialized
packet provenance supplies each packet's recorded response origin. -/
theorem sourceService_pending_completed_commitment_ledger
    {horizon beforeRemaining afterRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (before after repaired : (application setup leaks).Execution) (who : Player)
    (beforeTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨beforeRemaining, some who, before⟩))
    (afterTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨afterRemaining, none, after⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks before who)
    (pending : (graph setup).EventId)
    (turn : before.application.publicView.ownTurn? who = some pending)
    (unrecorded : (runtime setup).eventRecorded leaks (before.recall who) pending = false)
    (response : (application setup leaks).Action)
    (players : Player → (application setup leaks).Policy) (count : Nat)
    (reached : after ∈ ((application setup leaks).runRounds scheduler players count
      (before.respond (application setup leaks) who response)).support)
    (anchor : (application setup leaks).PlayerEntry)
    (named : (runtime setup).submittedEvent? leaks anchor.action = some pending)
    (later : List (application setup leaks).PlayerEntry)
    (split : after.recall who = before.recall who ++ anchor :: later)
    (silent : ∀ entry ∈ later, entry.action.transmission = none)
    (completed : pending ∈ after.application.config.cut.completed) :
    OwnerCommitmentsInertOrMatching who after repaired := by
  let app := application setup leaks
  have invariant := ReactiveApplication.Invariant.policyInvariant app
    ((runtime setup).reactiveCompletedInvariant leaks before.application.config.cut.completed)
      players
  have retained := invariant.runRounds scheduler count (before.respond app who response) after
    (by rw [((runtime setup).reactive_respond_application leaks before who response).1]) reached
  exact sourceService_silent_tail_completed_commitment_ledger after repaired who afterTrace
    (before.recall who) anchor pending named later split silent
    (fun entry member event named => retained
      (ownSubmissionsAtTurn_earlier_completed _ beforeTrace who atTurn pending turn unrecorded
        entry member event named)) completed


end Vegas
