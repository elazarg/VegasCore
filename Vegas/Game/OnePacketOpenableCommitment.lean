/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSureFailure
import Vegas.Game.OnePacketIntendedProjection
import Vegas.Game.OnePacketLateSuccess
import Vegas.Game.OnePacketBindingSite

/-! # A commitment to an openable value completes with that value or fails

Let `who`, at its binding event pending at the configuration `sent`, have
emitted from a recorded entry the commitment of the event to a candidate whose
meaning is openable at a value of the bound type. The owner's one packet is the
only commitment the contract can install at the event
(`Vegas.onePacket_accepted_new`), so, under every transition, the
configuration stays `sent` until the event completes, and the event completes
from `sent` either by the action binding that value or by a failure
(`Vegas.OpenableCommitmentInvariant`,
`Vegas.openableCommitmentInvariant_transition`). Under a scheduler completing
play, every stop of play until the event completes is such a completion
(`Vegas.openableCommitment_stop`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

variable (setup leaks) in
/-- **The openable-commitment invariant** after `who` emits, from a recorded
entry, the commitment of its binding event `event` to `candidate`, whose fixed
meaning is the successful value `value` that `action` binds: the history is
legal, the entry is recorded, the configuration is `sent` while the event is
unfinished, and once it has completed the configuration is one step of the
event from `sent`, by `action` or by a failure. -/
def OpenableCommitmentInvariant (who : Player) (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload) (value : L.Val payload)
    (sent : (graph setup).Config) (ready : sent.cut.Ready event)
    (action : (graph setup).Action event) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control =>
      Nonempty (((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some control)) ∧
      RecordsEntry setup leaks who entry (some control) ∧ entry.emitted = some message ∧
      message.sender = who ∧ message.payload.call = .commitment event candidate ∧
      control.execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      (event ∉ control.execution.application.config.cut.completed →
        control.execution.application.config = sent) ∧
      (event ∈ control.execution.application.config.cut.completed →
        control.execution.application.config ∈ (sent.step event ready action).support ∨
          ∃ failing : (graph setup).Action event,
            (cast (congrArg EventGraph.EventField.Action outputEq) failing :
              PublicationResult (L.Val payload)) = .failure ∧
            control.execution.application.config ∈ (sent.step event ready failing).support)

omit [DecidableEq Player] [IExpr.ResultTypes L] [Fintype Player] in
private theorem cast_some_value {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] [Fintype Player] in
private theorem cast_cast_back {A B : Type} (same : A = B) (value : B) :
    cast same (cast same.symm value) = value := by
  cases same
  rfl

/-- **The openable-commitment invariant persists** under every transition of
the one-packet game from a state at which the event is unfinished. -/
theorem openableCommitmentInvariant_transition {who : Player}
    {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload} {sent : (graph setup).Config} {ready : sent.cut.Ready event}
    {action : (graph setup).Action event}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
    (before after : (application setup leaks).ProtocolState)
    (unfinished : ∀ control, before = some control →
      event ∉ control.execution.application.config.cut.completed)
    (joint : Player → Option (application setup leaks).Action)
    (legal : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : OpenableCommitmentInvariant setup leaks bounds horizon scheduler who entry message
      event candidate outputEq value sent ready action before)
    (reached : after ∈ (((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    OpenableCommitmentInvariant setup leaks bounds horizon scheduler who entry message event
      candidate outputEq value sent ready action after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨⟨trace⟩, records, emitted, sender, call, fixed, frozen, _⟩ := holds
      have pending := unfinished control rfl
      have atSent := frozen pending
      have afterRecords := recordsEntry_transition who entry (initialLaw setup) horizon scheduler
        _ after joint records reached
      cases after with
      | none => exact afterRecords.elim
      | some next =>
          have nextTrace : ((bounds.onePacketMenu (runtime setup) leaks).protocol
              (initialLaw setup) horizon scheduler).Trace (some next) :=
            .extend trace joint legal reached
          have kept := (keepsFixedCandidates_step (runtime setup) leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have lookupEq := kept candidate (by
            rw [fixed]
            exact fun impossible => by cases impossible)
          have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
          rcases transition_configStep (initialLaw setup) horizon scheduler control next joint
              reached with same | ⟨completed, completedReady, found, member⟩
          · refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call, lookupEq.trans fixed,
              fun _ => by first | exact same.symm.trans atSent | exact same.trans atSent,
              fun done => ?_⟩
            rw [same] at done
            exact (pending done).elim
          · have eventEq : completed = event := by
              rw [atSent] at completedReady
              exact ready_unique (setup := setup) _ completedReady ready
            subst eventEq
            have done : completed ∈ next.execution.application.config.cut.completed := by
              rw [control.execution.application.config.step_cut completed completedReady found _
                member]
              exact Finset.mem_insert_self _ _
            refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call, lookupEq.trans fixed,
              fun undone => (undone done).elim, fun _ => ?_⟩
            revert completedReady member
            rw [atSent]
            intro completedReady member
            have output := step_binding_output (outputEq := outputEq) (codeEq := codeEq) member
            have nextRawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
                scheduler).Trace (some next) :=
              (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
                scheduler nextTrace
            have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
                scheduler).Trace (some control) :=
              (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
                scheduler trace
            have facts := legalFacts setup leaks horizon scheduler _ rawTrace
            have nextFacts := legalFacts setup leaks horizon scheduler _ nextRawTrace
            cases result : (cast (congrArg EventGraph.EventField.Action outputEq) found :
                PublicationResult (L.Val payload)) with
            | failure => exact Or.inr ⟨found, result, member⟩
            | success read =>
                left
                have reads : (⟨.inr completed, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
                    (.binding who payload)).get? next.execution.application.config.store =
                    some (.success read) := by
                  simp only [EventGraph.FieldRef.get?]
                  change cast _ (next.execution.application.config.outputs completed) = _
                  rw [output, cast_some_value (congrArg EventGraph.EventField.Value outputEq),
                    cast_cast_back, result]
                obtain ⟨installed, acceptedAt, _, meaning⟩ :=
                  nextFacts.binding.success_provenance _ read reads
                have vacant : control.execution.application.accepted (.inr completed) = none := by
                  cases present : control.execution.application.accepted (.inr completed) with
                  | none => rfl
                  | some present' =>
                      exact (pending (facts.binding.toAssociationInvariant.accepted_complete
                        completed present' present)).elim
                have same := onePacket_accepted_new bounds horizon scheduler trace records
                  emitted sender call owned vacant joint reached installed acceptedAt
                subst same
                rw [lookupEq, fixed] at meaning
                injection meaning with rawEq
                injection rawEq with _ valueEq
                have foundEq : found = action := by
                  have bothEq : (cast (congrArg EventGraph.EventField.Action outputEq) found :
                      PublicationResult (L.Val payload)) =
                      cast (congrArg EventGraph.EventField.Action outputEq) action := by
                    rw [result, successful, valueEq]
                  exact (cast_inj _).mp bothEq
                rw [← foundEq]
                exact member

omit [Fintype Player] in
/-- A configuration one step of the ready event of rank `rank` from a prefix of
`rank` events is a prefix of `rank + 1` events. -/
theorem isPrefix_succ_of_mem_step {sent after : (graph setup).Config} {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) {event : (graph setup).EventId}
    (ready : sent.cut.Ready event) {action : (graph setup).Action event}
    (member : after ∈ (sent.step event ready action).support) :
    after.cut.IsPrefix (rank + 1) := by
  rw [sent.step_cut event ready action _ member]
  exact ordered.complete_at event ready ((ready_iff_rank setup sent rank ordered event).mp ready)

/-- **Every stop completes the commitment.** Under a scheduler completing play,
from a history at which the openable-commitment invariant holds for an event of
rank `rank` still unfinished, every stop of play of any profile until the event
completes is one step of the event from `sent`, by the committed action or by a
failure. -/
theorem openableCommitment_stop
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload} {sent : (graph setup).Config} {ready : sent.cut.Ready event}
    {action : (graph setup).Action event}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
    {rank : Nat} (ordered : sent.cut.IsPrefix rank)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (holds : OpenableCommitmentInvariant setup leaks bounds horizon scheduler who entry message
      event candidate outputEq value sent ready action start.state) :
    ∀ stop ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (LateStopped setup leaks bounds horizon scheduler rank) start).support,
      ∃ final, stop.state = some final ∧
        (final.execution.application.config ∈ (sent.step event ready action).support ∨
          ∃ failing : (graph setup).Action event,
            (cast (congrArg EventGraph.EventField.Action outputEq) failing :
              PublicationResult (L.Val payload)) = .failure ∧
            final.execution.application.config ∈ (sent.step event ready failing).support) := by
  intro stop member
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have unfinishedOf : ∀ history : (menu.protocol (initialLaw setup) horizon scheduler).History,
      ¬ LateStopped setup leaks bounds horizon scheduler rank history →
      OpenableCommitmentInvariant setup leaks bounds horizon scheduler who entry message event
        candidate outputEq value sent ready action history.state →
      ∀ control, history.state = some control →
        event ∉ control.execution.application.config.cut.completed := by
    intro history going invariant control state done
    rw [state] at invariant
    obtain ⟨_, _, _, _, _, _, _, completion⟩ := invariant
    apply going
    refine ⟨control, state, ?_⟩
    rcases completion done with stepped | ⟨failing, _, stepped⟩
    · exact isPrefix_succ_of_mem_step ordered ready stepped
    · exact isPrefix_succ_of_mem_step ordered ready stepped
  have reachedInvariant := model.runBehavioralUntil_support_closed_of_going certificate players
    (LateStopped setup leaks bounds horizon scheduler rank)
    (OpenableCommitmentInvariant setup leaks bounds horizon scheduler who entry message event
      candidate outputEq value sent ready action)
    (fun history going _ joint legal target holds reached =>
      openableCommitmentInvariant_transition bounds horizon scheduler codeEq successful
        history.state target (unfinishedOf history going holds) joint legal holds reached)
    start holds stop member
  have ends := model.mem_support_runBehavioralUntil certificate players _ start stop member
  cases state : stop.state with
  | none =>
      rw [state] at reachedInvariant
      exact reachedInvariant.elim
  | some final =>
      rw [state] at reachedInvariant
      obtain ⟨⟨finalTrace⟩, _, _, _, _, _, frozen, completion⟩ := reachedInvariant
      refine ⟨final, rfl, completion ?_⟩
      by_contra pending
      have atSent := frozen pending
      rcases ends with ⟨other, otherState, prefixed⟩ | ended
      · rw [state] at otherState
        cases Option.some.inj otherState
        rw [atSent] at prefixed
        exact Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)
      · rw [state] at ended
        have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
            scheduler).Trace (some final) :=
          menu.toRawTrace (initialLaw setup) horizon scheduler finalTrace
        have terminal := completes final rawTrace ended
        exact pending (by rw [terminal]; exact Finset.mem_univ _)

/-- **A slot commitment sets up the invariant.** Along a history of the
one-packet game, at a decision of `who` at its pending binding `event`,
committing at a slot the count verdict permits a source choice encoded as an
action binding the successful value `value` leaves the openable-commitment
invariant, from the configuration of the decision, at the state it reaches. -/
theorem openableCommitmentInvariant_slot {remaining : Nat} {who : Player}
    {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    {event : (graph setup).EventId} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (ready : execution.application.config.cut.Ready event) (slot : Nat)
    (choice : Option (OwnAction Player L)) (action : (graph setup).Action event)
    (encoded : choice.bind (encodeEventAction? setup.program event) = some action)
    {value : L.Val payload}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
    (permitted : countPermits ((application setup leaks).outputs (execution.recall who))
      (slotEnvelope setup leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event slot) = true)
    (afterTrace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨remaining, none, execution.respond (application setup leaks)
        who (slotResponse setup leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event slot choice)⟩)) :
    ∃ entry message, OpenableCommitmentInvariant setup leaks bounds horizon scheduler who entry
      message event (who, .prepared slot) outputEq value execution.application.config ready
      action (some ⟨remaining, none, execution.respond (application setup leaks) who
        (slotResponse setup leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event slot choice)⟩) := by
  let response := slotResponse setup leaks who (execution.recall who)
    (execution.observe (application setup leaks) who) event slot choice
  obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup leaks who
    (execution.recall who) (execution.observe (application setup leaks) who) event node slot
    choice action encoded
  have call : material.call.packet = .commitment event (who, .prepared slot) :=
    congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
      message.payload.call) envelope
  have sends : response.transmission = some material := transmits
  have bound := slotResponse_of_bind setup leaks who (execution.recall who)
    (execution.observe (application setup leaks) who) event node slot choice action encoded
  rw [bound] at transmits
  have materialEq := Option.some.inj transmits.symm
  have submitted : (application setup leaks).submit execution.application who material =
      (execution.respond (application setup leaks) who
        ⟨some ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, value⟩⟩,
          .none⟩⟩).application := by
    rw [materialEq]
    change (application setup leaks).submit execution.application who
      (((runtime setup).reactiveNormalization leaks).normalize who
        ((application setup leaks).observePlayer execution.application who)
        (ReactiveApplication.ResponseMenu.knownPackets (execution.recall who)
          (execution.observe (application setup leaks) who))
        ⟨⟨.commitment event (who, .prepared slot), match (cast (congrArg
          EventGraph.EventField.Action outputEq) action : PublicationResult (L.Val payload)) with
          | .failure => none
          | .success value => some ⟨payload, value⟩⟩, .none⟩) = _
    rw [((runtime setup).reactiveNormalization leaks).submit, successful]
    rfl
  have fresh : execution.application.candidates.lookup (who, .prepared slot) = .fresh :=
    onePacket_permitted_fresh (control := ⟨remaining, some who, execution⟩) trace who event slot
      permitted
  have responded : (execution.respond (application setup leaks) who response).application =
      (application setup leaks).submit execution.application who material := by
    unfold ReactiveApplication.Execution.respond
    rw [sends]
  have sameConfig : (execution.respond (application setup leaks) who
      response).application.config = execution.application.config :=
    ((runtime setup).reactive_respond_application leaks execution who response).1
  refine ⟨respondEntry setup leaks execution who response, sentEnvelope setup leaks execution who
    material, ⟨afterTrace⟩, recordsEntry_respond execution who response remaining none, ?_, rfl,
    call, ?_, fun _ => sameConfig, fun done => ?_⟩
  · change response.transmission.map (sentEnvelope setup leaks execution who) = _
    rw [sends]
    rfl
  · rw [responded, submitted]
    change (submitStep (Submission.register
      ⟨.commitment event (who, .prepared slot), some ⟨payload, value⟩⟩
      execution.application who) who
      (.commitment event (who, .prepared slot))).candidates.lookup (who, .prepared slot) = _
    simp [submitStep, Submission.register, fresh, CommitmentCandidates.lookup_freeze_self,
      CommitmentCandidates.lookup_prepare_self]
  · rw [sameConfig] at done
    exact (ready.1 done).elim

end Vegas
