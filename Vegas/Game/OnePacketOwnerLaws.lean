/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateLumping
import Vegas.Game.OnePacketBindingSite
import Vegas.Game.OnePacketLateMasses

/-! # The owner's law of moves for slot-trembled late components

At a pending binding of the owner's turn along a one-packet history, the
response committing a covered source choice at a slot within capacity moves as
the slot does: when the count verdict permits the slot's envelope, it commits at
the slot with a successful candidate, and otherwise it keeps silence
(`Vegas.commitMove_slotChoiceOf`). The move does not depend on the value.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **A permitted envelope is first for its event.** Along every history of
the one-packet game, when the count verdict permits a commitment of the player
for an event, the player has no pending commitment to it. -/
theorem commitStatuses_nil_of_permitted {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) (slot : Nat)
    (permitted : countPermits ((application setup leaks).outputs (control.execution.recall who))
      (slotEnvelope setup leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event slot) = true)
    (payload : L.Ty) :
    commitStatuses event who payload control.execution.application
      control.execution.network.pending = [] := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have recalled := (runtime setup).countRecall_history leaks rawTrace
  have facts := settledFacts_history (initialLaw setup) horizon scheduler rawTrace
  have first := ((countPermits_eq_true_iff _ _).mp permitted).2.2
  unfold commitStatuses
  rw [List.filterMap_eq_nil_iff]
  intro message member
  unfold commitStatus
  split
  · rename_i named candidate call
    split
    · rename_i owned
      exfalso
      obtain ⟨namedEq, sender⟩ := owned
      have input : message ∈ control.execution.network.inputs :=
        facts.carried.pending message member
      have output : message ∈ (application setup leaks).outputs
          (control.execution.recall who) := by
        rw [← recalled.1 who]
        exact List.mem_filter.mpr ⟨input, by simp [sender]⟩
      obtain ⟨inOutputs, owner, lower⟩ := earlierOwnPacket_of_output rawTrace who
        (slotEnvelope setup leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event slot).payload
        message output
      apply first message ⟨inOutputs, owner, ?_⟩
      · rw [call, namedEq]
        rfl
      · change message.id.2 < (application setup leaks).submissionCount
          (control.execution.recall who)
        rw [← recalled.2.1 who]
        exact lower
    · rfl
  · rfl

omit [Fintype Player] in
/-- A commitment to the binding at a handle whose candidate succeeds, made with
no pending commitment of the owner to it, moves to that handle. -/
theorem commitMove_eq_some {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    {execution : (application setup leaks).Execution} {action : (application setup leaks).Action}
    {submission : (application setup leaks).Submission} {candidate : Handle (graph setup)}
    (sent : action.transmission = some submission)
    (call : submission.call.packet = .commitment event candidate)
    (succeeds : candidateSucceeds ((application setup leaks).submit execution.application owner
      submission) candidate payload = true)
    (empty : commitStatuses event owner payload execution.application
      execution.network.pending = []) :
    commitMove event owner payload execution action = some (some candidate) := by
  have committed : ∃ (submission : (application setup leaks).Submission)
      (candidate : Handle (graph setup)), action.transmission = some submission ∧
      submission.call.packet = .commitment event candidate ∧
      candidateSucceeds ((application setup leaks).submit execution.application owner
        submission) candidate payload = true ∧
      commitStatuses event owner payload execution.application execution.network.pending = [] :=
    ⟨submission, candidate, sent, call, succeeds, empty⟩
  have notSilent : ¬ action.transmission = none := by
    rw [sent]
    exact Option.some_ne_none _
  unfold commitMove
  simp only [notSilent, ↓reduceIte, dite_eq_left committed]
  obtain ⟨chosenSent, chosenCall, _, _⟩ := committed.choose_spec.choose_spec
  have same : submission = committed.choose := Option.some.inj (sent.symm.trans chosenSent)
  have callEq : Payload.commitment event candidate =
      Payload.commitment event committed.choose_spec.choose := by
    rw [← call, same]
    exact chosenCall
  rw [(Payload.commitment.inj callEq).2]

omit [Fintype Player] in
/-- Silence moves to silence. -/
theorem commitMove_silent {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    (execution : (application setup leaks).Execution) :
    commitMove event owner payload execution ⟨none⟩ = some none := by
  unfold commitMove
  rfl

/-- The move of committing at a slot: to the slot's handle when the count
verdict permits its envelope, and silence otherwise. -/
def slotMove (execution : (application setup leaks).Execution) (who : Player)
    (event : (graph setup).EventId) (slot : Nat) : Option (Handle (graph setup)) :=
  if countPermits ((application setup leaks).outputs (execution.recall who))
      (slotEnvelope setup leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event slot) = true then
    some (who, .prepared slot)
  else none

/-- **The move of a slot-tier choice.** Along every history of the one-packet
game, at a covered pending binding of the player's turn, committing an
as-if-honest source choice at a slot within capacity moves as the slot does. -/
theorem commitMove_slotChoiceOf {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (event : (graph setup).EventId) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (site : CoveredPendingBinding setup leaks bounds assessment who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event payload outputEq codeEq)
    (slot : Nat) (capacity : slot < bounds.candidateCount) (choice : Option (OwnAction Player L))
    (supported : choice ∈ (asIfHonestProfile setup leaks assessment who
      (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))).support) :
    commitMove event who payload control.execution
        ((slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who
          (control.execution.recall who) (control.execution.observe (application setup leaks) who)
          event slot choice).1.getD ⟨none⟩) =
      some (slotMove control.execution who event slot) := by
  have covered := site.covered choice supported
  have membership := slotResponse_mem_onePacket_iff setup leaks bounds who
    (control.execution.recall who) (control.execution.observe (application setup leaks) who) event
    site.node slot capacity choice covered
  obtain ⟨action, encoded, values⟩ := covered
  obtain ⟨value, successful, _⟩ := values who payload outputEq codeEq site.node
  unfold slotMove
  by_cases permitted : countPermits ((application setup leaks).outputs
      (control.execution.recall who)) (slotEnvelope setup leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event slot) = true
  · have member := membership.mpr permitted
    simp only [permitted, ↓reduceIte]
    have chosen : (slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who
        (control.execution.recall who) (control.execution.observe (application setup leaks) who)
        event slot choice).1 = some (slotResponse setup leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event slot choice) := by
      simp only [slotChoiceOf, responseChoice, member, ↓reduceDIte]
    rw [chosen, Option.getD_some]
    obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)
      event site.node slot choice action encoded
    have call : material.call.packet = .commitment event (who, .prepared slot) :=
      congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
        message.payload.call) envelope
    have bound := slotResponse_of_bind setup leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event site.node slot choice
      action encoded
    rw [bound] at transmits
    have materialEq := Option.some.inj transmits.symm
    have submitted : (application setup leaks).submit control.execution.application who material =
        (control.execution.respond (application setup leaks) who
          ⟨some ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, value⟩⟩,
            .none⟩⟩).application := by
      rw [materialEq]
      change (application setup leaks).submit control.execution.application who
        (((runtime setup).reactiveNormalization leaks).normalize who
          ((application setup leaks).observePlayer control.execution.application who)
          (ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
            (control.execution.observe (application setup leaks) who))
          ⟨⟨.commitment event (who, .prepared slot), match (cast (congrArg
            EventGraph.EventField.Action outputEq) action : PublicationResult (L.Val payload)) with
            | .failure => none
            | .success value => some ⟨payload, value⟩⟩, .none⟩) = _
      rw [((runtime setup).reactiveNormalization leaks).submit, successful]
      rfl
    have fresh : control.execution.application.candidates.lookup (who, .prepared slot) = .fresh :=
      site.freshOfPermitted slot permitted
    have result := submitted_bindingResult (runtime setup) leaks control.execution who event
      payload slot (some ⟨payload, value⟩) fresh
    apply commitMove_eq_some (submission := material) (by rw [bound]; exact transmits) call
    · unfold candidateSucceeds
      rw [submitted]
      change (match (control.execution.respond (application setup leaks) who
          ⟨some ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, value⟩⟩,
            .none⟩⟩).application.bindingResult (who, .prepared slot) payload with
        | .success _ => true
        | .failure => false) = true
      rw [result]
      simp [Raw.as?]
    · exact commitStatuses_nil_of_permitted trace who event slot permitted payload
  · have notMember : slotResponse setup leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event slot choice ∉
        bounds.onePacketActions (runtime setup) leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) :=
      fun member => permitted (membership.mp member)
    simp only [permitted, Bool.false_eq_true, ↓reduceIte]
    have chosen : (slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who
        (control.execution.recall who) (control.execution.observe (application setup leaks) who)
        event slot choice).1 = some ⟨none⟩ := by
      simp only [slotChoiceOf, responseChoice, notMember, ↓reduceDIte]
    rw [chosen, Option.getD_some]
    exact commitMove_silent control.execution

end Vegas
