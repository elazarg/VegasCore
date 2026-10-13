/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketRealizedCommitment
import Vegas.Game.OnePacketRetention

/-! # Covered pending bindings along one-packet histories

Along every history of the one-packet game, a prepared slot whose commitment
envelope the count verdict permits is fresh (`Vegas.onePacket_permitted_fresh`):
no earlier packet of the player commits to it. Some prepared slot is fresh, so
the canonical slot exists (`Vegas.onePacket_canonicalFreshSlot_exists`). At a
binding of the player's turn, when every binding value is a bounded value, every
source choice as-if-honest play supports encodes to a successful bounded value
(`Vegas.onePacket_honest_covered`), so the binding is a covered pending binding
(`Vegas.onePacket_coveredPendingBinding`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **Permitted slots are fresh.** Along every history of the one-packet game, a
prepared slot whose commitment envelope the count verdict permits against the
player's earlier packets is fresh. -/
theorem onePacket_permitted_fresh {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) (slot : Nat)
    (permitted : countPermits ((application setup leaks).outputs (control.execution.recall who))
      (slotEnvelope setup leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event slot) = true) :
    (control.execution.observe (application setup leaks) who).application.candidates
      (.prepared slot) = .fresh := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have recalled := (runtime setup).countRecall_history leaks rawTrace
  have correct := ((countPermits_eq_true_iff _ _).mp permitted).2.1
  unfold CountCallCorrect at correct
  obtain ⟨_, _, _, _, unused⟩ := correct
  refine ((preparedFresh_history horizon scheduler rawTrace) who slot).mpr ?_
  rintro ⟨message, input, sender, committed, call⟩
  have output : message ∈ (application setup leaks).outputs (control.execution.recall who) := by
    rw [← recalled.1 who]
    exact List.mem_filter.mpr ⟨input, by simp [sender]⟩
  obtain ⟨member, owner, lower⟩ := earlierOwnPacket_of_output rawTrace who
    (slotEnvelope setup leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event slot).payload message output
  refine unused message ⟨member, owner, ?_⟩ committed call
  change message.id.2 < (application setup leaks).submissionCount (control.execution.recall who)
  rw [← recalled.2.1 who]
  exact lower

/-- **The canonical slot exists.** Along every history of the one-packet game,
every player has a canonical slot. -/
theorem onePacket_canonicalFreshSlot_exists {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) :
    ∃ serial, canonicalFreshSlot who
      (control.execution.observe (application setup leaks) who).application = some serial := by
  classical
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have clean := (bounds.onePacketMenu_countClean (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (runtime setup).countClean_initial leaks state) trace
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  have uncommitted : ∃ serial, ¬ SlotCommitted control.execution.network.inputs who serial := by
    by_contra all
    push Not at all
    have bound := committedSlots_le_bindingEventCount clean.2
      (fun message member other otherMember => (facts.unique.inputs message member).inputs other
        otherMember)
      who (bindingEventCount (graph setup) who + 1) fun serial _ => all serial
    omega
  change ∃ serial, canonicalFreshSlot who (control.execution.application.playerView who) =
    some serial
  rw [canonicalFreshSlot_eq_publicFreshSlot (preparedFresh_history horizon scheduler rawTrace)]
  unfold publicFreshSlot
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **As-if-honest bindings are covered.** Along every history of the one-packet
game, at a binding of the player's turn, when every binding value is a bounded
value, every source choice as-if-honest play supports encodes to a successful
bounded value. -/
theorem onePacket_honest_covered (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (choice : Option (OwnAction Player L))
    (supported : choice ∈ (asIfHonestProfile setup leaks assessment who
      (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))).support) :
    CoveredBinding setup bounds event choice := by
  obtain ⟨rank, point, ordered, decoded⟩ :=
    onePacket_decodes (setup.intendedOpeningProfile assessment.strategy) trace
  have encodes := asIfHonestProfile_encodes assessment who control.execution rank ordered point
    decoded _ event turn choice supported
  obtain ⟨action, encoded⟩ := Option.isSome_iff_exists.mp encodes
  refine ⟨action, encoded, fun owner payload outputEq codeEq node => ?_⟩
  cases choice with
  | none => cases encoded
  | some source =>
      have back := decodeEventAction_encodeEventAction?_eq_some setup.program event source action
        encoded
      obtain ⟨noFailure, noWithholding⟩ := asIfHonestProfile_success assessment who
        control.execution rank ordered point decoded _ source supported
      have values := covers event
      rw [outputEq] at values
      generalize hresult : (cast (congrArg EventGraph.EventField.Action outputEq) action :
        PublicationResult (L.Val payload)) = result
      cases result with
      | success value => exact ⟨value, rfl, values value⟩
      | failure =>
          exfalso
          have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (PublicationResult.failure : PublicationResult (L.Val payload)) := by
            rw [← hresult]
            simp
          have failing : Failing (decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm)
                (PublicationResult.failure : PublicationResult (L.Val payload)))) :=
            decodeEventAction_failing_binding setup.program event.val (by exact event.isLt)
              (by exact outputEq)
          rw [← actionEq, back] at failing
          cases source with
          | commit sourceOwner name sourcePayload result =>
              have failed := failing.1 sourceOwner name sourcePayload result rfl
              subst failed
              exact noFailure sourceOwner name sourcePayload rfl
          | reveal sourceOwner name disclose =>
              have withheld : disclose = false := failing.2
              subst withheld
              exact noWithholding sourceOwner name rfl

/-- **A covered pending binding.** Along every history of the one-packet game,
at a binding of the player's turn, when every binding value is a bounded value
and the capacity is at least one, the binding is a covered pending binding. -/
theorem onePacket_coveredPendingBinding (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    CoveredPendingBinding setup leaks bounds assessment who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event payload outputEq
      codeEq where
  turn := turn
  node := node
  covered choice supported :=
    onePacket_honest_covered assessment covers trace who event turn choice supported
  capacity := capacity
  freshOfPermitted slot permitted := onePacket_permitted_fresh trace who event slot permitted

end Vegas
