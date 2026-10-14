/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSlotContent
import Vegas.Game.OnePacketRevealMasses
import Vegas.Game.OnePacketOwnSubmissions
import Vegas.Game.OnePacketIntendedProjection

/-! # Zero-content responses are commitments at the player's turn

Along every history of the one-packet game, a transmitting response of a player
who owes no failure at the decoded point names the event of its turn
(`Vegas.onePacket_submission_atTurn`). At a reveal every offered packet decodes
to the disclosure, which as-if-honest play supports, so its content is
positive. Hence a transmitting response of content factor zero naming the event
of the player's turn commits at a binding of that turn
(`Vegas.zeroContent_binding_of_turn`), and so does every such response of a
player who owes no failure (`Vegas.zeroContent_binding`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **A zero-content response at the player's turn commits at a binding.** Along
every history of the one-packet game, a transmitting response of content factor
zero whose packet names the event of the player's turn commits at a binding
event of that turn. -/
theorem zeroContent_binding_of_turn (assessment : setup.intendedModel.BehavioralAssessment)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who (execution.recall who)
      (execution.observe (application setup leaks) who))
    (transmits : response.transmission ≠ none)
    (zero : contentFactor setup leaks assessment who execution
      (execution.respond (application setup leaks) who response) response = 0)
    (atTurn : ∀ named, (runtime setup).submittedEvent? leaks response = some named →
      execution.application.publicView.ownTurn? who = some named) :
    ∃ (event : (graph setup).EventId) (payload : L.Ty)
      (outputEq : (graph setup).outputLayout event = .binding who payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .bind who payload),
      execution.application.publicView.ownTurn? who = some event ∧
      nodeView (graph setup) event = .bind who payload outputEq codeEq := by
  obtain ⟨material, sends⟩ := Option.ne_none_iff_exists'.mp transmits
  obtain ⟨named, _, packetEvent, _, _⟩ := onePacket_sentSourceAction who _ _ response member
    material sends (execution.respond (application setup leaks) who response)
  have submitted : (runtime setup).submittedEvent? leaks response = some named := by
    unfold EventGraphRuntime.submittedEvent?
    rw [sends]
    exact packetEvent
  have turn : execution.application.publicView.ownTurn? who = some named :=
    atTurn named submitted
  have owned := (PublicView.ownTurn?_spec _ who named turn).2
  cases node : nodeView (graph setup) named with
  | sample payload law outputEq codeEq =>
      rw [nodeView_sample_actor outputEq codeEq] at owned
      cases owned
  | bind owner payload outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst ownerEq
      exact ⟨named, payload, outputEq, codeEq, turn, node⟩
  | resolve owner payload binding checks outputEq codeEq =>
      exfalso
      obtain ⟨source, supported⟩ := (asIfHonestProfile setup leaks assessment who
        (some (execution.recall who,
          execution.observe (application setup leaks) who))).support_nonempty
      have discloses := onePacket_honest_discloses assessment trace who named turn outputEq source
        supported
      cases source with
      | none => cases discloses
      | some action =>
          have decoded := decodeEventAction_encodeEventAction?_eq_some setup.program named action
            _ discloses
          -- The response is an opening of the reveal.
          obtain ⟨_, permitted⟩ := (bounds.mem_onePacketActions (runtime setup) leaks who _ _
            response).mp member
          have verdict : CountPermits ((application setup leaks).outputs (execution.recall who))
              ((runtime setup).localEnvelope leaks who (execution.recall who)
                (execution.observe (application setup leaks) who) material) := by
            rcases permitted with silent | ⟨other, otherSends, counted⟩
            · rw [sends] at silent
              cases silent
            · rw [sends] at otherSends
              cases Option.some.inj otherSends
              exact (countPermits_eq_true_iff _ _).mp counted
          have correct := verdict.2.1
          unfold CountCallCorrect at correct
          have callEq : ((runtime setup).localEnvelope leaks who (execution.recall who)
              (execution.observe (application setup leaks) who) material).payload.call =
              material.call.packet := rfl
          rw [callEq] at correct
          unfold contentFactor sentSourceAction at zero
          rw [sends] at zero
          dsimp only at zero
          generalize material.call.packet = packet at correct packetEvent zero
          cases packet with
          | malformed => exact correct.elim
          | commitment event candidate =>
              cases Option.some.inj packetEvent
              obtain ⟨ownedBy, _⟩ := correct
              unfold bindingOwnedBy at ownedBy
              rw [outputEq] at ownedBy
              cases ownedBy
          | opening event candidate raw =>
              cases Option.some.inj packetEvent
              simp only [node] at zero
              rw [decoded] at zero
              have positive := (PMF.mem_support_iff _ _).mp supported
              exact positive ((ENNReal.toReal_eq_zero_iff _).mp zero |>.resolve_right
                (PMF.apply_ne_top _ _))

/-- **A zero-content response commits at a binding of the player's turn.** Along
every history of the one-packet game, at a response of a player who owes no
failure at the decoded point, a transmitting response of content factor zero
commits at a binding event of the player's turn. -/
theorem zeroContent_binding (assessment : setup.intendedModel.BehavioralAssessment)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who (execution.recall who)
      (execution.observe (application setup leaks) who))
    (transmits : response.transmission ≠ none)
    (zero : contentFactor setup leaks assessment who execution
      (execution.respond (application setup leaks) who response) response = 0) :
    ∃ (event : (graph setup).EventId) (payload : L.Ty)
      (outputEq : (graph setup).outputLayout event = .binding who payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .bind who payload),
      execution.application.publicView.ownTurn? who = some event ∧
      nodeView (graph setup) event = .bind who payload outputEq codeEq := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace ⟨remaining, some who,
      execution⟩ rfl
  refine zeroContent_binding_of_turn assessment trace response member transmits zero
    fun named submitted => ?_
  rcases onePacket_submission_atTurn bounds (failureProfile setup.program) rawTrace residual
      response member named submitted with turn | owes
  · exact turn
  · exact (notOwed _ (decodedPoint_eq residual) (owes _ residual.decode)).elim

end Vegas
