/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSlotChoiceMasses
import Vegas.Game.OnePacketSourceTurn
import Vegas.Game.SourceServiceFacts
import Vegas.Pending.ReactiveOnePacketFreshness

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
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **Permitted slots are fresh.** Along every history of the one-packet game, a
prepared slot whose commitment envelope the count verdict permits against the
player's earlier packets is fresh. -/
theorem onePacket_permitted_fresh {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) (slot : Nat)
    (permitted : countPermits ((application setup runtime leaks).outputs (control.execution.logs
      who))
      (slotEnvelope setup runtime leaks who (control.execution.logs who)
        (control.execution.observe (application setup runtime leaks) who) event slot) = true) :
    (control.execution.observe (application setup runtime leaks) who).application.candidates
      (.prepared slot) = .fresh := by
  have inputTrace := trace
  rw [initialLaw, serviceInitialLaw_eq_inputs setup] at inputTrace
  exact bounds.onePacket_permitted_binding_fresh runtime leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler inputTrace who event slot none
    permitted

/-- **The canonical slot exists.** Along every history of the one-packet game,
every player has a canonical slot. -/
theorem onePacket_canonicalFreshSlot_exists {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) :
    ∃ serial, canonicalFreshSlot who
      (control.execution.observe (application setup runtime leaks) who).application = some serial
        := by
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
    scheduler trace
  rw [initialLaw, serviceInitialLaw_eq_inputs setup] at rawTrace
  have recalled := runtime.candidateRecall_history leaks (setup.initialLaw.map setup.eventInputs)
    horizon scheduler rawTrace
  obtain ⟨serial, _bound, fresh⟩ := runtime.reactiveFreshSlot_le_recall leaks
    control.execution who recalled
  exact canonicalFreshSlot_isSome who _ serial fresh

/-- **As-if-honest bindings are covered.** Along every history of the one-packet
game, at a binding of the player's turn, when every binding value is a bounded
value, every source choice as-if-honest play supports encodes to a successful
bounded value. -/
theorem onePacket_honest_covered (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (choice : Option (OwnAction Player L))
    (supported : choice ∈ (asIfHonestProfile setup runtime leaks assessment who
      (some (control.execution.logs who,
        control.execution.observe (application setup runtime leaks) who))).support) :
    CoveredBinding setup bounds event choice := by
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
    scheduler trace
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  have turnFacts := PublicView.ownTurn?_spec _ who event turn
  have active := control.execution.application.active_of_ready_owned facts.quiescent
    ((control.execution.application.publicView_eventReady event).mp turnFacts.1) turnFacts.2
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime)
    (setup.intendedOpeningProfile assessment.strategy) _ horizon scheduler trace control rfl
  have ordered := residual.checkpoint.ordered
  have decoded := residual.decode
  have encodes := asIfHonestProfile_encodes (runtime := runtime) assessment who control.execution
    rank ordered _
    decoded _ event turn active choice supported
  obtain ⟨action, encoded⟩ := Option.isSome_iff_exists.mp encodes
  refine ⟨action, encoded, fun owner payload outputEq codeEq node => ?_⟩
  cases choice with
  | none => cases encoded
  | some source =>
      have successful := asIfHonestProfile_success (runtime := runtime)
        assessment who
        control.execution rank ordered _ decoded _ source supported
      have values := covers event
      rw [outputEq] at values
      obtain ⟨value, actionEq⟩ := encodeEventAction?_commitsValue setup.program event source
        successful.1 action encoded owner payload outputEq
      exact ⟨value, by rw [actionEq]; simp, values value⟩

/-- **A covered pending binding.** Along every history of the one-packet game,
at a binding of the player's turn, when every binding value is a bounded value
and the capacity is at least one, the binding is a covered pending binding. -/
theorem onePacket_coveredPendingBinding (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    CoveredPendingBinding setup runtime leaks bounds assessment who (control.execution.logs who)
      (control.execution.observe (application setup runtime leaks) who) event payload outputEq
      codeEq where
  turn := turn
  active := by
    have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
      scheduler trace
    have facts := legalFacts setup leaks horizon scheduler control rawTrace
    have turnFacts := PublicView.ownTurn?_spec _ who event turn
    exact control.execution.application.active_of_ready_owned facts.quiescent
      ((control.execution.application.publicView_eventReady event).mp turnFacts.1) turnFacts.2
  node := node
  covered choice supported :=
    onePacket_honest_covered (runtime := runtime) assessment covers trace who event turn choice
      supported
  capacity := capacity
  freshOfPermitted slot permitted := onePacket_permitted_fresh (runtime :=
    runtime) trace who event slot permitted

end Vegas
