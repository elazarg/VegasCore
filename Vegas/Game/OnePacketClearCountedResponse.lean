/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOffTurnPackets
import Vegas.Game.OnePacketClearRecord

/-! # Completed-event rejection at actual clear source callbacks

Clear public failure evidence removes the failure alternative from the actual
completed-owner record. Every permitted new signed callback therefore addresses
an unfinished event, including callbacks of the event's own player.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- Every completed owned event at an actual clear prefix has an authentic owner packet. -/
theorem completedByOwner_of_clear_trace {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId)
    (completed : event ∈ control.execution.application.config.cut.completed)
    (owner : Player) (acting : (graph setup).actor? event = some owner) :
    ∃ message ∈ control.execution.network.ledger, message.sender = owner ∧
      message.payload.call.event? (graph setup) = some event := by
  rcases completedByOwner_of_trace (runtime := runtime) trace control rfl event completed owner
    acting with
    packet | failure
  · exact packet
  · exfalso
    cases node : nodeView (graph setup) event with
    | bind actual payload outputEq codeEq =>
        have missed := (control.execution.application.publicView_missedBinding event actual
          payload outputEq).mpr ⟨completed, failure.2.1⟩
        have excluded := (clear.excluded_zero actual).mpr
          ⟨event, nodeView_bind_actor outputEq codeEq, Or.inl missed⟩
        exact Finset.notMem_empty actual excluded
    | resolve actual payload binding checks outputEq codeEq =>
        obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
          setup.program)
          (bounds.onePacketMenu runtime leaks) horizon scheduler trace control rfl
        have decoded := decodedPoint_eq residual
        exact not_revealFailed_of_exclusionEvidence control.execution.application clear rank _
          residual.decode owner (failure.2.2 payload outputEq _ decoded)
    | sample payload law outputEq codeEq =>
        have absent := nodeView_sample_actor outputEq codeEq
        rw [acting] at absent
        cases absent

/-- No permitted callback at an actual clear source prefix names a completed event. -/
theorem countPermits_localEnvelope_unfinished_of_clear_trace
    {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) (who : Player)
    (material : WitnessedSubmission (graph setup))
    (permitted : countPermits ((application setup runtime leaks).outputs (control.execution.recall
      who))
      (runtime.localEnvelope leaks who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who) material) = true)
    (event : (graph setup).EventId)
    (named : material.call.packet.event? (graph setup) = some event) :
    event ∉ control.execution.application.config.cut.completed := by
  intro completed
  let app := application setup runtime leaks
  let message := runtime.localEnvelope leaks who (control.execution.recall who)
    (control.execution.observe app who) material
  have allowed := (countPermits_eq_true_iff _ _).mp permitted
  have addressed : message.payload.call.event? (graph setup) = some event := named
  have acting := countCallCorrect_actor _ message allowed.2.1 addressed
  obtain ⟨old, onLedger, sender, oldNamed⟩ :=
    completedByOwner_of_clear_trace (runtime := runtime) trace clear event completed who acting
  let rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  obtain ⟨inputRecall, serialRecall, _⟩ := runtime.countRecall_history leaks rawTrace
  have facts := settledFacts_history (initialLaw setup) horizon scheduler rawTrace
  have present := facts.carried.ledger old onLedger
  have recalled : old ∈ app.outputs (control.execution.recall who) := by
    rw [← inputRecall who]
    exact List.mem_filter.mpr ⟨present, by simp only [sender, decide_true]⟩
  have lower := facts.serials.inputs old present
  change old.id.2 < control.execution.network.nextSerial old.sender at lower
  rw [sender, serialRecall who] at lower
  exact allowed.2.2 old ⟨recalled, sender, lower⟩ (oldNamed.trans addressed.symm)

/-- Every permitted clear source callback names a genuinely ready event. -/
theorem countPermits_localEnvelope_ready_of_clear_trace
    {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) (who : Player)
    (material : WitnessedSubmission (graph setup))
    (permitted : countPermits ((application setup runtime leaks).outputs (control.execution.recall
      who))
      (runtime.localEnvelope leaks who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who) material) = true)
    (event : (graph setup).EventId)
    (named : material.call.packet.event? (graph setup) = some event) :
    control.execution.application.config.cut.Ready event := by
  refine ⟨countPermits_localEnvelope_unfinished_of_clear_trace (runtime := runtime) trace clear
    who material permitted
    event named, ?_⟩
  have allowed := (countPermits_eq_true_iff _ _).mp permitted
  obtain ⟨actual, addressed, token⟩ := (WitnessedPacket.tokenValid_iff _).mp allowed.1
  have same : actual = event := Option.some.inj (addressed.symm.trans named)
  subst actual
  change control.execution.application.publicView.tokenFor material.call.packet =
    some ⟨event⟩ at token
  rw [PublicView.tokenFor, named, Option.bind_some] at token
  have prerequisites :=
    (PublicView.readinessToken?_eq_some_iff _ event ⟨event⟩).mp token
  intro predecessor member
  exact (control.execution.application.config.history_exact predecessor).mp
    (prerequisites.2 predecessor member)

end Vegas
