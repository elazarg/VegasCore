/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCountTransport

/-! # Literal counted transmission shape in a commitment interval -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Every permitted nonsilent response in an installed commitment interval is
literally a commitment packet. Arbitrary preparation and evidence aliases are
retained; neither a successful value nor a canonical source origin is assumed. -/
theorem onePacket_commitment_shape (bounds : MessageBounds graph)
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment) (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      onePacketActions runtime leaks bounds who (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who)) :
    ∃ event serial, material.call.packet = .commitment event (who, .prepared serial) := by
  classical
  obtain ⟨_bounded, permitted⟩ :=
    (mem_onePacketActions runtime leaks bounds who _ _ _).mp offered
  rcases permitted with impossible | ⟨supplied, same, allowed⟩
  · cases impossible
  cases Option.some.inj same
  have admitted := (permits_eq_true_iff _ _).mp allowed
  have authorized := (PhaseBindingRepair.localEnvelope_admitted runtime leaks execution who
    material admitted.1).1
  have correct := admitted.2.1
  have actualCall : (nativeMessage (localEnvelope runtime leaks who (execution.recall who)
      (execution.observe (phaseApplication runtime leaks) who) material)).payload.call =
        material.call.packet := maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [actualCall] at correct
  cases call : material.call.packet with
  | commitment event candidate =>
      rw [call] at correct
      obtain ⟨_, _, ownerEq, ⟨serial, prepared⟩, _⟩ := correct
      change candidate.1 = who at ownerEq
      have candidateEq : candidate = (who, .prepared serial) := Prod.ext ownerEq prepared
      exact ⟨event, serial, by rw [candidateEq]⟩
  | malformed raw => simp only [call] at correct
  | opening event candidate raw =>
      have inside : event ∈ phase.events := by
        simpa only [PhaseRuntimeState.allows, installed, List.head?_cons, call, Payload.event?,
          decide_eq_true_eq] using authorized
      obtain ⟨lower, upper⟩ := (phase.mem_events event).mp inside
      have matched := phase.fields event lower upper
      rw [committing] at matched
      obtain ⟨owner, payload, layout⟩ := matched
      rw [call] at correct
      cases node : nodeView graph event with
      | sample ty law outputEq codeEq => cases outputEq.symm.trans layout
      | resolve owner ty binding checks outputEq codeEq => cases outputEq.symm.trans layout
      | bind owner ty outputEq codeEq =>
          simp only [node] at correct
          exact correct.2.elim

end Vegas.EventGraphRuntime.PhaseCount
