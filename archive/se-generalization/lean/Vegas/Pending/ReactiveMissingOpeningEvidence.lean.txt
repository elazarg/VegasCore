/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveMissingBindingTransport
import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.ReactiveSignedEvidence
import Interaction.ReactivePolicyInvariant

/-! # Opening claims for actually blocked binding candidates

A missing-opening commitment permanently blocks its freshly allocated candidate.
Sound owned and forwarded evidence cannot authenticate a later opening of that
candidate. Such an emitted claim belongs to the existing signed content breach
class, whose complete-settlement verdict and partial collection laws already apply.
No continuation payoff comparison or additional collection after a prior charge
follows from this classification.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Neither ownership nor forwarding can supply a matching certificate for an
actually blocked candidate. Authentic evidence for another candidate may remain. -/
theorem blockedOpening_no_matching_evidence (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (sound : (runtime.packetEvidence leaks).Sound execution)
    (who : Player) (submission : WitnessedSubmission graph) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L)
    (blocked : execution.application.candidates.lookup candidate = .unopenable)
    (opening : submission.call.packet = .opening event candidate raw) :
    (submission.emit ((runtime.reactiveApplication leaks).submit execution.application who
      submission) who (execution.network.known who)).evidence ≠ some ⟨candidate, raw⟩ := by
  have unchanged : (runtime.reactiveApplication leaks).submit execution.application who
      submission = execution.application := by
    rcases submission with ⟨⟨packet, material⟩, request⟩
    dsimp only at opening
    subst packet
    cases material <;> rfl
  rw [unchanged]
  intro matching
  have valid := submission.emit_sound execution.application who (execution.network.known who)
    (fun message member fact attached => sound.known who message member fact (by
      simp only [packetEvidence, attached, Option.toList_some, List.mem_singleton]))
    ⟨candidate, raw⟩ matching
  change execution.application.candidates.lookup candidate = .openable raw at valid
  rw [blocked] at valid
  cases valid

/-- An actual opening claim for a blocked candidate is an uncertified signed
breach, regardless of the evidence request's normal form or current event phase. -/
theorem blockedOpening_signedContentBreach (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (sound : (runtime.packetEvidence leaks).Sound execution)
    (who : Player) (submission : WitnessedSubmission graph) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L)
    (blocked : execution.application.candidates.lookup candidate = .unopenable)
    (opening : submission.call.packet = .opening event candidate raw) :
    SignedContentBreach ⟨(who, execution.network.nextSerial who), submission.emit
      ((runtime.reactiveApplication leaks).submit execution.application who submission)
        who (execution.network.known who)⟩ := by
  have absent := runtime.blockedOpening_no_matching_evidence leaks execution sound who
    submission event candidate raw blocked opening
  refine Or.inr (Or.inr (Or.inr ⟨event, candidate, raw, opening, ?_⟩))
  unfold certifiedOpening
  rw [WitnessedSubmission.emit_call, opening]
  cases attached : (submission.emit ((runtime.reactiveApplication leaks).submit
      execution.application who submission) who (execution.network.known who)).evidence with
  | none => rfl
  | some fact =>
      have different : fact ≠ ⟨candidate, raw⟩ := by
        intro same
        exact absent (attached.trans (congrArg some same))
      simp only [different, decide_false]

/-- Start with an actual missing-opening bare commitment at a legal raw history.
Every later opening claim for its candidate remains in the same signed breach
class under arbitrary player policies, scheduler choices, inclusion and forwarding. -/
theorem missingBinding_runRounds_opening_breach (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon remaining : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (binding : graph.EventId) (serial : Nat)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh)
    (rounds : Nat) (next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players rounds
      (execution.respond (runtime.reactiveApplication leaks) who
        ⟨some ⟨⟨.commitment binding (who, .prepared serial), none⟩, .none⟩⟩)).support)
    (submission : WitnessedSubmission graph) (event : graph.EventId) (raw : Raw L)
    (opening : submission.call.packet = .opening event (who, .prepared serial) raw) :
    SignedContentBreach ⟨(who, next.network.nextSerial who), submission.emit
      ((runtime.reactiveApplication leaks).submit next.application who submission)
        who (next.network.known who)⟩ := by
  let app := runtime.reactiveApplication leaks
  let candidate : Handle graph := (who, .prepared serial)
  let response : app.Action :=
    ⟨some ⟨⟨.commitment binding candidate, none⟩, .none⟩⟩
  let original := execution.respond app who response
  let resources (current : app.Execution) :=
    current.application.candidates.lookup candidate = .unopenable ∧
      (runtime.packetEvidence leaks).Sound current
  have preserved : app.PolicyInvariant players resources := {
    respond := by
      intro current actor action good _
      refine ⟨?_, (runtime.packetEvidence leaks).sound_respond current actor action good.2⟩
      exact (runtime.reactive_respond_candidate_fixed leaks current actor action candidate
        (by rw [good.1]; simp)).trans good.1
    environment := by
      intro current after command good moved
      refine ⟨?_, (runtime.packetEvidence leaks).sound_environment current after command
        good.2 moved⟩
      exact (runtime.reactive_environment_candidate_fixed leaks current after command candidate
        (by rw [good.1]; simp) moved).trans good.1 }
  have sound : (runtime.packetEvidence leaks).Sound execution :=
    (runtime.packetEvidence leaks).history_sound initial horizon scheduler trace
  have valid : resources original := ⟨runtime.bareBinding_submitted_unopenable leaks execution
    who binding serial fresh, (runtime.packetEvidence leaks).sound_respond execution who
      response sound⟩
  have final := preserved.runRounds scheduler rounds original next valid reached
  exact runtime.blockedOpening_signedContentBreach leaks next final.2 who submission event
    candidate raw final.1 opening

end Vegas.EventGraphRuntime
