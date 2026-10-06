/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.EvidenceNormalization
import Interaction.ReactiveResponseNormalization

/-! # Semantic normal forms of event submissions

Opening material has an effect only when a submission fixes a fresh owned
prepared handle. Other opening material is a private representation artifact.
Successful certificate requests use the same representative exactly when they
issue the same certificate, whether by ownership or a known forwarding reference.
Normalization preserves the entire public packet, including malformed contents,
and changes no application or network effect. It uses only the sender's view.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def openingEffective (who : Player) (view : PlayerView graph) : Payload graph → Prop
  | .commitment _ (owner, .prepared serial) =>
      owner = who ∧ view.candidates (.prepared serial) = .fresh
  | _ => False

open Classical in
def Submission.normalizeReactive (who : Player) (view : PlayerView graph)
    (submission : Submission graph) : Submission graph :=
  ⟨submission.packet, if openingEffective who view submission.packet then submission.opening
    else none⟩

theorem Submission.normalizeReactive_packet (who : Player) (view : PlayerView graph)
    (submission : Submission graph) :
    (submission.normalizeReactive who view).packet = submission.packet := rfl

theorem Submission.normalizeReactive_idempotent (who : Player) (view : PlayerView graph)
    (submission : Submission graph) :
    (submission.normalizeReactive who view).normalizeReactive who view =
      submission.normalizeReactive who view := by
  classical
  simp only [normalizeReactive]
  split <;> rfl

/-- No metadata is removed when it can fix a commitment meaning. -/
theorem Submission.normalizeReactive_effective (who : Player) (view : PlayerView graph)
    (submission : Submission graph) (effective : openingEffective who view submission.packet) :
    submission.normalizeReactive who view = submission := by
  simp only [normalizeReactive, effective, ↓reduceIte]

theorem Submission.normalizeReactive_none (who : Player) (view : PlayerView graph)
    (packet : Payload graph) :
    (⟨packet, none⟩ : Submission graph).normalizeReactive who view = ⟨packet, none⟩ := by
  simp only [normalizeReactive, ite_self]

variable [DecidableEq Player]

theorem Submission.candidateAfter_opening (who : Player) (event : graph.EventId)
    (handle : Handle graph) (raw : Raw L) (material : Option (Raw L))
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L)) :
    (⟨.opening event handle raw, material⟩ : Submission graph).candidateAfter who candidates =
      candidates := by
  funext slot
  rfl

theorem Submission.normalizeReactive_candidateAfter (who : Player)
    (view : PlayerView graph) (submission : Submission graph)
    (slot : CandidateSlot graph) :
    (submission.normalizeReactive who view).candidateAfter who view.candidates slot =
      submission.candidateAfter who view.candidates slot := by
  classical
  rcases submission with ⟨packet, material⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, selected⟩
      cases selected with
      | initial input =>
          simp only [normalizeReactive, openingEffective, ↓reduceIte, candidateAfter]
      | prepared serial =>
          by_cases owned : owner = who
          · subst owner
            by_cases fresh : view.candidates (.prepared serial) = .fresh
            · simp [normalizeReactive, openingEffective, fresh]
            · by_cases same : slot = .prepared serial
              · subst slot
                cases meaning : view.candidates (.prepared serial) <;>
                  simp_all [normalizeReactive, openingEffective, candidateAfter]
              · simp [normalizeReactive, openingEffective, fresh, candidateAfter, same]
          · simp [normalizeReactive, openingEffective, owned, candidateAfter]
  | opening | malformed => rfl

theorem Submission.normalizeReactive_register (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (state : State graph) (submission : Submission graph) :
    (submission.normalizeReactive who
        ((runtime.reactiveApplication leaks).observePlayer state who)).register state who =
      submission.register state who := by
  classical
  rcases submission with ⟨packet, material⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      cases slot with
      | initial index => simp [normalizeReactive, openingEffective, register]
      | prepared serial =>
          by_cases same : owner = who
          · subst owner
            by_cases fresh : state.candidates.lookup (who, .prepared serial) = .fresh
            · simp [normalizeReactive, openingEffective, reactiveApplication, State.playerView,
                fresh]
            · cases material with
              | none =>
                  simp [normalizeReactive, openingEffective, reactiveApplication,
                    State.playerView, fresh]
              | some raw =>
                  simp [normalizeReactive, openingEffective, reactiveApplication,
                    State.playerView, fresh, register,
                    state.candidates.prepare_eq_self_of_not_fresh who (.prepared serial) raw fresh]
          · cases material <;> simp [normalizeReactive, openingEffective, register, same]
  | opening event candidate raw | malformed raw =>
      cases material <;> simp [normalizeReactive, openingEffective, register]

def WitnessedSubmission.normalizeReactive (who : Player) (view : PlayerView graph)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) : WitnessedSubmission graph :=
  ⟨submission.call.normalizeReactive who view,
    submission.evidence.normalize who (submission.call.candidateAfter who view.candidates) known⟩

theorem WitnessedSubmission.normalizeReactive_idempotent
    (who : Player) (view : PlayerView graph)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) :
    (submission.normalizeReactive who view known).normalizeReactive who view known =
      submission.normalizeReactive who view known := by
  have candidates : (submission.call.normalizeReactive who view).candidateAfter
      who view.candidates = submission.call.candidateAfter who view.candidates :=
    funext (Submission.normalizeReactive_candidateAfter who view submission.call)
  simp only [normalizeReactive, Submission.normalizeReactive_idempotent,
    candidates, EvidenceRequest.normalize_idempotent]

theorem WitnessedSubmission.normalizeReactive_emit
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) :
    (submission.normalizeReactive who
      ((runtime.reactiveApplication leaks).observePlayer state who) known).emit
        (submitStep (submission.call.register state who) who submission.call.packet) who known =
      submission.emit
        (submitStep (submission.call.register state who) who submission.call.packet) who known := by
  have candidates := funext (submission.call.candidateAfter_eq who state)
  rw [emit_eq_resolve, emit_eq_resolve]
  simp only [normalizeReactive, Submission.normalizeReactive_packet]
  change WitnessedPacket.mk submission.call.packet
      (EvidenceRequest.resolve who _ known (submission.evidence.normalize who
        (submission.call.candidateAfter who (fun slot => state.candidates.lookup (who, slot)))
          known)) _ = _
  rw [candidates, EvidenceRequest.resolve_normalize]

def reactiveNormalization (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).SubmissionNormalization where
  normalize := WitnessedSubmission.normalizeReactive
  idempotent := WitnessedSubmission.normalizeReactive_idempotent
  packet := WitnessedSubmission.normalizeReactive_emit runtime leaks
  submit state who known submission := by
    change submitStep _ who _ = submitStep _ who _
    dsimp only [WitnessedSubmission.normalizeReactive]
    rw [Submission.normalizeReactive_register, Submission.normalizeReactive_packet]

end Vegas.EventGraphRuntime
