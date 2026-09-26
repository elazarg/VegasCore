/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Interaction.ReactiveResponseNormalization

/-! # Semantic normal forms of event submissions

Opening material has an effect only when a submission fixes a fresh owned
prepared handle. Other opening material is a private representation artifact.
Normalization preserves the entire public packet, including malformed contents,
and changes no application or network effect. It uses only the sender's view.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def openingEffective (who : Player) (view : ReactivePlayerView graph) : Payload graph → Prop
  | .commitment _ (owner, .prepared serial) =>
      owner = who ∧ view.candidates (.prepared serial) = .fresh
  | _ => False

open Classical in
def Submission.normalizeReactive (who : Player) (view : ReactivePlayerView graph)
    (submission : Submission graph) : Submission graph :=
  ⟨submission.packet, if openingEffective who view submission.packet then submission.opening
    else none⟩

theorem Submission.normalizeReactive_packet (who : Player) (view : ReactivePlayerView graph)
    (submission : Submission graph) :
    (submission.normalizeReactive who view).packet = submission.packet := rfl

theorem Submission.normalizeReactive_idempotent (who : Player) (view : ReactivePlayerView graph)
    (submission : Submission graph) :
    (submission.normalizeReactive who view).normalizeReactive who view =
      submission.normalizeReactive who view := by
  classical
  simp only [normalizeReactive]
  split <;> rfl

/-- No metadata is removed when it can fix a commitment meaning. -/
theorem Submission.normalizeReactive_effective (who : Player) (view : ReactivePlayerView graph)
    (submission : Submission graph) (effective : openingEffective who view submission.packet) :
    submission.normalizeReactive who view = submission := by
  simp only [normalizeReactive, effective, ↓reduceIte]

theorem Submission.normalizeReactive_none (who : Player) (view : ReactivePlayerView graph)
    (packet : Payload graph) :
    (⟨packet, none⟩ : Submission graph).normalizeReactive who view = ⟨packet, none⟩ := by
  simp only [normalizeReactive, ite_self]

variable [DecidableEq Player]

theorem Submission.normalizeReactive_candidateAfter (who : Player)
    (view : ReactivePlayerView graph) (submission : Submission graph)
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
  | opening | withhold | malformed => rfl

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
            · simp [normalizeReactive, openingEffective, reactiveApplication, fresh]
            · cases material with
              | none => simp [normalizeReactive, openingEffective, reactiveApplication, fresh]
              | some raw =>
                  simp [normalizeReactive, openingEffective, reactiveApplication, fresh, register,
                    state.candidates.prepare_eq_self_of_not_fresh who (.prepared serial) raw fresh]
          · cases material <;> simp [normalizeReactive, openingEffective, register, same]
  | opening event candidate raw | withhold event | malformed raw =>
      cases material <;> simp [normalizeReactive, openingEffective, register]

open Classical in
/-- Remove requests that issue no certificate, using only the sender's local
candidate meanings after its call and the evidence in known packets. -/
def EvidenceRequest.normalize (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) :
    EvidenceRequest graph → EvidenceRequest graph
  | .none => .none
  | .owned fact =>
      if fact.handle.1 = who ∧ candidates fact.handle.2 = .openable fact.raw
      then .owned fact else .none
  | .forward id =>
      if ((known.find? fun message => message.id = id).bind
        fun message => message.payload.evidence).isSome then .forward id else .none

theorem EvidenceRequest.normalize_forward (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (id : MessageId Player)
    (available : ((known.find? fun message => message.id = id).bind
      fun message => message.payload.evidence).isSome = true) :
    (EvidenceRequest.forward (graph := graph) id).normalize who candidates known =
      .forward id := by
  simp [normalize, available]

theorem EvidenceRequest.normalize_unknown (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (id : MessageId Player)
    (absent : ¬ ∃ message ∈ known, message.id = id) :
    (EvidenceRequest.forward (graph := graph) id).normalize who candidates known = .none := by
  have missing : known.find? (fun message => message.id = id) = Option.none := by
    apply List.find?_eq_none.mpr
    intro message member found
    exact absent ⟨message, member, of_decide_eq_true found⟩
  simp [normalize, missing]

theorem EvidenceRequest.normalize_empty_forward (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (id : MessageId Player)
    (empty : ((known.find? fun message => message.id = id).bind
      fun message => message.payload.evidence) = Option.none) :
    (EvidenceRequest.forward (graph := graph) id).normalize who candidates known = .none := by
  simp [normalize, empty]

theorem EvidenceRequest.normalize_idempotent (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (request : EvidenceRequest graph) :
    (request.normalize who candidates known).normalize who candidates known =
      request.normalize who candidates known := by
  classical
  cases request with
  | none => rfl
  | owned fact => by_cases available : fact.handle.1 = who ∧
        candidates fact.handle.2 = .openable fact.raw <;> simp [normalize, available]
  | forward id => by_cases available : ((known.find? fun message => message.id = id).bind
        fun message => message.payload.evidence).isSome = true <;> simp [normalize, available]

def WitnessedSubmission.normalizeReactive (who : Player) (view : ReactivePlayerView graph)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) : WitnessedSubmission graph :=
  ⟨submission.call.normalizeReactive who view,
    submission.evidence.normalize who (submission.call.candidateAfter who view.candidates) known⟩

theorem WitnessedSubmission.normalizeReactive_idempotent
    (who : Player) (view : ReactivePlayerView graph)
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
  classical
  rcases submission with ⟨call, request⟩
  cases request with
  | none => rfl
  | owned fact =>
      by_cases owner : fact.handle.1 = who
      · have handle : fact.handle = (who, fact.handle.2) := by
          rw [← owner]
        have localMeaning :
            (submitStep (call.register state who) who call.packet).candidates.lookup fact.handle =
              call.candidateAfter who (fun slot => state.candidates.lookup (who, slot))
                fact.handle.2 := by
          conv_lhs => rw [handle]
          exact call.candidateAfter_eq who state fact.handle.2
        by_cases available : call.candidateAfter who
            (fun slot => state.candidates.lookup (who, slot)) fact.handle.2 = .openable fact.raw
        all_goals simp [normalizeReactive, EvidenceRequest.normalize, reactiveApplication,
          emit, Submission.normalizeReactive_packet, CommitmentCandidates.verify,
          owner, localMeaning, available]
      · simp [normalizeReactive, EvidenceRequest.normalize, emit, owner,
          Submission.normalizeReactive_packet]
  | forward id =>
      cases evidence : (known.find? fun message => message.id = id).bind
          (fun message => message.payload.evidence) <;>
        simp [normalizeReactive, EvidenceRequest.normalize, evidence, emit,
          Submission.normalizeReactive_packet]

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
