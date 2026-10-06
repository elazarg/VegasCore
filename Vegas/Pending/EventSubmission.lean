/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication

/-! # Submissions with private opening data

A submission supplies its hidden opening data at the same decision as its
public envelope; the envelope alone enters the network. Registration is
implemented by the contract's private preparation step, which is not a
strategic position.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Private opening data is interpreted only for an authored commitment to a
prepared-slot handle. It cannot change a meaning fixed by an earlier submission. -/
structure Submission (graph : Vegas.EventGraph Player L) where
  packet : Payload graph
  opening : Option (Raw L)


/-- Register opening data only for a fresh handle owned by the sender. Initial
handles and foreign handles cannot acquire meanings through this operation. -/
def Submission.register (submission : Submission graph) (state : State graph)
    (who : Player) : State graph :=
  match submission.packet, submission.opening with
  | .commitment _ (owner, .prepared serial), some raw =>
      if owner = who then
        { state with candidates := state.candidates.prepare who (.prepared serial) raw }
      else state
  | _, _ => state

/-- A submission affects just its authenticated candidate, fixing fresh
prepared slots to their supplied value and all other fresh slots to failure. -/
def Submission.candidateAfter (submission : Submission graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (query : CandidateSlot graph) : CommitmentCandidate (Raw L) :=
  match submission.packet with
  | .commitment _ (owner, slot) =>
      if owner = who ∧ query = slot then
        match candidates query with
        | .fresh => match slot, submission.opening with
          | .prepared _, some raw => .openable raw
          | _, _ => .unopenable
        | fixed => fixed
      else candidates query
  | _ => candidates query

theorem Submission.candidateAfter_eq (submission : Submission graph) (who : Player)
    (state : State graph) (query : CandidateSlot graph) :
    (submitStep (submission.register state who) who submission.packet).candidates.lookup
        (who, query) =
      submission.candidateAfter who (fun slot => state.candidates.lookup (who, slot)) query := by
  rcases submission with ⟨packet, opening⟩
  cases packet with
  | commitment event handle =>
      rcases handle with ⟨owner, slot⟩
      by_cases owned : owner = who
      · subst owner
        by_cases same : query = slot
        · subst query
          cases meaning : state.candidates.lookup (who, slot) <;>
            cases slot <;> cases opening <;>
              simp_all [Submission.register, submitStep, Submission.candidateAfter,
                CommitmentCandidates.prepare, CommitmentCandidates.freeze,
                CommitmentCandidates.lookup]
        · cases meaning : state.candidates.lookup (who, slot) <;>
            cases slot <;> cases opening <;>
              simp_all [Submission.register, submitStep, Submission.candidateAfter,
                CommitmentCandidates.prepare, CommitmentCandidates.freeze,
                CommitmentCandidates.lookup]
      · cases slot <;> cases opening <;>
          simp [Submission.register, submitStep, Submission.candidateAfter, owned]
  | opening event handle raw | malformed raw => rfl

/-- Lowering describes the implementation of registration, not strategic
intermediate positions or a program supplied by the player. -/
def Submission.registrationCommand (submission : Submission graph) (who : Player) :
    Option (PrivateCommand graph) :=
  match submission.packet, submission.opening with
  | .commitment _ (owner, .prepared serial), some raw =>
      if owner = who then some (.prepare serial raw) else none
  | _, _ => none

theorem Submission.register_eq (submission : Submission graph) (who : Player)
    (state : State graph) :
    submission.register state who =
      match submission.registrationCommand who with
      | none => state
      | some command => privateStep state who command := by
  rcases submission with ⟨packet, opening⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      cases slot <;> cases opening <;>
        simp only [Submission.register, Submission.registrationCommand]
      split <;> rfl
  | opening event candidate raw | malformed raw => rfl

theorem Submission.register_facts (submission : Submission graph) (who : Player)
    (state : State graph) :
    (submission.register state who).config = state.config ∧
      (submission.register state who).publicView = state.publicView := by
  rcases submission with ⟨packet, opening⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      cases slot <;> cases opening <;>
        by_cases same : owner = who <;> simp [Submission.register, State.publicView, same]
  | opening event candidate raw | malformed raw => exact ⟨rfl, rfl⟩

theorem Submission.register_other (submission : Submission graph) (state : State graph)
    (actor observer : Player) (different : observer ≠ actor) :
    (submission.register state actor).playerView observer = state.playerView observer := by
  rw [submission.register_eq]
  cases registration : submission.registrationCommand actor with
  | none => rfl
  | some command => exact privateStep_playerView_other state actor observer different command

end Vegas.EventGraphRuntime
