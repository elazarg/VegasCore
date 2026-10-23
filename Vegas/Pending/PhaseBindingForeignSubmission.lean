/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingForeignMemory

/-! # Actual foreign submissions through all-value private memory -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- An arbitrary foreign raw submission commutes with the existing memory.
Registration and freezing affect only the authenticated sender's catalogue;
no condition on packet shape, preparation or remembered binding values is used. -/
theorem native_foreign_submission (memory : BindingShadow graph) (hidden actor : Player)
    (different : actor ≠ hidden) (state : State graph) (submission : Submission graph) :
    memory.native hidden (submitStep (submission.register state actor) actor submission.packet) =
      submitStep (submission.register (memory.native hidden state) actor) actor
        submission.packet := by
  classical
  let prepare (current : State graph) :=
    submitStep (submission.register current actor) actor submission.packet
  have configs (current : State graph) : (prepare current).config = current.config :=
    (submitStep_config _ _ _).trans ((submission.register_facts actor current).1)
  have publics (current : State graph) : (prepare current).publicView = current.publicView :=
    (submitStep_publicView _ _ _).trans ((submission.register_facts actor current).2)
  have foreign (current : State graph) (who : Player) (other : who ≠ actor)
      (slot : CandidateSlot graph) :
      (prepare current).candidates.lookup (who, slot) = current.candidates.lookup (who, slot) := by
    have views := (submitStep_playerView_other (submission.register current actor)
      actor who other submission.packet).trans (submission.register_other current actor who other)
    exact congrFun (congrArg PlayerView.candidates views) slot
  have candidates : (memory.native hidden (prepare state)).candidates =
      (prepare (memory.native hidden state)).candidates := by
    apply congrArg CommitmentCandidates.mk
    funext who slot
    by_cases acting : who = actor
    · subst who
      change (if actor = hidden then memory.candidate slot
          ((prepare state).candidates.lookup (actor, slot))
        else (prepare state).candidates.lookup (actor, slot)) = _
      simp only [different, ↓reduceIte]
      change (prepare state).candidates.lookup (actor, slot) =
        (prepare (memory.native hidden state)).candidates.lookup (actor, slot)
      calc
        _ = submission.candidateAfter actor
            (fun query => state.candidates.lookup (actor, query)) slot :=
          submission.candidateAfter_eq actor state slot
        _ = submission.candidateAfter actor
            (fun query => (memory.native hidden state).candidates.lookup (actor, query)) slot := by
          congr 1
          funext query
          simp only [native, CommitmentCandidates.lookup, different, ↓reduceIte]
        _ = _ := (submission.candidateAfter_eq actor (memory.native hidden state) slot).symm
    · change (if who = hidden then memory.candidate slot
          ((prepare state).candidates.lookup (who, slot))
        else (prepare state).candidates.lookup (who, slot)) = _
      calc
        _ = (if who = hidden then memory.candidate slot (state.candidates.lookup (who, slot))
            else state.candidates.lookup (who, slot)) := by rw [foreign state who acting slot]
        _ = (memory.native hidden state).candidates.lookup (who, slot) := rfl
        _ = _ := (foreign (memory.native hidden state) who acting slot).symm
  have config : (memory.native hidden (prepare state)).config =
      (prepare (memory.native hidden state)).config := by
    change memory.config (prepare state).config = _
    rw [configs state, configs (memory.native hidden state)]
    rfl
  have accepted : (memory.native hidden (prepare state)).accepted =
      (prepare (memory.native hidden state)).accepted :=
    (congrArg PublicView.accepted (publics state)).trans
      (congrArg PublicView.accepted (publics (memory.native hidden state))).symm
  have clock : (memory.native hidden (prepare state)).clock =
      (prepare (memory.native hidden state)).clock :=
    (congrArg PublicView.clock (publics state)).trans
      (congrArg PublicView.clock (publics (memory.native hidden state))).symm
  have activated : (memory.native hidden (prepare state)).activatedAt =
      (prepare (memory.native hidden state)).activatedAt :=
    (congrArg PublicView.activatedAt (publics state)).trans
      (congrArg PublicView.activatedAt (publics (memory.native hidden state))).symm
  have extensional (first second : State graph)
      (sameConfig : first.config = second.config)
      (sameCandidates : first.candidates = second.candidates)
      (sameAccepted : first.accepted = second.accepted)
      (sameClock : first.clock = second.clock)
      (sameActivated : first.activatedAt = second.activatedAt) : first = second := by
    cases first
    cases second
    cases sameConfig
    cases sameCandidates
    cases sameAccepted
    cases sameClock
    cases sameActivated
    rfl
  exact extensional _ _ config candidates accepted clock activated

end Vegas.EventGraphRuntime.BindingShadow
