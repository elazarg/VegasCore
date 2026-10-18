/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryInformation

/-! # Proposal readout determined by the acting owner's complete typed view -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

theorem recoveryProposal_eq_none_of_actor_none :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program),
      actor program point = none →
      ∀ joint, recoveryProposal program point joint = none
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, silent, joint => by
      cases point with
      | inl _ => rfl
      | inr point =>
          simpa only [recoveryProposal, Sum.elim_inr, Option.map_none] using
            congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
              (recoveryProposal_eq_none_of_actor_none next point silent joint)
  | _, _, .commit _ _ _ _ next, point, silent, joint => by
      cases point with
      | inl _ => cases silent
      | inr point =>
          simpa only [recoveryProposal, Sum.elim_inr, Option.map_none] using
            congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
              (recoveryProposal_eq_none_of_actor_none next point silent joint)
  | _, _, .reveal _ _ _ _ _ _ next, point, silent, joint => by
      cases point with
      | inl _ => cases silent
      | inr point =>
          simpa only [recoveryProposal, Sum.elim_inr, Option.map_none] using
            congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
              (recoveryProposal_eq_none_of_actor_none next point silent joint)

/-- No opponent's hidden cells are needed to recover an actor's proposal.
This remains true when the proposal later fails its guard or delivery. -/
theorem recoveryProposal_eq_of_actor_view (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      actor program first = some who → observe who program first = observe who program second →
      ∀ (left right : Player → Option (ProposalRecoveryMove Player L)),
      left who = right who → recoveryProposal program first left =
        recoveryProposal program second right
  | _, _, .ret _, _, _, active, _, _, _, _ => by cases active
  | _, _, .sample _ _ _ next, first, second, active, view, left, right, own => by
      cases first <;> cases second
      · cases active
      · cases active
      · cases view
      · exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
          (recoveryProposal_eq_of_actor_view who next _ _ active (Sum.inr.inj view)
            left right own)
  | _, _, .commit _ _ _ _ next, first, second, active, view, left, right, own => by
      cases first <;> cases second
      · rfl
      · cases view
      · cases view
      · exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
          (recoveryProposal_eq_of_actor_view who next _ _ active (Sum.inr.inj view)
            left right own)
  | _, _, .reveal _ owner name (payload := payload) _ source _ next,
      first, second, active, view, left, right, own => by
      cases first with
      | inl first =>
          cases second with
          | inl second =>
              have actorEq : owner = who := Option.some.inj active
              subst owner
              have observed := congrArg
                (fun current => current.1.cells name (.commitment who payload) source)
                (Sum.inl.inj view)
              have stored : first.state.get source = second.state.get source :=
                Option.some.inj (by
                  simpa only [observe, Config.view, sourceObserve_commitment, ite_true]
                    using observed)
              simp only [recoveryProposal, Sum.elim_inl, own, stored]
          | inr _ => cases view
      | inr first =>
          cases second with
          | inl _ => cases view
          | inr second =>
              exact congrArg (Option.map fun pair => (pair.1 + 1, pair.2))
                (recoveryProposal_eq_of_actor_view who next first second active
                  (Sum.inr.inj view) left right own)

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryProposalOf_eq_of_actor_view (who : Player)
    (first second : CommitRecoveryState setup.program)
    (active : ProtocolState.actor setup.program first.point = some who)
    (view : setup.commitRecoveryPrivate who (some first) =
      setup.commitRecoveryPrivate who (some second))
    (excluded : first.excluded = second.excluded)
    (generation : first.generation = second.generation)
    (left right : Player → Option (ProposalRecoveryMove Player L))
    (own : left who = right who) :
    setup.proposalRecoveryProposalOf (some first) left =
      setup.proposalRecoveryProposalOf (some second) right := by
  have core := ProtocolState.recoveryProposal_eq_of_actor_view who setup.program
    first.point second.point active (Option.some.inj view)
    (fun owner => if owner ∈ first.excluded then none else left owner)
    (fun owner => if owner ∈ second.excluded then none else right owner)
    (by rw [excluded, own])
  simp only [proposalRecoveryProposalOf, Option.bind_some, core, generation]

end Setup
end Vegas.SourceProgram
