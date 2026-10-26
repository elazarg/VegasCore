/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledCommitHead
import Vegas.Source.CommitRecoveryNoMissInformation
import Vegas.Source.CommitRecoveryOwnedStep

/-! # Actual binding receipts determine the original source step

A missing accepted handle is an omission. A present handle with an unusable
meaning is an accepted bad binding. The source install and close execute in
the same step, including the final-slot rollback or exhausted close.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The literal accepted receipt and its current native binding meaning
produce an exact original source kernel, including immediate phase close.
No successful guard, honest choice, or delayed-close hypothesis is required. -/
theorem sourcePhase_binding_receipt_kernel
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard tail))
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard tail) lift)
    (entry : SourceProgram.Config Player L Γ) (current : CommitRecoveryState setup.program)
    (point : current.point = lift (.inl entry)) :
    let event := embedding.event ⟨0, by simp only [eventCount]; omega⟩
    let accepted := native.accepted (.inr event)
    let result := accepted.elim PublicationResult.failure
      (fun candidate => native.bindingResult candidate payload)
    let missed := accepted.isNone
    let nextConfig := if owner ∈ current.excluded then automaticCommit name owner payload entry
      else commitSuccessor name guard entry result
    let excluded := if owner ∈ current.excluded then current.excluded
      else excludeCommit current.excluded owner missed
    let joint := current.commitJoint owner name payload result missed
    ∃ monotone : current.excluded ⊆ excluded,
      ∃ legal : setup.commitRecoveryProtocol.Legal (some current) joint,
        setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩ =
          PMF.pure (some ((current.install
            (lift (.inr (ProtocolState.entry tail nextConfig)), excluded) monotone).close)) := by
  intro event accepted result missed nextConfig excluded joint
  have missingFailure : missed = true → result = .failure := by
    cases found : accepted with
    | none => simp only [result, found, Option.elim_none, implies_true]
    | some candidate =>
        simp only [missed, found, Option.isNone_some, Bool.false_eq_true, false_implies]
  obtain ⟨monotone, legal, supported⟩ := lifted_commit_successor setup.program
    (setup.initialConfig setup.initialLaw.support_nonempty.choose) guard tail lift
      origin.remaining_lift origin.actor_lift (fun point who => origin.recoveryAvailable who point)
      origin.recoveryStep_lift entry current point result missed missingFailure
  have acting : ProtocolState.actor setup.program current.point = some owner := by
    rw [point, origin.actor_lift]
    rfl
  refine ⟨monotone, legal, ?_⟩
  change (current.step joint).map some = _
  have pure : current.step joint = PMF.pure
      ((current.install (lift (.inr (ProtocolState.entry tail nextConfig)), excluded)
        monotone).close) := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro next reached
    exact setup.commitRecovery_step_unique_of_actor current owner acting joint next _ reached
      supported
  rw [pure, PMF.pure_map]

/-- The same exact source kernel lands at the actual one-slot physical
decoder. Its literal close includes final-slot rollback, rather than an
artificial post-instruction cursor that survives the close. -/
theorem sourcePhase_binding_decoder_kernel
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard tail))
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard tail) lift)
    (entry : SourceProgram.Config Player L Γ) (current : CommitRecoveryState setup.program)
    (point : current.point = lift (.inl entry)) :
    let head : SourceProgram.CommitPrefix Γ O ((name, .commitment owner payload) :: Γ)
      (insert name O) := .commit name owner fresh guard .nil
    let event := embedding.event ⟨0, by simp only [eventCount]; omega⟩
    let accepted := native.accepted (.inr event)
    let result := accepted.elim PublicationResult.failure
      (fun candidate => native.bindingResult candidate payload)
    let missed := accepted.isNone
    let joint := current.commitJoint owner name payload result missed
    let decoded := decodeCommitAttempt setup.program mode head tail embedding native entry
      current.excluded
    ∃ monotone : current.excluded ⊆ decoded.2.1,
      ∃ legal : setup.commitRecoveryProtocol.Legal (some current) joint,
        decoded.2.2.joints = [joint] ∧
        setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩ =
          PMF.pure (some ((current.install
            (lift (.inr (ProtocolState.entry tail decoded.1)), decoded.2.1) monotone).close)) := by
  intro head event accepted result missed joint decoded
  obtain ⟨monotone, legal, kernel⟩ := sourcePhase_binding_receipt_kernel setup mode fresh guard
    tail embedding native lift origin entry current point
  have configEq : decoded.1 =
      if owner ∈ current.excluded then automaticCommit name owner payload entry
      else commitSuccessor name guard entry result := by
    by_cases inactive : owner ∈ current.excluded
    · dsimp only [decoded, head, decodeCommitAttempt]
      rw [dite_eq_left inactive, ite_eq_left inactive]
    · dsimp only [decoded, head, decodeCommitAttempt]
      rw [dite_eq_right inactive, ite_eq_right inactive]
  have excludedEq : decoded.2.1 =
      if owner ∈ current.excluded then current.excluded
      else excludeCommit current.excluded owner missed := by
    by_cases inactive : owner ∈ current.excluded
    · dsimp only [decoded, head, decodeCommitAttempt]
      rw [dite_eq_left inactive, ite_eq_left inactive]
    · dsimp only [decoded, head, decodeCommitAttempt]
      rw [dite_eq_right inactive, ite_eq_right inactive]
  refine ⟨decoded.2.2.excluded_subset, legal, ?_, ?_⟩
  · exact decodeCommitAttempt_head_joints setup.program mode fresh guard tail embedding native
      entry current
  · simpa only [configEq, excludedEq] using kernel

end Vegas
