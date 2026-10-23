/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBlockEmbedding

/-! # Exact recovery control after a typed commitment telescope -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Prepending commitments preserves the suffix's typed terminal context. -/
theorem terminalCtx_prepend (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) :
    suffix.terminalCtx = (block.prepend suffix).terminalCtx := by
  induction block with
  | nil => rfl
  | commit _ _ _ _ _ ih => exact ih suffix

/-- The existing suffix lift preserves every recovery-control component,
effective action history, typed available menu, raw step and terminal readout. -/
theorem liftPoint_recovery (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) :
    (∀ point, ProtocolState.remaining (block.prepend suffix) (block.liftPoint suffix point) =
      ProtocolState.remaining suffix point) ∧
    (∀ point, ProtocolState.actor (block.prepend suffix) (block.liftPoint suffix point) =
      ProtocolState.actor suffix point) ∧
    (∀ point, ProtocolState.atCommit (block.prepend suffix) (block.liftPoint suffix point) =
      ProtocolState.atCommit suffix point) ∧
    (∀ point, ProtocolState.commitOwners (block.prepend suffix) (block.liftPoint suffix point) =
      ProtocolState.commitOwners suffix point) ∧
    (∀ point, ProtocolState.commitEnd (block.prepend suffix) (block.liftPoint suffix point) =
      ProtocolState.commitEnd suffix point) ∧
    (∀ point, block.liftPoint suffix (ProtocolState.automaticCommitBlock suffix point) =
      ProtocolState.automaticCommitBlock (block.prepend suffix) (block.liftPoint suffix point)) ∧
    (∀ point, ProtocolState.history (block.prepend suffix) (block.liftPoint suffix point) =
      ProtocolState.history suffix point) ∧
    (∀ point past, block.liftPoint suffix (ProtocolState.withHistory suffix point past) =
      ProtocolState.withHistory (block.prepend suffix) (block.liftPoint suffix point) past) ∧
    (∀ point excluded joint,
      ProtocolState.recoveryStep (block.prepend suffix) (block.liftPoint suffix point)
          excluded joint =
        (ProtocolState.recoveryStep suffix point excluded joint).map
          (fun result => (block.liftPoint suffix result.1, result.2))) ∧
    (∀ who point, ProtocolView.recoveryAvailable who (block.prepend suffix)
      (ProtocolState.observe who (block.prepend suffix) (block.liftPoint suffix point)) =
      ProtocolView.recoveryAvailable who suffix (ProtocolState.observe who suffix point)) ∧
    (∀ point, ProtocolState.readout (block.prepend suffix) (block.liftPoint suffix point) =
      (ProtocolState.readout suffix point).map
        (cast (congrArg (State L) (block.terminalCtx_prepend suffix)))) := by
  induction block with
  | nil =>
      refine ⟨(fun _ => rfl), (fun _ => rfl), (fun _ => rfl), (fun _ => rfl),
        (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), (fun _ _ => rfl), ?_,
        (fun _ _ => rfl), ?_⟩
      · intro point excluded joint
        exact (PMF.map_id _).symm
      · intro point
        change _ = Option.map id _
        simp only [Option.map_id, id_eq]
        rfl
  | commit name owner fresh guard rest ih =>
      obtain ⟨_remaining, actor, commit, owners, endpoint, automatic, _history,
        memory, step, menus, readout⟩ := ih suffix
      refine ⟨(CommitPrefix.commit name owner fresh guard rest).liftPoint_remaining suffix,
        ?_, ?_, ?_, ?_, ?_,
        (CommitPrefix.commit name owner fresh guard rest).liftPoint_history suffix,
        ?_, ?_, ?_, ?_⟩
      · intro point
        exact actor point
      · intro point
        exact commit point
      · intro point
        exact owners point
      · intro point
        exact endpoint point
      · intro point
        exact congrArg Sum.inr (automatic point)
      · intro point past
        exact congrArg Sum.inr (memory point past)
      · intro point excluded joint
        change ((ProtocolState.recoveryStep (rest.prepend suffix)
          (rest.liftPoint suffix point) excluded joint).map
            (fun result => (Sum.inr result.1, result.2))) = _
        rw [step]
        simp only [PMF.map_comp, Function.comp_def]
        rfl
      · intro who point
        exact menus who point
      · intro point
        exact readout point

end Vegas.SourceProgram.CommitPrefix
