/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixReadout
import Vegas.Source.ProtocolBehavioralPolicy

/-! # The structural policy read by an interior commitment word -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Dropping the consumed constructors restricts the original policy at the
same lifted protocol observation, without a policy agreement premise. -/
theorem tailProfile_protocolAction (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (who : Player) (point : ProtocolState suffix) :
    (block.tailProfile suffix profile who).protocolAction suffix
        (ProtocolState.observe who suffix point) =
      (profile who).protocolAction (block.prepend suffix)
        (ProtocolState.observe who (block.prepend suffix) (block.liftPoint suffix point)) := by
  induction block with
  | nil => rfl
  | commit name owner fresh guard rest ih => exact ih suffix (afterCommit profile) point

/-- The next typed-result kernel is the original structural policy at the
actual interior source point, with its exact variable name and payload. -/
theorem binding_kernel_protocolAction
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (block : CommitPrefix Γ O Δ P)
    (profile : BehavioralProfile (block.prepend (.commit name owner fresh guard next)))
    (config : Config Player L Δ) :
    (commitKernel (block.tailProfile (.commit name owner fresh guard next) profile)
      (config.view owner)).map (fun result => some (OwnAction.commit owner name payload result)) =
      (profile owner).protocolAction (block.prepend (.commit name owner fresh guard next))
        (ProtocolState.observe owner (block.prepend (.commit name owner fresh guard next))
          (block.liftPoint (.commit name owner fresh guard next)
            (ProtocolState.entry (.commit name owner fresh guard next) config))) := by
  have law := block.tailProfile_protocolAction (.commit name owner fresh guard next) profile
    owner (ProtocolState.entry (.commit name owner fresh guard next) config)
  simpa only [BehavioralPolicy.protocolAction, ProtocolState.observe, ProtocolState.entry,
    Sum.elim_inl, dite_eq_left (Eq.refl owner), dite_true, commitKernel] using law

end Vegas.SourceProgram.CommitPrefix
