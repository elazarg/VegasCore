/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixAdmission
import Vegas.Compile.ProtocolViewSuffix

/-! # Original intended binding actions at a partial compiled commitment prefix -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem decodeCommitPrefix_binding
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {name : VarId} {who : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ who name payload)
    (next : SourceProgram Player L ((name, .commitment who payload) :: Δ) (insert name P))
    (block : CommitPrefix Γ O Δ P) :
    ∀ (selected : Fin (eventCount (block.prepend (.commit name who fresh guard next)))),
      selected.val = block.length →
      ∀ (binding : outputLayout (block.prepend (.commit name who fresh guard next)) selected =
          .binding who payload)
        (action : EventField.Action
          (outputLayout (block.prepend (.commit name who fresh guard next)) selected)),
        decodeEventAction (block.prepend (.commit name who fresh guard next)) selected action =
          some (.commit who name payload (cast (congrArg EventField.Action binding) action)) := by
  induction block with
  | nil =>
      intro selected atEnd binding action
      refine Fin.cases ?_ ?_ selected atEnd binding action
      · intro _atEnd _binding action
        rfl
      · intro tail impossible
        change tail.val + 1 = 0 at impossible
        omega
  | commit prior owner freshBefore guardBefore rest ih =>
      intro selected
      refine Fin.cases ?_ ?_ selected
      · intro impossible
        change 0 = rest.length + 1 at impossible
        omega
      · intro tail atEnd binding action
        apply ih fresh guard next tail _ binding action
        change tail.val + 1 = rest.length + 1 at atEnd
        omega

/-- A sampled original intended source action fixes the actual typed graph
binding to a guard-admitted success. The partial foreign fill is used only as
an observation reference; its earlier owned choices supply satisfiability. -/
theorem compiledCommitPrefix_action_admitted
    {wholeΓ Γ Δ : SourceCtx Player L} {wholeO O P : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    {name : VarId} {who : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ who name payload)
    (next : SourceProgram Player L ((name, .commitment who payload) :: Δ) (insert name P))
    (block : CommitPrefix Γ O Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend (.commit name who fresh guard next)))
    (refs : ContextRefs (graphLayout whole) Γ)
    (lift : ProtocolState (block.prepend (.commit name who fresh guard next)) →
      ProtocolState whole)
    (origin : ProtocolSuffix whole (block.prepend (.commit name who fresh guard next)) lift)
    (views : ProtocolViewSuffix whole (block.prepend (.commit name who fresh guard next))
      refs embedding lift)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (savedIntended : ProtocolState.Intended whole
      (lift (ProtocolState.entry (block.prepend (.commit name who fresh guard next)) entry)))
    (ownAdmitted : (fillCommitPrefix whole block (.commit name who fresh guard next)
      embedding store entry).IntendedFor who P)
    (selected : Fin (eventCount (block.prepend (.commit name who fresh guard next))))
    (atEnd : selected.val = block.length)
    (binding : outputLayout whole (embedding.event selected) = .binding who payload)
    (action : EventField.Action (outputLayout whole (embedding.event selected)))
    (sourceAction : OwnAction Player L)
    (decoded : decodeEventAction whole (embedding.event selected) action = some sourceAction)
    (offered : sourceAction ∈ ProtocolView.intendedAvailable who whole
      (ProtocolState.observe who whole
        (lift (block.liftPoint (.commit name who fresh guard next)
          (ProtocolState.entry (.commit name who fresh guard next)
            (fillCommitPrefix whole block (.commit name who fresh guard next)
              embedding store entry)))))) :
    let filled := fillCommitPrefix whole block (.commit name who fresh guard next)
      embedding store entry
    ∃ value, cast (congrArg EventField.Action binding) action = .success value ∧
      guard.predicts (sourceObserve who filled.state) value = true ∧
      (commitSuccessor name guard filled (.success value)).IntendedFor who (insert name P) := by
  have localBinding := (embedding.layout_eq selected).symm.trans binding
  have localDecoded := decodeCommitPrefix_binding fresh guard next block selected atEnd
    localBinding (cast (congrArg EventField.Action (embedding.layout_eq selected)) action)
  have actualDecoded : decodeEventAction whole (embedding.event selected) action =
      some (.commit who name payload (cast (congrArg EventField.Action binding) action)) := by
    simpa only [cast_cast] using (views.actionEq selected action).trans localDecoded
  have identified := Option.some.inj (decoded.symm.trans actualDecoded)
  rw [identified, origin.intendedAvailable who] at offered
  obtain ⟨value, equal, accepted, nextAdmitted⟩ := fillCommitPrefix_intended_commit_choice whole
    fresh guard next block embedding store entry (origin.intended_reflect _ savedIntended)
      ownAdmitted _ offered
  have result : cast (congrArg EventField.Action binding) action = .success value := by
    simpa only [OwnAction.commit.injEq, heq_eq_eq, true_and] using equal
  exact ⟨value, result, accepted, nextAdmitted⟩

end Vegas
