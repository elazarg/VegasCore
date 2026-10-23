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

end Vegas
