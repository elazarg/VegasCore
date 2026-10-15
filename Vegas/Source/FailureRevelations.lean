/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Semantics

/-! # Failed immutable bindings cannot acquire successful publications -/

namespace Vegas.SourceProgram

variable {Player : Type} {L : IExpr} {Γ : SourceCtx Player L}

/-- Every failed binding remains failed in its published-result interpretation. -/
def Revelations.PreservesFailures (revelations : Revelations Γ) (state : State L Γ) : Prop :=
  ∀ owner payload name (source : HasVar Γ name (.commitment owner payload)),
    state.get source = .failure → (revelations source).result state = .failure

theorem Revelations.initial_preservesFailures (state : State L Γ) :
    Revelations.PreservesFailures (Revelations.initial Γ) state := by
  intro owner payload name source _failed
  rfl

/-- New cells and commitments cannot publish an earlier failed binding. -/
theorem Revelations.PreservesFailures.weaken {revelations : Revelations Γ} {state : State L Γ}
    (valid : Revelations.PreservesFailures revelations state)
    {name : VarId} {cell : CellTy Player L}
    (head : CellVal L cell) :
    Revelations.PreservesFailures (revelations.weaken (name := name) (cell := cell))
      (Env.cons head state) := by
  intro owner payload readName source failed
  cases source with
  | here => rfl
  | there previous =>
      simpa only [Revelations.weaken_there, Revelation.result_weaken] using
        valid owner payload readName previous failed

/-- Publishing any legal source binding preserves failure propagation,
independently of which guard obligations will subsequently be checked. -/
theorem Revelations.PreservesFailures.reveal {revelations : Revelations Γ} {state : State L Γ}
    (valid : Revelations.PreservesFailures revelations state) (unique : (Γ.map Prod.fst).Nodup)
    {name published : VarId} {owner : Player} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload))
    (publication : PublicationResult (L.Val payload))
    (failedSource : state.get source = .failure → publication = .failure) :
    Revelations.PreservesFailures (revelations.reveal (published := published) source)
      (Env.cons (Val := CellVal (Player := Player) L) (x := published)
        (τ := .publication payload) publication state) := by
  intro readOwner readPayload readName selected failed
  cases selected with
  | there previous =>
      by_cases same : readName = name
      · subst readName
        have cellEq := HasVar.type_unique unique previous source
        cases cellEq
        cases HasVar.eq_of_nodup unique previous source
        simpa only [Revelations.reveal_source, Revelation.result, Env.get, Env.cons] using
          failedSource failed
      · simpa only [Revelations.reveal_of_ne revelations source previous same,
          Revelation.result_weaken] using
          valid readOwner readPayload readName previous failed

/-- Source guard rejection also preserves immutable failed binding meanings. -/
theorem Revelations.PreservesFailures.revealSuccessor [DecidableEq Player]
    (config : Config Player L Γ)
    (valid : Revelations.PreservesFailures config.revelations config.state)
    (unique : (Γ.map Prod.fst).Nodup)
    {name published : VarId} {owner : Player} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload)) (disclose : Bool) :
    Revelations.PreservesFailures (revealSuccessor published source config disclose).revelations
      (revealSuccessor published source config disclose).state := by
  unfold SourceProgram.revealSuccessor
  dsimp only
  exact valid.reveal (published := published) unique source _ (fun failed => by
    simp only [failed, ite_self])

end Vegas.SourceProgram
