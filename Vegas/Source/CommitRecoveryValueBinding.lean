/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryValueMenu
import Vegas.Source.CommitRecoveryErasure

/-! # Genuine payload readout of ordinary recovery source coordinates -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The ordinary domain subtype transports along erasure of the same full
information while retaining its literal raw choice. -/
def commitRecoveryErasedValueChoice (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    setup.CommitRecoveryValueChoice who info ≃
      setup.CommitRecoveryValueChoice who (setup.commitRecoveryErasedInformation who info) where
  toFun choice := ⟨setup.commitRecoveryErasedChoice who info choice.val, choice.property⟩
  invFun choice := ⟨(setup.commitRecoveryErasedChoice who info).symm choice.val, choice.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {Γ : SourceCtx Player L} {O : Finset VarId} {owner : Player} {name : VarId}
  {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
  {guard : SourceGuard L Γ owner name payload}
  {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
  {lift : SourceProgram.ProtocolState (.commit name owner fresh guard next) →
    SourceProgram.ProtocolState setup.program}

/-- Every genuine payload is an ordinary choice at its original complete
source information. No failure flag is folded into this embedding. -/
def commitRecoveryBindingValueAtom
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard next) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (config : Config Player L Γ)
    (atPoint : current.point = lift (.inl config)) (survives : owner ∉ current.excluded) :
    L.Val payload ↪
      setup.CommitRecoveryValueChoice owner (setup.commitRecoveryModel.infoOf owner trace) where
  toFun value :=
    ⟨setup.commitRecoveryBindingAtom origin current trace config atPoint survives (.inl value), by
      intro move selected
      have equal : CommitRecoveryMove.bindingAtom owner name payload (.inl value) = move :=
        Option.some.inj selected
      subst move
      exact ⟨rfl, fun impossible => by cases impossible⟩⟩
  inj' first second same := by
    have equal := congrArg Subtype.val same
    exact Sum.inl.inj
      ((setup.commitRecoveryBindingAtom origin current trace config atPoint survives).injective
        equal)

/-- The genuine ordinary menu contains exactly the payload values. The two
failure atoms of the full source menu are excluded by the domain predicate. -/
theorem commitRecoveryBindingValueAtom_surjective
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard next) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (config : Config Player L Γ)
    (atPoint : current.point = lift (.inl config)) (survives : owner ∉ current.excluded) :
    Function.Surjective
      (setup.commitRecoveryBindingValueAtom origin current trace config atPoint survives) := by
  intro choice
  obtain ⟨atom, same⟩ := setup.commitRecoveryBindingAtom_surjective origin current trace config
    atPoint survives choice.val
  cases atom with
  | inl value => exact ⟨value, Subtype.ext same⟩
  | inr omitted =>
      have selected : choice.val.val =
          some (CommitRecoveryMove.bindingAtom owner name payload (.inr omitted)) :=
        (congrArg Subtype.val same).symm
      exact ((choice.property _ selected).2 rfl).elim

/-- A genuine original binding query has a payload-valued domain coordinate. -/
def commitRecoveryBindingValueEquiv
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard next) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (config : Config Player L Γ)
    (atPoint : current.point = lift (.inl config)) (survives : owner ∉ current.excluded) :
    L.Val payload ≃
      setup.CommitRecoveryValueChoice owner (setup.commitRecoveryModel.infoOf owner trace) :=
  Equiv.ofBijective
    (setup.commitRecoveryBindingValueAtom origin current trace config atPoint survives)
    ⟨(setup.commitRecoveryBindingValueAtom origin current trace config atPoint survives).injective,
      setup.commitRecoveryBindingValueAtom_surjective origin current trace config atPoint survives⟩

/-- The same genuine payload coordinate is read at its erased sampling label.
The label need not itself be an original played information state. -/
def commitRecoveryErasedBindingValueEquiv
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard next) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (config : Config Player L Γ)
    (atPoint : current.point = lift (.inl config)) (survives : owner ∉ current.excluded) :
    L.Val payload ≃ setup.CommitRecoveryValueChoice owner (setup.commitRecoveryErasedInformation
      owner (setup.commitRecoveryModel.infoOf owner trace)) :=
  (setup.commitRecoveryBindingValueEquiv origin current trace config atPoint survives).trans
    (setup.commitRecoveryErasedValueChoice owner
      (setup.commitRecoveryModel.infoOf owner trace))

/-- Decoding an ordinary erased coordinate and encoding the payload gives
exactly its original domain value law, with no conditioning on source failure. -/
theorem commitRecoveryErasedBindingValueEquiv_map
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard next) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (config : Config Player L Γ)
    (atPoint : current.point = lift (.inl config)) (survives : owner ∉ current.excluded)
    (values : PMF (setup.CommitRecoveryValueChoice owner (setup.commitRecoveryErasedInformation
      owner (setup.commitRecoveryModel.infoOf owner trace)))) :
    (values.map (setup.commitRecoveryErasedBindingValueEquiv
      origin current trace config atPoint survives).symm).map
        (setup.commitRecoveryErasedBindingValueEquiv
          origin current trace config atPoint survives) = values := by
  rw [PMF.map_comp]
  simp only [Function.comp_def, Equiv.apply_symm_apply]
  change values.map id = values
  exact PMF.map_id values

end Vegas.SourceProgram.Setup
