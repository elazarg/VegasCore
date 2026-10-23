/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerPrior
import Vegas.Game.OnePacketOwnerGuard

/-! # The owner swap keeps the prior's support at a site

Every history of a decision site of `who` starts from a setup draw whose inputs
the site's view stores at `who`'s private inputs (`Vegas.siteDraw`), and in a
well-formed setup no such input is a failure (`Vegas.eventInputs_not_failure`).
So the owner swap between two sites sends the draw of a history of the first
site to its splice with a draw of the second, which an initial law with
independent hidden cells supports (`Vegas.ownerSwap_priorClosed`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- **Private initial inputs are not failures** in a well-formed setup: a
private input never fails, and an initial commitment holds a success. -/
theorem eventInputs_not_failure (wellFormed : setup.WellFormed) {who : Player}
    {draw : State L setup.context} (member : draw ∈ setup.initialLaw.support)
    {name : VarId} {kind : CellTy Player L} (source : HasVar setup.context name kind)
    (hidden : kind.hiddenOwner? = some who) :
    ¬ ((graph setup).layout (.inl (inputId source))).IsFailure
      (setup.eventInputs draw (inputId source)) := by
  have layoutEq : (graph setup).layout (.inl (inputId source)) = cellField kind :=
    inputLayout_inputId source
  have value := encodeInputs_get draw source
  change cast _ (setup.eventInputs draw (inputId source)) = _ at value
  have general : ∀ (field : EventGraph.EventField Player L) (fieldEq : field = cellField kind)
      (stored : field.Value),
      cast (congrArg EventGraph.EventField.Value fieldEq) stored = cellValue (draw.get source) →
        ¬ field.IsFailure stored := by
    rintro _ rfl stored storedEq
    rw [cast_eq] at storedEq
    subst storedEq
    cases kind with
    | publicData | publication => simp [CellTy.hiddenOwner?] at hidden
    | privateInput => exact id
    | commitment owner payload =>
        obtain ⟨success, successEq⟩ := wellFormed.initialValues draw member source
        change ¬ cellValue (draw.get source) = PublicationResult.failure
        rw [successEq]
        simp [cellValue]
  exact general _ layoutEq _ value

variable [Fintype Player] {leaks : MessageNetwork.ObservationRule Player
    (WitnessedPacket (graph setup))} {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

omit [Fintype Player] in
/-- A private input of `who` is the input of a cell `who` hides. -/
private theorem hidden_of_privateTo {who : Player} {input : (graph setup).InputId}
    (privateTo : PrivateTo who (setup := setup) (.inl input)) :
    ∃ (name : VarId) (kind : CellTy Player L) (source : HasVar setup.context name kind),
      inputId source = input ∧ kind.hiddenOwner? = some who := by
  have positions : ∀ (Γ : SourceCtx Player L) (position : Fin Γ.length),
      ∃ (name : VarId) (kind : CellTy Player L) (source : HasVar Γ name kind),
        inputId source = position := by
    intro Γ
    induction Γ with
    | nil => exact fun position => Fin.elim0 position
    | cons head Γ ih =>
        intro position
        cases position using Fin.cases with
        | zero => exact ⟨head.1, head.2, .here, rfl⟩
        | succ position =>
            obtain ⟨other, otherKind, source, rfl⟩ := ih position
            exact ⟨other, otherKind, .there source, rfl⟩
  obtain ⟨name, kind, source, rfl⟩ := positions setup.context input
  exact ⟨name, kind, source, rfl, (privateTo_inl_iff who source).mp privateTo⟩

/-- **The draw of a site history.** Every history of a decision site of `who`
ends at a control whose inputs are those of a supported setup draw, and the
site's view stores that draw's inputs at `who`'s private inputs. -/
theorem siteDraw {who : Player}
    {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (decision : site.1 = some (past, view))
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1) :
    ∃ (control : (application setup leaks).Control) (draw : State L setup.context),
      history.1.state = some control ∧ draw ∈ setup.initialLaw.support ∧
      control.execution.application.config.inputs = setup.eventInputs draw ∧
      ∀ input, PrivateTo who (setup := setup) (.inl input) →
        view.application.observation.store (.inl input) = some (setup.eventInputs draw input) := by
  obtain ⟨control, stateEq, viewEq⟩ := state_of_decision history decision
  obtain ⟨draw, member, inputsEq, -⟩ :=
    initialSlots_of_trace history.1.trace control stateEq
  refine ⟨control, draw, stateEq, member, inputsEq, fun input privateTo => ?_⟩
  rw [← viewEq]
  change (graph setup).playerStore who control.execution.application.config.store (.inl input) =
    _
  rw [EventGraph.playerStore_of_visible _ who _ _ privateTo.1]
  change some (control.execution.application.config.inputs input) = _
  rw [inputsEq]

/-- **The owner swap keeps the prior's support at the first site.** With
independent hidden initial cells, the owner swap between two sites of `who`
sends the inputs of the draw of every history of the first site to the inputs
of a supported draw. -/
theorem ownerSwap_priorClosed (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent) {who : Player}
    {site₁ site₂ : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past₁ past₂ : List (application setup leaks).PlayerEntry}
    {view₁ view₂ : (application setup leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂)) :
    ∀ initial ∈ setup.initialLaw.support,
      (∃ history : (onePacketInformation setup leaks bounds horizon
          scheduler).InformationHistory who site₁.1, ∃ control : (application setup leaks).Control,
        history.1.state = some control ∧
          control.execution.application.config.inputs = setup.eventInputs initial) →
      ∃ other ∈ setup.initialLaw.support, setup.eventInputs other =
        (ownerSwap who view₁.application view₂.application).inputs (setup.eventInputs initial) := by
  rintro initial member ⟨history, control, stateEq, inputsEq⟩
  obtain ⟨control₁, draw₁, stateEq₁, -, inputsEq₁, firstStore⟩ := siteDraw firstSite history
  rw [stateEq] at stateEq₁
  cases Option.some.inj stateEq₁
  obtain ⟨history₂, -⟩ := site₂.2
  obtain ⟨-, draw₂, -, drawMember₂, -, secondStore⟩ := siteDraw secondSite history₂
  have firstStore' : ∀ input, PrivateTo who (setup := setup) (.inl input) →
      view₁.application.observation.store (.inl input) =
        some (setup.eventInputs initial input) := fun input privateTo => by
    rw [firstStore input privateTo, ← inputsEq₁, inputsEq]
  have ok : ∀ draw ∈ setup.initialLaw.support, ∀ input,
      PrivateTo who (setup := setup) (.inl input) →
        ¬ ((graph setup).layout (.inl input)).IsFailure (setup.eventInputs draw input) := by
    intro draw drawMember input privateTo
    obtain ⟨name, kind, source, rfl, hidden⟩ := hidden_of_privateTo privateTo
    exact eventInputs_not_failure wellFormed drawMember source hidden
  refine ⟨splice who draw₂ initial, setup.splice_mem_support independent who drawMember₂ member,
    ?_⟩
  exact (ownerSwap_inputs_splice who initial draw₂ firstStore' secondStore
    (ok initial member) (ok draw₂ drawMember₂)).symm

end Vegas
