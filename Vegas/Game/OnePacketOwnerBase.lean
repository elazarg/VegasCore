/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerPriorSite
import Vegas.Game.OnePacketOwnerBounds

/-! # Owner-swap input encodings and restricted guards

Setup draws are determined by their encoded inputs, and hidden-cell agreement
is equivalent to equality at inputs private to the player. Actual histories
at two sites provide the values needed to keep the owner swap within bounds.

The image of a history under a hidden swap does not depend on its allowed
input set (`Vegas.mapTrace_allowed_congr`). A guard restricts to any smaller
set containing the actual inputs (`Vegas.swapGuardState_inter`). These facts
let prior scaling on a site's input fiber apply to the same mapped trace.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **The image of a history does not depend on the allowed inputs.** -/
theorem mapTrace_allowed_congr (swap : HiddenSwap (graph setup))
    {first second : Set (graph setup).Inputs}
    (firstClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ first →
      state.swap swap ∈ (initialLaw setup).support)
    (secondClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ second →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
      (firstGuard : SwapGuardState setup swap first state)
      (secondGuard : SwapGuardState setup swap second state),
    (onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap firstClosed
        bounded).mapTrace trace firstGuard =
      (onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap secondClosed
        bounded).mapTrace trace secondGuard
  | _, .start, _, _ => rfl
  | _, .extend prior joint legal reached, firstGuard, secondGuard => by
      rw [StateSymmetry.mapTrace_extend, StateSymmetry.mapTrace_extend,
        mapTrace_allowed_congr swap firstClosed secondClosed bounded prior]
      rfl

omit [Fintype Player] in
/-- **A guard holds for a smaller allowed set** containing the current inputs. -/
theorem swapGuardState_inter (swap : HiddenSwap (graph setup))
    {allowed restricted : Set (graph setup).Inputs}
    {state : (application setup leaks).ProtocolState}
    (guarded : SwapGuardState setup swap allowed state)
    (inside : ∀ control : (application setup leaks).Control, state = some control →
      control.execution.application.config.inputs ∈ restricted) :
    SwapGuardState setup swap (allowed ∩ restricted) state := by
  cases state with
  | none => trivial
  | some control =>
      obtain ⟨inputs, compatible, reveals, requests, expired⟩ := guarded
      exact ⟨⟨inputs, inside control rfl⟩, compatible, reveals, requests, expired⟩

omit [Fintype Player] in
/-- Setup draws are determined by their encoded inputs. -/
theorem eventInputs_injective :
    Function.Injective (setup.eventInputs (Player := Player) (L := L)) := by
  intro first second same
  funext name kind source
  have firstValue := encodeInputs_get first source
  have secondValue := encodeInputs_get second source
  change cast _ (setup.eventInputs first (inputId source)) = _ at firstValue
  change cast _ (setup.eventInputs second (inputId source)) = _ at secondValue
  rw [same, secondValue] at firstValue
  change cellValue (second name kind source) = cellValue (first name kind source) at firstValue
  cases kind <;> exact firstValue.symm

omit [Fintype Player] in
/-- The mass of the initial state of a draw is the mass of the draw. -/
theorem initialLaw_initial (draw : State L setup.context) :
    initialLaw setup (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs draw)) =
      setup.initialLaw draw := by
  have injective : Function.Injective fun draw : State L setup.context =>
      EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs draw) := by
    intro first second same
    apply eventInputs_injective
    exact congrArg (fun state : EventGraphRuntime.State (graph setup) => state.config.inputs)
      same
  exact GameTheory.Math.Probability.pmf_map_apply_of_injective setup.initialLaw injective draw

omit [Fintype Player] in
/-- A state of the initial law's support is the initial state of its inputs. -/
theorem eq_initial_of_mem_support {state : EventGraphRuntime.State (graph setup)}
    (member : state ∈ (initialLaw setup).support) :
    ∃ draw ∈ setup.initialLaw.support,
      state = EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs draw) := by
  rw [initialLaw, serviceInitialLaw, PMF.support_map] at member
  obtain ⟨draw, drawMember, rfl⟩ := member
  exact ⟨draw, drawMember, rfl⟩


omit [Fintype Player] in
private theorem hidden_of_privateTo' {who : Player} {input : (graph setup).InputId}
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

omit [Fintype Player] in
/-- Two draws whose inputs agree at every input private to `who` agree on the
cells `who` hides, and conversely. -/
theorem hiddenAgree_iff_inputs {who : Player} {first second : State L setup.context} :
    HiddenAgree who first second ↔
      ∀ input, PrivateTo who (setup := setup) (.inl input) →
        setup.eventInputs first input = setup.eventInputs second input := by
  constructor
  · intro agree input privateTo
    obtain ⟨name, kind, source, rfl, hidden⟩ := hidden_of_privateTo' privateTo
    have firstValue := encodeInputs_get first source
    have secondValue := encodeInputs_get second source
    change cast _ (setup.eventInputs first (inputId source)) = _ at firstValue
    change cast _ (setup.eventInputs second (inputId source)) = _ at secondValue
    apply (cast_inj (congrArg EventGraph.EventField.Value (inputLayout_inputId source))).mp
    rw [firstValue, secondValue]
    change cellValue (first name kind source) = cellValue (second name kind source)
    rw [agree name kind source hidden]
  · intro same name kind source hidden
    have equal := same (inputId source) ((privateTo_inl_iff who source).mpr hidden)
    have firstValue := encodeInputs_get first source
    have secondValue := encodeInputs_get second source
    change cast _ (setup.eventInputs first (inputId source)) = _ at firstValue
    change cast _ (setup.eventInputs second (inputId source)) = _ at secondValue
    rw [equal, secondValue] at firstValue
    change cellValue (second name kind source) = cellValue (first name kind source) at firstValue
    cases kind <;> exact firstValue.symm

/-- **The owner swap between two sites keeps the bounds.** -/
theorem ownerSwap_bounded_sites (covers : bounds.CoversInputValues) {who : Player}
    {site₁ site₂ : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past₁ past₂ : List (application setup leaks).PlayerEntry}
    {view₁ view₂ : (application setup leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂)) :
    ∀ handle raw, raw ∈ bounds.values →
      (ownerSwap who view₁.application view₂.application).raw handle raw ∈ bounds.values := by
  obtain ⟨history₁, -⟩ := site₁.2
  obtain ⟨history₂, -⟩ := site₂.2
  obtain ⟨control₁, stateEq₁, viewEq₁⟩ := state_of_decision history₁ firstSite
  obtain ⟨control₂, stateEq₂, viewEq₂⟩ := state_of_decision history₂ secondSite
  have trace₁ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control₁) :=
    stateEq₁ ▸ history₁.1.trace
  have trace₂ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control₂) :=
    stateEq₂ ▸ history₂.1.trace
  rw [← viewEq₁, ← viewEq₂]
  exact ownerSwap_bounded covers who trace₁ trace₂

end Vegas
