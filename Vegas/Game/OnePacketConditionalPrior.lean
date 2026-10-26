/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerBase
import Vegas.Game.OnePacketPublicInitialSignal
import Vegas.Compile.EventGraphObservationEncoding

/-! # Owner swaps within an observed public prior fiber

Private initial cells may be independent conditional on a public signal.
The owner swap then has a common prior ratio on the supported input set
fixing both the owner's hidden cells and that signal. Every actual history
at a site belongs to this set when public initial inputs determine the signal.
Same-key sites also supply supported splices, through their actual public views.
These are prior-law producers; no equilibrium preservation result is asserted.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Public : Type*} {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  (signal : State L setup.context → Public)
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

private theorem private_input_not_failed (wellFormed : setup.WellFormed)
    {draw : State L setup.context} (member : draw ∈ setup.initialLaw.support) (who : Player)
    (input : (graph setup).InputId) (privateTo : PrivateTo who (setup := setup) (.inl input)) :
    ¬ ((graph setup).layout (.inl input)).IsFailure (setup.eventInputs draw input) := by
  obtain ⟨name, kind, source, found⟩ :=
    (ContextRefs.initial_coversPrefix setup.program).1 input
  have same : inputId source = input := Sum.inl.inj found
  subst input
  exact eventInputs_not_failure wellFormed member source
    ((privateTo_inl_iff who source).mp privateTo)

/-- The shared prior set restricts both hidden inputs and the public fiber. -/
def hiddenPublicFiberInputs (who : Player) (base : State L setup.context) :
    Set (graph setup).Inputs :=
  {inputs | ∃ draw ∈ setup.initialLaw.support, inputs = setup.eventInputs draw ∧
    HiddenAgree who draw base ∧ signal draw = signal base}

/-- Conditional prior scaling uses only the restricted shared set; it does not
require the public signal to be fixed on every supported HiddenAgree draw. -/
theorem ownerSwap_priorScaled (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (preserves : ∀ (who : Player) (mine others : State L setup.context),
      signal (splice who mine others) = signal others)
    {who : Player} {view₁ view₂ : (application setup runtime leaks).PlayerView}
    {base other : State L setup.context} (baseMember : base ∈ setup.initialLaw.support)
    (otherMember : other ∈ setup.initialLaw.support)
    (baseStore : ∀ input, PrivateTo who (setup := setup) (.inl input) →
      view₁.application.observation.store (.inl input) = some (setup.eventInputs base input))
    (otherStore : ∀ input, PrivateTo who (setup := setup) (.inl input) →
      view₂.application.observation.store (.inl input) = some (setup.eventInputs other input)) :
    ∀ state ∈ (initialLaw setup).support,
      state.config.inputs ∈ swapAllowed (ownerSwap who view₁.application view₂.application) ∩
        hiddenPublicFiberInputs signal who base →
      (initialLaw setup (state.swap (ownerSwap who view₁.application view₂.application))).toReal =
        (setup.initialLaw (splice who other base)).toReal / (setup.initialLaw base).toReal *
          (initialLaw setup state).toReal := by
  rintro state member ⟨⟨allowedState, allowedMember, allowedInputs, swappedMember⟩, draw,
    drawMember, drawInputs, agree, sameSignal⟩
  obtain ⟨stateDraw, -, rfl⟩ := eq_initial_of_mem_support member
  have stateDrawEq : stateDraw = draw := eventInputs_injective drawInputs
  subst stateDrawEq
  obtain ⟨allowedDraw, -, rfl⟩ := eq_initial_of_mem_support allowedMember
  have allowedDrawEq : allowedDraw = stateDraw := eventInputs_injective allowedInputs
  subst allowedDrawEq
  obtain ⟨swappedDraw, -, swappedEq⟩ := eq_initial_of_mem_support swappedMember
  have firstStore : ∀ input, PrivateTo who (setup := setup) (.inl input) →
      view₁.application.observation.store (.inl input) =
        some (setup.eventInputs allowedDraw input) := fun input privateTo => by
    rw [baseStore input privateTo, (hiddenAgree_iff_inputs.mp agree input privateTo)]
  have spliced := ownerSwap_inputs_splice who allowedDraw other firstStore otherStore
    (private_input_not_failed wellFormed drawMember who)
    (private_input_not_failed wellFormed otherMember who)
  have swappedInputs := congrArg (fun state : EventGraphRuntime.State (graph setup) =>
    state.config.inputs) swappedEq
  change (ownerSwap who view₁.application view₂.application).inputs
    (setup.eventInputs allowedDraw) = setup.eventInputs swappedDraw at swappedInputs
  have swappedDrawEq : swappedDraw = splice who other allowedDraw :=
    eventInputs_injective (swappedInputs.symm.trans spliced)
  rw [swappedEq, swappedDrawEq, initialLaw_initial, initialLaw_initial]
  have product := setup.initialLaw_splice_mul signal independent preserves who other
    agree sameSignal.symm
  have basePositive : 0 < (setup.initialLaw base).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp baseMember) (PMF.apply_ne_top _ _)
  have realProduct := congrArg ENNReal.toReal product
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at realProduct
  field_simp
  linarith

variable [Fintype Player]

/-- Every actual history at the site belongs to the restricted shared set.
The public-signal equality comes from actual public input observations. -/
theorem site_hiddenPublicFiberInputs
    (observable : setup.PublicInitialSignal signal)
    {who : Player}
    {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (decision : site.1 = some (past, view))
    (anchor : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory
      who site.1) {anchorControl : (application setup runtime leaks).Control}
    {base : State L setup.context} (anchorState : anchor.1.state = some anchorControl)
    (anchorInputs : anchorControl.execution.application.config.inputs = setup.eventInputs base)
    (baseStore : ∀ input, PrivateTo who (setup := setup) (.inl input) →
      view.application.observation.store (.inl input) = some (setup.eventInputs base input)) :
    ∀ history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory
      who site.1, ∃ control : (application setup runtime leaks).Control,
      history.1.state = some control ∧ control.execution.application.config.inputs ∈
        hiddenPublicFiberInputs signal who base := by
  intro history
  obtain ⟨control, draw, stateEq, member, inputsEq, drawStore⟩ := siteDraw (runtime := runtime)
    decision history
  refine ⟨control, stateEq, draw, member, inputsEq, ?_, ?_⟩
  · apply hiddenAgree_iff_inputs.mpr
    intro input privateTo
    exact Option.some.inj ((drawStore input privateTo).symm.trans (baseStore input privateTo))
  · apply observable draw base
    intro input publicField
    exact same_key_public_initial_inputs (runtime := runtime) decision decision rfl history anchor
      stateEq anchorState inputsEq anchorInputs input publicField

/-- The same-key bridge applies to all actual draws used by supported splice
closure, not just a selected pair of anchors. -/
theorem ownerSwap_priorClosed_given_public (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    {who : Player}
    {site₁ site₂ : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationSite who}
    {past₁ past₂ : List (application setup runtime leaks).PlayerEntry}
    {view₁ view₂ : (application setup runtime leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂))
    (sameKey : lateKey setup runtime leaks who site₁.1 = lateKey setup runtime leaks who site₂.1) :
    ∀ initial ∈ setup.initialLaw.support,
      (∃ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory
        who site₁.1, ∃ control : (application setup runtime leaks).Control,
        history.1.state = some control ∧
          control.execution.application.config.inputs = setup.eventInputs initial) →
      ∃ other ∈ setup.initialLaw.support, setup.eventInputs other =
        (ownerSwap who view₁.application view₂.application).inputs (setup.eventInputs initial) := by
  rintro initial member ⟨history, control, stateEq, inputsEq⟩
  obtain ⟨control₁, draw₁, stateEq₁, -, inputsEq₁, firstStore⟩ := siteDraw (runtime := runtime)
    firstSite history
  rw [stateEq] at stateEq₁
  cases Option.some.inj stateEq₁
  obtain ⟨history₂, -⟩ := site₂.2
  obtain ⟨control₂, draw₂, stateEq₂, drawMember₂, inputsEq₂, secondStore⟩ :=
    siteDraw (runtime := runtime) secondSite history₂
  have firstStore' : ∀ input, PrivateTo who (setup := setup) (.inl input) →
      view₁.application.observation.store (.inl input) = some (setup.eventInputs initial input) :=
    fun input privateTo => by rw [firstStore input privateTo, ← inputsEq₁, inputsEq]
  have sameSignal : signal draw₂ = signal initial := observable draw₂ initial
    (fun input publicField => same_key_public_initial_inputs (runtime := runtime)
      secondSite firstSite sameKey.symm history₂ history stateEq₂ stateEq inputsEq₂ inputsEq
        input publicField)
  refine ⟨splice who draw₂ initial,
    setup.splice_mem_support signal independent who drawMember₂ member sameSignal, ?_⟩
  exact (ownerSwap_inputs_splice who initial draw₂ firstStore' secondStore
    (private_input_not_failed wellFormed member who)
    (private_input_not_failed wellFormed drawMember₂ who)).symm

end Vegas
