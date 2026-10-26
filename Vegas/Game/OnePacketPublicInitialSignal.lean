/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerPriorSite

/-! # The actual late key retains every public initial input -/

noncomputable section

namespace Vegas

open Vegas Vegas.SourceProgram Interaction GameTheory GameTheory.Protocol EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {bounds : MessageBounds (graph setup)} {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}

/-- The public compiled initial inputs determine the signal. -/
def SourceProgram.Setup.PublicInitialSignal {Public : Type*}
    (setup : Setup (Player := Player) (L := L))
    (signal : State L setup.context → Public) : Prop :=
  ∀ (first second : State L setup.context),
    (∀ input, (graph setup).fieldPublic (.inl input) →
      setup.eventInputs first input = setup.eventInputs second input) →
    signal first = signal second

/-- Hidden-cell splicing leaves every public compiled initial input unchanged. -/
theorem splice_public_initial_inputs (who : Player) (mine others : State L setup.context)
    (input : (graph setup).InputId) (publicField : (graph setup).fieldPublic (.inl input)) :
    setup.eventInputs (splice who mine others) input = setup.eventInputs others input := by
  obtain ⟨name, kind, source, found⟩ :=
    (ContextRefs.initial_coversPrefix setup.program).1 input
  have same : inputId source = input := Sum.inl.inj found
  subst input
  have publicKind : (cellField kind).IsPublic := by
    change (inputLayout setup.context (inputId source)).IsPublic at publicField
    rwa [inputLayout_inputId source] at publicField
  have cellEq : (splice who mine others).get source = others.get source := by
    cases kind with
    | publicData payload => rfl
    | privateInput owner payload => exact publicKind.elim
    | commitment owner payload => exact publicKind.elim
    | publication payload => rfl
  have firstValue := encodeInputs_get (splice who mine others) source
  have secondValue := encodeInputs_get others source
  change cast _ (setup.eventInputs (splice who mine others) (inputId source)) = _ at firstValue
  change cast _ (setup.eventInputs others (inputId source)) = _ at secondValue
  have valuesEq := firstValue.trans ((congrArg cellValue cellEq).trans secondValue.symm)
  have back := congrArg (fun value =>
    cast (congrArg EventGraph.EventField.Value (inputLayout_inputId source)).symm value) valuesEq
  simpa only [cast_cast, cast_eq] using back

/-- A signal determined by public initial inputs is preserved by hidden-cell splicing. -/
theorem public_signal_preserved {Public : Type*} (signal : State L setup.context → Public)
    (observable : setup.PublicInitialSignal signal)
    (who : Player) (mine others : State L setup.context) :
    signal (splice who mine others) = signal others :=
  observable _ _ (splice_public_initial_inputs who mine others)


/-- Public initial fields are read directly from the actual input configuration. -/
theorem execution_public_initial_input
    (execution : (application setup runtime leaks).Execution) (who : Player)
    {draw : State L setup.context}
    (inputsEq : execution.application.config.inputs = setup.eventInputs draw)
    (input : (graph setup).InputId) (publicField : (graph setup).fieldPublic (.inl input)) :
    (execution.observe (application setup runtime leaks)
      who).application.publicView.observation.store
      (.inl input) = some (setup.eventInputs draw input) := by
  change (graph setup).publicStore execution.application.config.store (.inl input) = _
  rw [EventGraph.publicStore_of_public _ _ _ publicField]
  change some (execution.application.config.inputs input) = _
  rw [inputsEq]

variable [Fintype Player]

/-- Every draw actually represented by a site history is read at each public
initial field by that site's fixed public view, not only one chosen anchor. -/
theorem site_public_initial_inputs {who : Player}
    {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (decision : site.1 = some (past, view))
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory
      who site.1) {control : (application setup runtime leaks).Control}
    {draw : State L setup.context} (stateEq : history.1.state = some control)
    (inputsEq : control.execution.application.config.inputs = setup.eventInputs draw)
    (input : (graph setup).InputId) (publicField : (graph setup).fieldPublic (.inl input)) :
    view.application.publicView.observation.store (.inl input) =
      some (setup.eventInputs draw input) := by
  obtain ⟨seen, seenEq, viewEq⟩ := state_of_decision (runtime := runtime) history decision
  have same : control = seen := Option.some.inj (stateEq.symm.trans seenEq)
  subst seen
  rw [← viewEq]
  exact execution_public_initial_input (runtime := runtime) control.execution who inputsEq input
    publicField

/-- Same-key sites share the actual public view, including the initial store. -/
theorem same_key_publicView {who : Player}
    {site₁ site₂ : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationSite who}
    {past₁ past₂ : List (application setup runtime leaks).PlayerEntry}
    {view₁ view₂ : (application setup runtime leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂))
    (sameKey : lateKey setup runtime leaks who site₁.1 = lateKey setup runtime leaks who site₂.1) :
    view₁.application.publicView = view₂.application.publicView := by
  rw [firstSite, secondSite] at sameKey
  simp only [lateKey, Option.some.injEq, LateKey.mk.injEq] at sameKey
  obtain ⟨_, currentEq, _, _⟩ := sameKey
  exact congrArg Prod.fst currentEq

/-- Any two actual history draws at same-key sites have equal public initial
inputs. No unconditional prior independence or global hidden-fiber premise is used. -/
theorem same_key_public_initial_inputs {who : Player}
    {site₁ site₂ : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationSite who}
    {past₁ past₂ : List (application setup runtime leaks).PlayerEntry}
    {view₁ view₂ : (application setup runtime leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂))
    (sameKey : lateKey setup runtime leaks who site₁.1 = lateKey setup runtime leaks who site₂.1)
    (first : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory
      who site₁.1)
    (second : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory
      who site₂.1)
    {firstControl secondControl : (application setup runtime leaks).Control}
    {firstDraw secondDraw : State L setup.context}
    (firstState : first.1.state = some firstControl)
    (secondState : second.1.state = some secondControl)
    (firstInputs : firstControl.execution.application.config.inputs = setup.eventInputs firstDraw)
    (secondInputs : secondControl.execution.application.config.inputs =
      setup.eventInputs secondDraw)
    (input : (graph setup).InputId) (publicField : (graph setup).fieldPublic (.inl input)) :
    setup.eventInputs firstDraw input = setup.eventInputs secondDraw input := by
  have firstRead := site_public_initial_inputs (runtime := runtime) firstSite first firstState
    firstInputs input
    publicField
  have secondRead := site_public_initial_inputs (runtime := runtime) secondSite second secondState
    secondInputs input
    publicField
  have views := same_key_publicView (runtime := runtime) firstSite secondSite sameKey
  have observed := congrArg (fun view : PublicView (graph setup) =>
    view.observation.store (.inl input)) views
  exact Option.some.inj (firstRead.symm.trans (observed.trans secondRead))

end Vegas
