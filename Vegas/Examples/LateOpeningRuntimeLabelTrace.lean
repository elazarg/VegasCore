/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLabelHistories
import Interaction.ReactiveRecallInvariant

/-! # Actual initialized label permutations and native input persistence -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeLabelTrace

open Vegas.EventGraph Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
open LateOpeningRuntimeLabelSymmetry LateOpeningRuntimeLabelTransitions
open LateOpeningRuntimeLabelHistories

theorem replaceStateInputs_self (state : Vegas.EventGraphRuntime.State nativeGraph) :
    replaceStateInputs state state.config.inputs = state := rfl

theorem inputs_invariant (inputs : nativeGraph.Inputs) :
    app.Invariant (fun state => state.config.inputs = inputs) where
  submit state who submission valid := by
    change (submitStep (submission.call.register state who) who
      submission.call.packet).config.inputs = _
    rw [submitStep_config, (Submission.register_facts submission.call who state).1]
    exact valid
  handle state message next valid accepted := by
    have original : replaceStateInputs state inputs = state := by
      rw [← valid, replaceStateInputs_self]
    have covariance := reactive_handle_replace state inputs
      (congrFun valid aliceInput).symm message
    rw [original, accepted] at covariance
    exact (congrArg (fun result => result.config.inputs) (Option.some.inj covariance)).symm
  environment state command next valid supported := by
    have original : replaceStateInputs state inputs = state := by
      rw [← valid, replaceStateInputs_self]
    have covariance := environment_replace state inputs command
    rw [original] at covariance
    change next ∈ (environmentStep LateOpeningRuntimeService.runtime state command).support
      at supported
    rw [← covariance, PMF.support_map] at supported
    obtain ⟨before, _, rfl⟩ := supported
    rfl

def inputLabel (inputs : nativeGraph.Inputs) : Fin 3 :=
  let label : Label := inputs labelInput
  ⟨label.val.toNat, by
    have lower := label.property.1
    have upper := label.property.2
    omega⟩

theorem labelValue_inputLabel (inputs : nativeGraph.Inputs) :
    labelValue (inputLabel inputs) = inputs labelInput := by
  apply Subtype.ext
  change ((inputs labelInput).val.toNat : Int) = (inputs labelInput).val
  exact Int.toNat_of_nonneg (inputs labelInput).property.1

def permuteInputs (permutation : Equiv.Perm (Fin 3)) (inputs : nativeGraph.Inputs) :
    nativeGraph.Inputs :=
  Fin.cases (inputs aliceInput) (fun input =>
    Fin.cases (labelValue (permutation (inputLabel inputs))) (fun empty => nomatch empty) input)

theorem permuteInputs_bit (permutation : Equiv.Perm (Fin 3)) (inputs : nativeGraph.Inputs) :
    permuteInputs permutation inputs aliceInput = inputs aliceInput := rfl

theorem inputLabel_permuted (permutation : Equiv.Perm (Fin 3)) (inputs : nativeGraph.Inputs) :
    inputLabel (permuteInputs permutation inputs) = permutation (inputLabel inputs) := by
  apply Fin.ext
  exact Int.toNat_natCast _

theorem permuteInputs_inverse (permutation : Equiv.Perm (Fin 3)) (inputs : nativeGraph.Inputs) :
    permuteInputs permutation.symm (permuteInputs permutation inputs) = inputs := by
  funext input
  change Fin 2 at input
  fin_cases input
  · rfl
  · change labelValue (permutation.symm (inputLabel (permuteInputs permutation inputs))) = _
    rw [inputLabel_permuted, Equiv.symm_apply_apply, labelValue_inputLabel]


theorem respond_inputs (execution : app.Execution) (who : Player) (action : app.Action) :
    (execution.respond app who action).application.config.inputs =
      execution.application.config.inputs :=
  (inputs_invariant execution.application.config.inputs).respond execution who action rfl

theorem environmentStep_inputs (execution next : app.Execution) (command : app.Command)
    (supported : next ∈ (execution.environmentStep app command).support) :
    next.application.config.inputs = execution.application.config.inputs :=
  (inputs_invariant execution.application.config.inputs).environmentStep
    execution next command rfl supported

def permuteExecution (permutation : Equiv.Perm (Fin 3)) (execution : app.Execution) :
    app.Execution :=
  replaceExecution execution (permuteInputs permutation execution.application.config.inputs)

theorem permuteExecution_respond (permutation : Equiv.Perm (Fin 3))
    (execution : app.Execution) (who : Player) (action : app.Action) :
    permuteExecution permutation (execution.respond app who action) =
      (permuteExecution permutation execution).respond app who action := by
  unfold permuteExecution
  rw [respond_inputs]
  exact respond_replace execution _ (permuteInputs_bit permutation _) who action

theorem permuteExecution_environmentStep (permutation : Equiv.Perm (Fin 3))
    (execution : app.Execution) (command : app.Command) :
    (execution.environmentStep app command).map (permuteExecution permutation) =
      (permuteExecution permutation execution).environmentStep app command := by
  change _ = (replaceExecution execution
    (permuteInputs permutation execution.application.config.inputs)).environmentStep app command
  rw [← environmentStep_replace execution
    (permuteInputs permutation execution.application.config.inputs)
    (permuteInputs_bit permutation _) command]
  apply GameTheory.Math.Probability.map_congr_on_support _
  intro next supported
  unfold permuteExecution
  rw [environmentStep_inputs execution next command supported]


theorem permuteInputs_initial (permutation : Equiv.Perm (Fin 3)) (bit : Bool) (label : Fin 3) :
    permuteInputs permutation (setup.eventInputs (sourceInitial bit label)) =
      setup.eventInputs (sourceInitial bit (permutation label)) := by
  have labelEq : inputLabel (setup.eventInputs (sourceInitial bit label)) = label := by
    apply Fin.ext
    exact Int.toNat_natCast _
  funext input
  change Fin 2 at input
  fin_cases input
  · rfl
  · change labelValue (permutation (inputLabel _)) = labelValue (permutation label)
    rw [labelEq]

theorem initial_permutation (permutation : Equiv.Perm (Fin 3)) :
    initial.map (fun state => replaceStateInputs state
      (permuteInputs permutation state.config.inputs)) = initial := by
  have initialEq : initial = prior.map (fun parameter =>
      Vegas.EventGraphRuntime.State.initial (graph := nativeGraph)
        (setup.eventInputs (sourceInitial parameter.1 parameter.2))) := by
    unfold initial Vegas.serviceInitialLaw
    rw [show setup.initialLaw = prior.map (fun parameter =>
      sourceInitial parameter.1 parameter.2) from rfl, PMF.map_comp]
    rfl
  rw [initialEq, PMF.map_comp]
  have pointwise : (fun parameter : Parameter =>
      replaceStateInputs (Vegas.EventGraphRuntime.State.initial (graph := nativeGraph)
        (setup.eventInputs (sourceInitial parameter.1 parameter.2)))
        (permuteInputs permutation (setup.eventInputs
          (sourceInitial parameter.1 parameter.2)))) =
      (fun parameter => Vegas.EventGraphRuntime.State.initial (graph := nativeGraph)
        (setup.eventInputs (sourceInitial parameter.1 (permutation parameter.2)))) := by
    funext parameter
    rw [initial_replace _ _ (permuteInputs_bit permutation _), permuteInputs_initial]
  change prior.map (fun parameter : Parameter =>
    replaceStateInputs (Vegas.EventGraphRuntime.State.initial (graph := nativeGraph)
      (setup.eventInputs (sourceInitial parameter.1 parameter.2)))
      (permuteInputs permutation (setup.eventInputs
        (sourceInitial parameter.1 parameter.2)))) = _
  rw [pointwise]
  change prior.map ((fun parameter : Parameter =>
    Vegas.EventGraphRuntime.State.initial (graph := nativeGraph)
    (setup.eventInputs (sourceInitial parameter.1 parameter.2))) ∘
      (fun parameter => (parameter.1, permutation parameter.2))) = _
  rw [← PMF.map_comp, prior_label_permutation]


def permuteControl (permutation : Equiv.Perm (Fin 3)) (control : app.Control) : app.Control :=
  { control with execution := permuteExecution permutation control.execution }

def permuteProtocolState (permutation : Equiv.Perm (Fin 3)) :
    app.ProtocolState → app.ProtocolState := Option.map (permuteControl permutation)

theorem permuteControl_actor (permutation : Equiv.Perm (Fin 3)) (control : app.Control) :
    (permuteControl permutation control).actor = control.actor := rfl

theorem permuteControl_remaining (permutation : Equiv.Perm (Fin 3)) (control : app.Control) :
    (permuteControl permutation control).remaining = control.remaining := rfl

theorem permuteExecution_environmentObserve (permutation : Equiv.Perm (Fin 3))
    (execution : app.Execution) :
    (permuteExecution permutation execution).observeEnvironment app =
      execution.observeEnvironment app :=
  observeEnvironment_replace execution _ (permuteInputs_bit permutation _)


theorem permuteProtocolState_transition (permutation : Equiv.Perm (Fin 3))
    (horizon : Nat) (scheduler : app.Scheduler) (state : app.ProtocolState)
    (joint : Player → Option app.Action) :
    (app.transition initial horizon scheduler state joint).map
        (permuteProtocolState permutation) =
      app.transition initial horizon scheduler (permuteProtocolState permutation state) joint := by
  cases state with
  | none =>
      have same := congrArg (PMF.map (fun physical =>
        some (⟨horizon, none, ReactiveApplication.Execution.initial app physical⟩ : app.Control)))
        (initial_permutation permutation)
      convert same using 1
      all_goals simp only [ReactiveApplication.transition,
        permuteProtocolState, Option.map_none,
        PMF.map_comp, Function.comp_def, Option.map_some, permuteControl, permuteExecution,
        replaceExecution, ReactiveApplication.Execution.initial, List.map_nil]
      all_goals rfl
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          simp only [ReactiveApplication.transition, permuteProtocolState, Option.map_some,
            permuteControl, PMF.pure_map]
          rw [permuteExecution_respond]
      | none =>
          cases remaining with
          | zero => simp only [ReactiveApplication.transition, PMF.pure_map,
              permuteProtocolState, Option.map_some, permuteControl]
          | succ remaining =>
              have publicEq := permuteExecution_environmentObserve permutation execution
              have recalled : (permuteExecution permutation execution).environmentRecall =
                  execution.environmentRecall := rfl
              simp only [ReactiveApplication.transition, permuteProtocolState,
                Option.map_some, permuteControl, publicEq, recalled, PMF.map_bind]
              congr 1
              funext command
              rw [PMF.map_comp, ← permuteExecution_environmentStep permutation execution command,
                PMF.map_comp]
              rfl


/-- Every genuinely recorded Alice before-view retains the current immutable label. -/
def RecordedLabels (execution : app.Execution) : Prop :=
  ∀ who entry, entry ∈ execution.recall who → entry.beforeView.application.who = alice →
    entry.beforeView.application.observation.store (.inl labelInput) =
      some (execution.application.config.inputs labelInput)

theorem recordedLabels_invariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler RecordedLabels where
  respond execution acting action valid := by
    intro observer entry recorded aliceView
    rw [respond_inputs]
    rcases app.respond_entry_origin execution acting observer action entry recorded with old | fresh
    · exact valid observer entry old aliceView
    · rw [fresh.2] at aliceView ⊢
      change acting = alice at aliceView
      subst acting
      exact nativeGraph.playerStore_own_privateInput execution.application.config.store
        (.inl labelInput) alice (.range 0 2) rfl
  environment execution next command valid _ supported := by
    intro who entry recorded aliceView
    rw [environmentStep_inputs execution next command supported]
    rw [app.environmentStep_recall execution next command supported] at recorded
    exact valid who entry recorded aliceView

theorem recordedLabels_history (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    RecordedLabels control.execution :=
  (recordedLabels_invariant scheduler).history initial horizon
    (fun _ _ _ _ member => False.elim (List.not_mem_nil member)) trace

theorem replaceLocalView_inverse (view : Vegas.EventGraphRuntime.PlayerView nativeGraph)
    (original changed : nativeGraph.Inputs)
    (aligned : view.who = alice → view.observation.store (.inl labelInput) =
      some (original labelInput)) :
    replaceLocalView (replaceLocalView view changed) original = view := by
  cases view with
  | mk who publicView observation candidates =>
      cases observation with
      | mk order store actions =>
          by_cases isAlice : who = alice
          · subst who
            have fixed : Function.update store (.inl labelInput)
                (some (original labelInput)) = store := by
              rw [← aligned rfl]
              exact Function.update_eq_self _ _
            change (⟨alice, publicView,
              ⟨order, Function.update (Function.update store (.inl labelInput)
                (some (changed labelInput))) (.inl labelInput)
                (some (original labelInput)), actions⟩, candidates⟩ :
              Vegas.EventGraphRuntime.PlayerView nativeGraph) = _
            rw [Function.update_idem, fixed]
          · simp only [replaceLocalView, isAlice, ↓reduceIte]

theorem replaceEntry_inverse (entry : app.PlayerEntry) (original changed : nativeGraph.Inputs)
    (aligned : entry.beforeView.application.who = alice →
      entry.beforeView.application.observation.store (.inl labelInput) =
        some (original labelInput)) :
    replaceEntry (replaceEntry entry changed) original = entry := by
  have localEq := replaceLocalView_inverse entry.beforeView.application original changed aligned
  cases entry with
  | mk view action emitted =>
      cases view
      simp only [replaceEntry, replaceView, localEq]

theorem permuteExecution_inverse (permutation : Equiv.Perm (Fin 3))
    (execution : app.Execution) (aligned : RecordedLabels execution) :
    permuteExecution permutation.symm (permuteExecution permutation execution) = execution := by
  unfold permuteExecution replaceExecution
  dsimp only [replaceStateInputs, replaceInputs]
  rw [permuteInputs_inverse]
  have recalls : (fun who => ((execution.recall who).map
      (fun entry => replaceEntry entry
        (permuteInputs permutation execution.application.config.inputs))).map
      (fun entry => replaceEntry entry execution.application.config.inputs)) =
      execution.recall := by
    funext who
    rw [List.map_map]
    have fixed : (execution.recall who).map (fun entry =>
        replaceEntry (replaceEntry entry
          (permuteInputs permutation execution.application.config.inputs))
          execution.application.config.inputs) = (execution.recall who).map id := by
      apply List.map_congr_left
      intro entry member
      exact replaceEntry_inverse entry _ _ (aligned who entry member)
    simpa only [List.map_id, Function.comp_def] using fixed
  rw [recalls]
  cases execution
  rfl


theorem permuteProtocolState_actor (permutation : Equiv.Perm (Fin 3))
    (state : app.ProtocolState) :
    app.actor (permuteProtocolState permutation state) = app.actor state := by
  cases state <;> rfl

theorem permuteProtocolState_terminal (permutation : Equiv.Perm (Fin 3))
    (state : app.ProtocolState) :
    app.terminal (permuteProtocolState permutation state) = app.terminal state := by
  cases state <;> rfl

theorem rawMenu_available_permutation (permutation : Equiv.Perm (Fin 3))
    (state : app.ProtocolState) (who : Player) :
    rawMenu.available (permuteProtocolState permutation state) who =
      rawMenu.available state who := by
  cases state with
  | none => rfl
  | some control =>
      unfold ReactiveApplication.ResponseMenu.available
      dsimp only [permuteProtocolState, Option.map_some, permuteControl]
      change (rawMenu.actions who _ _ : Set app.Action) = _
      have observed := observe_replace control.execution
        (permuteInputs permutation control.execution.application.config.inputs)
        (permuteInputs_bit permutation _) who
      change (rawMenu.actions who
        ((replaceExecution control.execution _).recall who)
        ((replaceExecution control.execution _).observe app who) : Set app.Action) = _
      rw [observed]
      exact congrArg (fun actions : Finset app.Action => (actions : Set app.Action))
        (rawMenu_replace who (control.execution.recall who)
          (control.execution.observe app who) _)

theorem rawMenu_legal_permutation (permutation : Equiv.Perm (Fin 3))
    (horizon : Nat) (scheduler : app.Scheduler) (state : app.ProtocolState)
    (joint : Player → Option app.Action)
    (legal : (rawMenu.protocol initial horizon scheduler).Legal state joint) :
    (rawMenu.protocol initial horizon scheduler).Legal
      (permuteProtocolState permutation state) joint := by
  have availableEq : rawMenu.available (permuteProtocolState permutation state) =
      rawMenu.available state := funext (rawMenu_available_permutation permutation state)
  simpa only [ExecutionProtocol.Legal, ReactiveApplication.ResponseMenu.protocol,
    permuteProtocolState_terminal, permuteProtocolState_actor, availableEq]
    using legal

def permuteTrace (permutation : Equiv.Perm (Fin 3)) (horizon : Nat)
    (scheduler : app.Scheduler) :
    ∀ {state}, (rawMenu.protocol initial horizon scheduler).Trace state →
      (rawMenu.protocol initial horizon scheduler).Trace (permuteProtocolState permutation state)
  | _, .start => .start
  | _, .extend prior joint legal reached => by
      have pushed : permuteProtocolState permutation _ ∈
          ((app.transition initial horizon scheduler _ joint).map
            (permuteProtocolState permutation)).support :=
        PMF.support_map .. ▸ Set.mem_image_of_mem _ reached
      rw [permuteProtocolState_transition] at pushed
      exact .extend (permuteTrace permutation horizon scheduler prior) joint
        (rawMenu_legal_permutation permutation horizon scheduler _ joint legal) pushed


theorem recorded_view_owner (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (rawMenu.protocol initial horizon scheduler).Trace (some control))
    (who : Player) (entry : app.PlayerEntry) (recorded : entry ∈ control.execution.recall who) :
    entry.beforeView.application.who = who := by
  obtain ⟨before, _, _, original⟩ := app.recorded_response_prefix initial horizon scheduler
    control (rawMenu.toRawTrace initial horizon scheduler trace) who entry recorded
  rw [original]
  rfl

theorem permuteExecution_bob_recall (permutation : Equiv.Perm (Fin 3))
    (horizon : Nat) (scheduler : app.Scheduler) (control : app.Control)
    (trace : (rawMenu.protocol initial horizon scheduler).Trace (some control)) :
    (permuteExecution permutation control.execution).recall bob = control.execution.recall bob := by
  change (control.execution.recall bob).map _ = _
  have fixed : (control.execution.recall bob).map
      (fun entry => replaceEntry entry
        (permuteInputs permutation control.execution.application.config.inputs)) =
      (control.execution.recall bob).map id := by
    apply List.map_congr_left
    intro entry recorded
    have own := recorded_view_owner horizon scheduler control trace bob entry recorded
    simp only [replaceEntry, replaceView, replaceLocalView, own]
    norm_num [alice, bob]
  simpa only [List.map_id] using fixed

theorem permuteExecution_bob_observe (permutation : Equiv.Perm (Fin 3))
    (execution : app.Execution) :
    (permuteExecution permutation execution).observe app bob = execution.observe app bob := by
  have localEq := replaceStateInputs_bob_view execution.application
    (permuteInputs permutation execution.application.config.inputs)
    (permuteInputs_bit permutation _)
  change (⟨execution.network.observe bob,
    (replaceStateInputs execution.application _).playerView bob, execution.receipts⟩ :
    app.PlayerView) = _
  rw [localEq]
  rfl


theorem observe_bob_permutation (permutation : Equiv.Perm (Fin 3))
    (horizon : Nat) (scheduler : app.Scheduler) (state : app.ProtocolState)
    (trace : (rawMenu.protocol initial horizon scheduler).Trace state) :
    app.observe bob (permuteProtocolState permutation state) = app.observe bob state := by
  cases state with
  | none => rfl
  | some control =>
      change (if control.actor = some bob then
        some ((permuteExecution permutation control.execution).recall bob,
          (permuteExecution permutation control.execution).observe app bob) else none) = _
      rw [permuteExecution_bob_recall permutation horizon scheduler control trace,
        permuteExecution_bob_observe]
      rfl

theorem info_bob_permutation (permutation : Equiv.Perm (Fin 3))
    (horizon : Nat) (scheduler : app.Scheduler) (state : app.ProtocolState)
    (trace : (rawMenu.protocol initial horizon scheduler).Trace state) :
    (rawMenu.signals initial horizon scheduler).infoOf bob
        (permuteTrace permutation horizon scheduler trace) =
      (rawMenu.signals initial horizon scheduler).infoOf bob trace := by
  rw [rawMenu.info, rawMenu.info]
  exact observe_bob_permutation permutation horizon scheduler state trace

end Vegas.Examples.LateOpeningRuntimeLabelTrace
