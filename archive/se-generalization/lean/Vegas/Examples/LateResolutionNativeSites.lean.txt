/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionFirstDecision

/-! # All decision inputs of the concrete native risk menu

The initialized service has exactly two activations. Canonical first decisions
complete the application; the only unrecorded second input follows actual
silence. The classification uses genuine initialized native support.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

def secondExecutionFor (response : app.Action) : app.Execution :=
  let submitted := firstExecution.respond app owner response
  activateExecution (tickExecution (if response.transmission.isSome then
    includeExecution submitted (owner, 0) else waitExecution submitted))

theorem first_control_response (players : Player → app.Policy) :
    app.controlStep (initialLaw setup) horizon scheduler players
      (some ⟨7, some owner, firstExecution⟩) =
      (players owner (firstExecution.recall owner) (firstExecution.observe app owner)).map
        (fun response => some ⟨7, none, firstExecution.respond app owner response⟩) := by
  change ((players owner (firstExecution.recall owner) (firstExecution.observe app owner)).bind
    fun response => PMF.pure
    (some (⟨7, none, firstExecution.respond app owner response⟩ : app.Control))) = _
  exact PMF.bind_pure_comp _ _

theorem first_second_control_kernel (bounds : MessageBounds nativeGraph)
    (players : Player → app.Policy) (response : app.Action)
    (available : response ∈ (nativeMenu bounds).actions owner (firstExecution.recall owner)
      (firstExecution.observe app owner)) :
    (((PMF.pure (some ⟨7, none, firstExecution.respond app owner response⟩)).bind
      (app.controlStep (initialLaw setup) horizon scheduler players)).bind
        (app.controlStep (initialLaw setup) horizon scheduler players)).bind
          (app.controlStep (initialLaw setup) horizon scheduler players) =
      PMF.pure (some ⟨4, some owner, secondExecutionFor response⟩) := by
  rcases first_native_response_cases bounds response available with rfl | ⟨disclose, rfl⟩
  · rw [PMF.pure_bind, first_control_wait, PMF.pure_bind, first_control_wait_tick,
      PMF.pure_bind, first_control_wait_second_activation]
    rfl
  · rw [PMF.pure_bind, first_control_include, PMF.pure_bind, first_control_tick,
      PMF.pure_bind, first_control_second_activation]
    cases disclose <;> rfl

theorem first_native_second_prefix (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who) :
    ((nativeModel bounds).runBehavioral profile 8).map ExecutionProtocol.History.state =
      (profile owner (some (firstExecution.recall owner, firstExecution.observe app owner))).map
        (fun choice => some ⟨4, some owner, secondExecutionFor (choice.val.getD ⟨none⟩)⟩) := by
  change (((nativeModel bounds).runBehavioralFrom profile 8
    ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
      ExecutionProtocol.History.state) = _
  rw [(nativeMenu bounds).run_map_controlStep (initialLaw setup) horizon scheduler profile 8]
  let players := (nativeMenu bounds).decodeProfile (initialLaw setup) horizon scheduler profile
  have initialized := first_native_prefix bounds profile
  change (((nativeModel bounds).runBehavioralFrom profile 4
    ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
      ExecutionProtocol.History.state) = _ at initialized
  rw [(nativeMenu bounds).run_map_controlStep (initialLaw setup) horizon scheduler profile 4]
    at initialized
  change (fun law => law.bind (app.controlStep (initialLaw setup) horizon scheduler players))^[4]
    (PMF.pure none) = _ at initialized
  change (fun law => law.bind (app.controlStep (initialLaw setup) horizon scheduler players))^[8]
    (PMF.pure none) = _
  rw [show 8 = 4 + 4 by decide, Function.iterate_add_apply, initialized]
  change ((((PMF.pure (some ⟨7, some owner, firstExecution⟩)).bind
    (app.controlStep (initialLaw setup) horizon scheduler players)).bind
      (app.controlStep (initialLaw setup) horizon scheduler players)).bind
        (app.controlStep (initialLaw setup) horizon scheduler players)).bind
          (app.controlStep (initialLaw setup) horizon scheduler players) = _
  rw [PMF.pure_bind, first_control_response]
  have response : players owner (firstExecution.recall owner) (firstExecution.observe app owner) =
      (profile owner (some (firstExecution.recall owner, firstExecution.observe app owner))).map
        (fun choice => choice.val.getD ⟨none⟩) := by
    simp only [players, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      PMF.map_comp]
    rfl
  rw [response]
  simp only [PMF.bind_map, PMF.map_comp, PMF.bind_bind, Function.comp_def]
  conv_rhs => rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro choice _
  obtain ⟨action, allowed, same⟩ := choice.2
  dsimp only [Function.comp_def]
  rw [same, Option.getD_some]
  have kernel := first_second_control_kernel bounds players action allowed
  simp only [PMF.pure_bind, PMF.bind_bind] at kernel
  exact kernel


theorem second_native_history_state_cases (bounds : MessageBounds nativeGraph)
    (history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History)
    (control : app.Control) (current : history.state = some control)
    (active : control.actor = some owner)
    (position : control.execution.environmentRecall.length = 6) :
    history.state = some ⟨4, some owner, secondWaitExecution⟩ ∨
      ∃ disclose : Bool,
        history.state = some ⟨4, some owner, secondDecisionExecution disclose⟩ := by
  rcases history with ⟨state, originalTrace⟩
  cases current
  let history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History :=
    ⟨some control, originalTrace⟩
  let rawTrace := (nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler originalTrace
  have phase := phase_history rawTrace
  have recalled : (control.execution.recall owner).length = 1 := by
    have count := phase.recallCount
    rw [position, active] at count
    exact count
  have length := app.trace_length_of_control (initialLaw setup) horizon scheduler control rawTrace
  have rawLength : rawTrace.length = history.trace.length := by
    dsimp only [rawTrace]
    rw [(nativeMenu bounds).toRawTrace_length]
  rw [rawLength] at length
  have nativeLength : history.trace.length = 8 := by
    rw [position, Fin.sum_univ_one, recalled] at length
    exact length
  let assessment := (nativeMenu bounds).uniformAssessment (initialLaw setup) horizon scheduler
  have mixed := (nativeMenu bounds).uniform_fullyMixed (initialLaw setup) horizon scheduler
  have supported := mixed.history_supported history.trace
  rw [nativeLength] at supported
  have stateSupported : history.state ∈
      (((nativeModel bounds).runBehavioral assessment.strategy 8).map
        ExecutionProtocol.History.state).support := by
    rw [PMF.support_map]
    exact Set.mem_image_of_mem _ supported
  rw [first_native_second_prefix] at stateSupported
  obtain ⟨choice, _, same⟩ := PMF.support_map .. ▸ stateSupported
  obtain ⟨action, allowed, chosen⟩ := choice.2
  dsimp only at same
  rw [chosen, Option.getD_some] at same
  rcases first_native_response_cases bounds action allowed with rfl | ⟨disclose, rfl⟩
  · exact Or.inl same.symm
  · right
    refine ⟨disclose, ?_⟩
    cases disclose <;> exact same.symm

/-- Every actual decision history lies at the protected first input, the
unrecorded late input, or one of the two completed late inputs. -/
theorem native_decision_history_cases (bounds : MessageBounds nativeGraph)
    (history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History)
    (control : app.Control) (current : history.state = some control)
    (active : control.actor = some owner) :
    history.state = some ⟨7, some owner, firstExecution⟩ ∨
      history.state = some ⟨4, some owner, secondWaitExecution⟩ ∨
        ∃ disclose : Bool,
          history.state = some ⟨4, some owner, secondDecisionExecution disclose⟩ := by
  have traced : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) := current ▸ history.trace
  have phase := phase_history
    ((nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler traced)
  rcases phase.activation (by rw [active]; rfl) with first | second
  · exact Or.inl (first_native_history_state bounds history control current active first)
  · exact Or.inr (second_native_history_state_cases bounds history control current active second)


theorem native_decision_site_cases (bounds : MessageBounds nativeGraph)
    (site : (nativeModel bounds).InformationSite owner) :
    site.1 = some (firstExecution.recall owner, firstExecution.observe app owner) ∨
      site.1 = some (secondWaitExecution.recall owner, secondWaitExecution.observe app owner) ∨
        ∃ disclose : Bool, site.1 = some ((secondDecisionExecution disclose).recall owner,
          (secondDecisionExecution disclose).observe app owner) := by
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active (nativeModel bounds) site history
  cases current : history.1.state with
  | none => rw [current] at active; cases active
  | some control =>
      rw [current] at active
      have observed := ((nativeMenu bounds).info (initialLaw setup) horizon scheduler owner
        history.1.trace).symm.trans history.2
      rcases native_decision_history_cases bounds history.1 control current active with
        first | late | ⟨disclose, complete⟩
      · rw [first] at observed
        exact Or.inl observed.symm
      · rw [late] at observed
        exact Or.inr (Or.inl observed.symm)
      · rw [complete] at observed
        exact Or.inr (Or.inr ⟨disclose, observed.symm⟩)

end Vegas.LateResolutionService
