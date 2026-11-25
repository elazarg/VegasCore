module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensLedgerClient

@[expose] public section

/-! # The first callback of the periodic Odds–Evens service -/

noncomputable section

namespace Vegas.Examples.OddsEvensLedgerClient

open OddsEvens EventGraphRuntime EventGraph Interaction GameTheory.Math.Probability

local notation "schedule" => OddsEvensService.scheduler
local notation "leakRule" => OddsEvensService.leaks
local notation "limits" => OddsEvensService.timeouts
local notation "startLaw" => OddsEvensService.initial

private def initialState : EventGraphRuntime.State compiled :=
  State.initial (setup.eventInputs (Env.empty (CellVal simpleExpr)))

private theorem startLaw_eq : startLaw = PMF.pure initialState := by
  change (PMF.pure _).map _ = _
  rw [PMF.pure_map]
  rfl

private theorem initial_quiescent (clock : Nat) (event : compiled.EventId) :
    ¬ ({initialState with clock := clock} : EventGraphRuntime.State compiled).AutomaticReady
      event := by
  intro automatic
  obtain ⟨_, _, defaulted⟩ := automatic.owned
  change _ ∈ (∅ : Finset Player) at defaulted
  exact Finset.notMem_empty _ defaulted

private theorem initial_ready : initialState.config.cut.Ready (eventId 0) := by decide

private theorem initial_not_ready (event : compiled.EventId) (different : event ≠ eventId 0) :
    ¬ initialState.config.cut.Ready event := by
  change Fin 4 at event
  fin_cases event
  · exact (different rfl).elim
  all_goals decide

private theorem initial_expire (event : compiled.EventId) :
    app.environment initialState (.expire event) = PMF.pure initialState := by
  change (environmentStep limits initialState (.expire event)).map State.drain = _
  have clear : ∀ query, ¬ initialState.AutomaticReady query := initial_quiescent 0
  by_cases zero : event = eventId 0
  · subst event
    rw [environmentStep_expire_of_not_due limits initialState _ initial_ready 0
      (by rfl) (by decide), PMF.pure_map, initialState.drain_eq_of_clear clear]
  · rw [environmentStep_expire_of_not_ready limits initialState _ (initial_not_ready event zero),
      PMF.pure_map, initialState.drain_eq_of_clear clear]

private theorem initial_tick :
    app.environment initialState .advanceClock = PMF.pure {initialState with clock := 1} := by
  exact reactiveApplication_tick_eq_pure limits leakRule initialState (initial_quiescent 0)

private theorem initial_commands (execution : app.Execution) (cursor : Nat)
    (cursorEq : execution.environmentRecall.length = cursor)
    (pending : execution.network.pending = []) (bound : cursor < 135) :
    ∃ command, schedule execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure command ∧
      ((command = .wait ∧ cursor ≠ 70) ∨
        (∃ event, command = .application (.expire event) ∧ cursor < 70) ∨
        (command = .application .advanceClock ∧ cursor = 70)) := by
  let view := execution.observeEnvironment app
  unfold OddsEvensService.scheduler PeriodicService.scheduler
  rw [cursorEq]
  have wait : app.pendingHeadCommand view = .wait := by
    simp [view, ReactiveApplication.pendingHeadCommand,
      ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView, pending]
  by_cases beforeQueue : cursor < 64
  · refine ⟨.wait, ?_, Or.inl ⟨rfl, by omega⟩⟩
    congr 1
    have selected := PeriodicService.processing_command (graph := compiled)
      (roster := Equiv.refl Bool) (leaks := leakRule) 0 cursor view beforeQueue
    simp only [Nat.zero_mul, Nat.zero_add] at selected
    change PeriodicService.command compiled (Equiv.refl Bool) leakRule cursor view =
      app.pendingHeadCommand view at selected
    exact selected.trans wait
  by_cases firstCycle : cursor < 71
  · interval_cases cursor
    · exact ⟨.wait, rfl, Or.inl ⟨rfl, by decide⟩⟩
    · exact ⟨.wait, rfl, Or.inl ⟨rfl, by decide⟩⟩
    · exact ⟨_, rfl, Or.inr (Or.inl ⟨eventId 0, rfl, by decide⟩)⟩
    · exact ⟨_, rfl, Or.inr (Or.inl ⟨eventId 1, rfl, by decide⟩)⟩
    · exact ⟨_, rfl, Or.inr (Or.inl ⟨eventId 2, rfl, by decide⟩)⟩
    · exact ⟨_, rfl, Or.inr (Or.inl ⟨eventId 3, rfl, by decide⟩)⟩
    · exact ⟨_, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  · refine ⟨.wait, ?_, Or.inl ⟨rfl, by omega⟩⟩
    congr 1
    have within : cursor - 71 < 64 := by omega
    have selected := PeriodicService.processing_command (graph := compiled)
      (roster := Equiv.refl Bool) (leaks := leakRule) 1 (cursor - 71) view within
    change PeriodicService.command compiled (Equiv.refl Bool) leakRule
      (71 + (cursor - 71)) view = app.pendingHeadCommand view at selected
    rwa [show 71 + (cursor - 71) = cursor by omega, wait] at selected

private theorem idle_prefix (cursor : Nat) (bound : cursor ≤ 135) :
    ∃ execution, app.roundsFrom startLaw schedule policy cursor = PMF.pure execution ∧
      execution.environmentRecall.length = cursor ∧
      execution.application = {initialState with clock := if 70 < cursor then 1 else 0} ∧
      execution.network = .empty ∧ execution.receipts = [] ∧ ∀ who, execution.logs who = [] := by
  induction cursor with
  | zero =>
    refine ⟨ReactiveApplication.Execution.initial app initialState, ?_, rfl, rfl, rfl, rfl, ?_⟩
    · simp only [ReactiveApplication.roundsFrom, startLaw_eq, PMF.pure_bind,
        ReactiveApplication.runRounds]
    · intro who
      rfl
  | succ cursor ih =>
    obtain ⟨execution, law, length, state, network, receipts, logs⟩ := ih (by omega)
    obtain ⟨command, selected, shape⟩ := initial_commands execution cursor length
      (by rw [network]; rfl) (by omega)
    let record := execution.environmentRecall ++ [⟨execution.observeEnvironment app, command⟩]
    let next := {execution with
      application := {initialState with clock := if 70 < cursor + 1 then 1 else 0}
      environmentRecall := record}
    refine ⟨next, ?_, ?_, rfl, network, receipts, logs⟩
    swap
    · simp [next, record, length]
    rw [ReactiveApplication.roundsFrom_succ, law, PMF.pure_bind,
      ReactiveApplication.round, selected, PMF.pure_bind]
    rcases shape with ⟨rfl, beforeTick⟩ | ⟨event, rfl, expiry⟩ | ⟨rfl, rfl⟩
    · have clock : (70 < cursor + 1) = (70 < cursor) := by
        apply propext
        omega
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        PMF.pure_map, ReactiveApplication.Command.actor?, PMF.pure_bind,
        ReactiveApplication.resume]
      change PMF.pure {execution with environmentRecall := record} = PMF.pure next
      have applicationEq : ({initialState with clock := if 70 < cursor + 1 then 1 else 0} :
          EventGraphRuntime.State compiled) = execution.application := by
        simp only [clock, ← state]
      exact congrArg PMF.pure (congrArg
        (fun application => {execution with application, environmentRecall := record})
        applicationEq.symm)
    · have before : execution.application = initialState := by
        rw [state, ite_eq_right (by omega : ¬ 70 < cursor)]
        rfl
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, before, initial_expire,
        PMF.pure_bind, PMF.pure_map]
      congr 1
      simp only [next, record, ite_eq_right (by omega : ¬ 70 < cursor + 1)]
      rfl
    · have before : execution.application = initialState := by
        rw [state, ite_eq_right (by decide : ¬ 70 < 70)]
        rfl
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, before, initial_tick,
        PMF.pure_bind, PMF.pure_map]
      rfl

/-- The periodic scheduler's first callback submits Even's commitment with
the fair bit law and an empty preceding response recall. -/
theorem periodic_first_activation :
    ∃ before : app.Execution,
      app.roundsFrom startLaw schedule policy 135 = PMF.pure before ∧
      before.application.clock = 1 ∧ before.network = .empty ∧
      (∀ who, before.logs who = []) ∧
      app.roundsFrom startLaw schedule policy 136 = (uniformLaw Bool).map
        (fun bit =>
          ({before with environmentRecall := before.environmentRecall ++
            [⟨before.observeEnvironment app, .activate even⟩]} : app.Execution).respond
              app even (reactiveBinding limits leakRule even (eventId 0) BaseTy.bool
                (.success bit) 0)) := by
  obtain ⟨before, prior, length, state, empty, _, logs⟩ := idle_prefix 135 (by decide)
  let activated : app.Execution := {before with environmentRecall := before.environmentRecall ++
    [⟨before.observeEnvironment app, .activate even⟩]}
  refine ⟨before, prior, ?_, empty, logs, ?_⟩
  · rw [state]
    rfl
  change app.roundsFrom startLaw schedule policy (135 + 1) = (uniformLaw Bool).map
    (fun bit => activated.respond app even
      (reactiveBinding limits leakRule even (eventId 0) BaseTy.bool (.success bit) 0))
  have selected : schedule before.environmentRecall (before.observeEnvironment app) =
      PMF.pure (.activate even) := by
    change PMF.pure (PeriodicService.command compiled (Equiv.refl Bool) leakRule
      before.environmentRecall.length (before.observeEnvironment app)) = _
    rw [length]
    rfl
  rw [ReactiveApplication.roundsFrom_succ, prior, PMF.pure_bind,
    ReactiveApplication.round, selected, PMF.pure_bind]
  have pendingObservation : app.observePending even before.network.pending =
      PMF.pure (∅ : Finset (MessageId Player)) := rfl
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    ReactiveApplication.Command.actor?, pendingObservation, PMF.pure_map,
    MessageNetwork.learn_empty, PMF.pure_bind, ReactiveApplication.resume]
  change app.invoke policy even activated = _
  let view := (activated.observe app even).ledgerOnly app
  let past := (activated.logs even).map (ReactiveApplication.PlayerEntry.ledgerOnly app)
  have inactive : even ∉ view.application.publicView.observation.defaulted := by
    change even ∉ before.application.config.defaulted
    rw [state]
    decide
  have turn : view.application.publicView.ownTurn? even = some (eventId 0) := by
    apply PublicView.ownTurn?_of_ownTurn
    refine ⟨?_, rfl, ?_⟩
    · change before.application.publicView.EventReady (eventId 0)
      rw [state]
      decide
    · intro event ready _
      by_contra different
      have notReady := initial_not_ready event different
      apply notReady
      change before.application.publicView.EventReady event at ready
      rw [state] at ready
      exact ⟨Finset.notMem_empty event, by
        intro pred member
        exact (List.not_mem_nil (ready.2 pred member)).elim⟩
  have unrecorded : eventRecorded timeouts leakRule past (eventId 0) = false := by
    change eventRecorded timeouts leakRule
      ((before.logs even).map (ReactiveApplication.PlayerEntry.ledgerOnly app)) (eventId 0) = false
    rw [logs]
    rfl
  have preferred : view.application.candidates
      (.prepared (view.application.publicView.bindingCount even)) = .fresh := by
    change before.application.candidates.lookup
      (even, .prepared (before.application.publicView.bindingCount even)) = .fresh
    rw [state]
    exact State.initial_candidate _ _ _
  have counted : view.application.publicView.bindingCount even = 0 := by
    change before.application.publicView.bindingCount even = 0
    rw [state]
    rfl
  have canonical : canonicalFreshSlot even view.application = some 0 :=
    (canonicalFreshSlot_canonical even _ preferred).trans (congrArg some counted)
  unfold ReactiveApplication.invoke
  change ((respond even past view).map (activated.respond app even)) = _
  simp only [respond, ite_eq_right inactive, turn, unrecorded, Bool.false_eq_true, ↓reduceIte,
    PMF.map_comp, Function.comp_def]
  congr 1
  funext bit
  congr 1
  exact canonicalServiceDecision_binding limits leakRule even past view (eventId 0)
    BaseTy.bool rfl rfl rfl inactive 0 canonical (.success bit)

end Vegas.Examples.OddsEvensLedgerClient
