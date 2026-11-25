module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensFirstActivation

@[expose] public section

/-! # The pending first commitment in the periodic Odds–Evens service -/

noncomputable section

namespace Vegas.Examples.OddsEvensLedgerClient

open OddsEvens EventGraphRuntime EventGraph Interaction GameTheory.Math.Probability

local notation "schedule" => OddsEvensService.scheduler
local notation "leakRule" => OddsEvensService.leaks
local notation "limits" => OddsEvensService.timeouts
local notation "startLaw" => OddsEvensService.initial

private def withCommand (execution : app.Execution) (command : app.Command) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
    [⟨execution.observeEnvironment app, command⟩] }

private theorem withCommand_length (execution : app.Execution) (command : app.Command) :
    (withCommand execution command).environmentRecall.length =
      execution.environmentRecall.length + 1 := by
  simp [withCommand]

private def firstAction (bit : Bool) : app.Action :=
  reactiveBinding limits leakRule even (eventId 0) BaseTy.bool (.success bit) 0

private theorem firstAction_recall (execution : app.Execution) (bit : Bool) :
    (execution.respond app even (firstAction bit)).environmentRecall =
      execution.environmentRecall := rfl

private theorem no_turn_odd_initial (state : EventGraphRuntime.State compiled)
    (config : state.config =
      Config.initial (graph := compiled) (setup.eventInputs (Env.empty (CellVal simpleExpr)))) :
    state.publicView.ownTurn? odd = none := by
  cases selected : state.publicView.ownTurn? odd with
  | none => rfl
  | some event =>
    obtain ⟨ready, actor⟩ := state.publicView.ownTurn?_spec odd event selected
    have noPrereq (predecessor : compiled.EventId)
        (requires : predecessor ∈ compiled.order.predecessors event) : False := by
      have complete := ready.2 predecessor requires
      change predecessor ∈ state.config.history.map EventCompletion.event at complete
      rw [config] at complete
      exact List.not_mem_nil complete
    change Fin 4 at event
    fin_cases event
    · change some even = some odd at actor
      cases actor
    · exact (noPrereq (eventId 0) (by decide)).elim
    · change some even = some odd at actor
      cases actor
    · exact (noPrereq (eventId 0) (by decide)).elim

private theorem early_odd_round (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 136)
    (config : execution.application.config =
      Config.initial (graph := compiled) (setup.eventInputs (Env.empty (CellVal simpleExpr)))) :
    app.round schedule policy execution =
      PMF.pure ((withCommand execution (.activate odd)).respond app odd ⟨none⟩) := by
  have selected : schedule execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.activate odd) := by
    change PMF.pure (PeriodicService.command compiled (Equiv.refl Bool) leakRule
      execution.environmentRecall.length (execution.observeEnvironment app)) = _
    rw [cursor]
    rfl
  have pendingObservation : app.observePending odd execution.network.pending =
      PMF.pure (∅ : Finset (MessageId Player)) := rfl
  have idle := no_turn_odd_initial execution.application config
  unfold ReactiveApplication.round
  rw [selected, PMF.pure_bind]
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    ReactiveApplication.Command.actor?, pendingObservation, PMF.pure_map,
    MessageNetwork.learn_empty, PMF.pure_bind, ReactiveApplication.resume]
  change app.invoke policy odd (withCommand execution (.activate odd)) = _
  unfold ReactiveApplication.invoke
  have silent : policy odd ((withCommand execution (.activate odd)).logs odd)
      ((withCommand execution (.activate odd)).observe app odd) = PMF.pure ⟨none⟩ := by
    unfold policy ReactiveApplication.ledgerPolicy respond
    split
    · rfl
    · change (match execution.application.publicView.ownTurn? odd with
        | none => PMF.pure (⟨none⟩ : app.Action)
        | some _ => _) = _
      rw [idle]
  rw [silent, PMF.pure_map]

/-- The first Even callback submits its bit. The immediately following Odd
callback is recorded with a silent response. -/
def firstOddIdleResponse (before : app.Execution) (bit : Bool) : app.Execution :=
  let evenSent : app.Execution := ({before with environmentRecall := before.environmentRecall ++
    [⟨before.observeEnvironment app, .activate even⟩]} : app.Execution).respond app even
      (reactiveBinding limits leakRule even (eventId 0) BaseTy.bool (.success bit) 0)
  ({evenSent with environmentRecall := evenSent.environmentRecall ++
    [⟨evenSent.observeEnvironment app, .activate odd⟩]} : app.Execution).respond app odd ⟨none⟩

/-- The scheduler's first Odd callback happens before Even's commitment
is included. It is silent, and the run still retains both fair bit branches. -/
theorem periodic_first_odd_activation :
    ∃ before : app.Execution,
      app.roundsFrom startLaw schedule policy 135 = PMF.pure before ∧
      app.roundsFrom startLaw schedule policy 137 =
        (uniformLaw Bool).map (firstOddIdleResponse before) := by
  obtain ⟨before, prior, _, _, _, afterEven⟩ := periodic_first_activation
  obtain ⟨length, state, _, _, _⟩ := periodic_before_first_activation before prior
  refine ⟨before, prior, ?_⟩
  change app.roundsFrom startLaw schedule policy (136 + 1) =
    (uniformLaw Bool).map (fun bit =>
      (withCommand ((withCommand before (.activate even)).respond app even (firstAction bit))
        (.activate odd)).respond app odd ⟨none⟩)
  rw [ReactiveApplication.roundsFrom_succ, afterEven, PMF.bind_map, PMF.map]
  apply bind_congr_on_support _
  intro bit _
  apply early_odd_round
  · change ((withCommand before (.activate even)).respond app even
        (firstAction bit)).environmentRecall.length = 136
    rw [firstAction_recall, withCommand_length, length]
  · change ((withCommand before (.activate even)).respond app even
        (firstAction bit)).application.config = _
    rw [(reactive_respond_application limits leakRule
        (withCommand before (.activate even)) even (firstAction bit)).1]
    change before.application.config = _
    rw [state]
    rfl

private def startingApplication : EventGraphRuntime.State compiled :=
  State.initial (graph := compiled) (setup.eventInputs (Env.empty (CellVal simpleExpr)))

private theorem starting_clear (state : EventGraphRuntime.State compiled)
    (config : state.config = startingApplication.config) (event : compiled.EventId) :
    ¬ state.AutomaticReady event := by
  intro automatic
  obtain ⟨_, _, defaulted⟩ := automatic.owned
  rw [config] at defaulted
  exact Finset.notMem_empty _ defaulted

private theorem pending_expiry (state : EventGraphRuntime.State compiled)
    (config : state.config = startingApplication.config)
    (activated : state.activatedAt = startingApplication.activatedAt)
    (clock : state.clock = 1) (event : compiled.EventId) :
    app.environment state (.expire event) = PMF.pure state := by
  change (environmentStep limits state (.expire event)).map State.drain = _
  have clear := starting_clear state config
  by_cases zero : event = eventId 0
  · subst event
    have ready : state.config.cut.Ready (eventId 0) := by rw [config]; decide
    have entered : state.activatedAt (eventId 0) = some 0 := by rw [activated]; rfl
    rw [environmentStep_expire_of_not_due limits state _ ready 0 entered (by rw [clock]; decide),
      PMF.pure_map, state.drain_eq_of_clear clear]
  · have notReady : ¬ state.config.cut.Ready event := by
      rw [config]
      change Fin 4 at event
      fin_cases event
      · exact (zero rfl).elim
      all_goals decide
    rw [environmentStep_expire_of_not_ready limits state event notReady,
      PMF.pure_map, state.drain_eq_of_clear clear]

private theorem scheduled_environment_round (execution : app.Execution)
    (command : EnvironmentCommand compiled) (application : EventGraphRuntime.State compiled)
    (selected : schedule execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.application command))
    (result : app.environment execution.application command = PMF.pure application) :
    app.round schedule policy execution =
      PMF.pure { withCommand execution (.application command) with application } := by
  simp only [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, result, PMF.pure_map,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  rfl

private theorem pending_bookkeeping (origin : app.Execution)
    (cursor : origin.environmentRecall.length = 137)
    (config : origin.application.config = startingApplication.config)
    (activated : origin.application.activatedAt = startingApplication.activatedAt)
    (clock : origin.application.clock = 1)
    (count : Nat) (bound : count ≤ 5) :
    ∃ execution, app.runRounds schedule policy count origin = PMF.pure execution ∧
      execution.environmentRecall.length = 137 + count ∧
      execution.application = {origin.application with clock := if count = 5 then 2 else 1} ∧
      execution.network = origin.network ∧ execution.logs = origin.logs := by
  induction count with
  | zero =>
    refine ⟨origin, rfl, cursor, ?_, rfl, rfl⟩
    rw [ite_eq_right (by decide : ¬ 0 = 5), ← clock]
    rfl
  | succ count ih =>
    obtain ⟨execution, law, length, application, network, logs⟩ := ih (by omega)
    have old : execution.application = origin.application := by
      rw [application, ite_eq_right (by omega : count ≠ 5), ← clock]
      rfl
    have step : app.runRounds schedule policy (count + 1) origin =
        app.round schedule policy execution := by
      rw [app.runRounds_add schedule policy count 1 origin, law, PMF.pure_bind]
      simp only [ReactiveApplication.runRounds, PMF.bind_pure]
    by_cases going : count < 4
    · let event : compiled.EventId := ⟨count, going⟩
      have chosen : schedule execution.environmentRecall (execution.observeEnvironment app) =
          PMF.pure (.application (.expire event)) := by
        change PMF.pure (PeriodicService.command compiled (Equiv.refl Bool) leakRule
          execution.environmentRecall.length (execution.observeEnvironment app)) = _
        rw [length]
        simpa [PeriodicService.width, PeriodicService.packetBudget, PeriodicService.cycles,
          event, ← Nat.add_assoc] using congrArg PMF.pure
          (PeriodicService.expire_command (graph := compiled)
          (roster := Equiv.refl Bool) (leaks := leakRule) 1 event going
          (execution.observeEnvironment app))
      have unchanged : app.environment execution.application (.expire event) =
          PMF.pure execution.application := pending_expiry execution.application
        (old ▸ config) (old ▸ activated) (old ▸ clock) event
      refine ⟨withCommand execution (.application (.expire event)), ?_, ?_, ?_, network, logs⟩
      · rw [step, scheduled_environment_round _ _ _ chosen unchanged]
        rfl
      · rw [withCommand_length, length]
        omega
      · change execution.application = _
        rw [old, ite_eq_right (by omega : count + 1 ≠ 5), ← clock]
        rfl
    · have fourth : count = 4 := by omega
      subst count
      have chosen : schedule execution.environmentRecall (execution.observeEnvironment app) =
          PMF.pure (.application .advanceClock) := by
        change PMF.pure (PeriodicService.command compiled (Equiv.refl Bool) leakRule
          execution.environmentRecall.length (execution.observeEnvironment app)) = _
        rw [length]
        rfl
      have changed : app.environment execution.application .advanceClock =
          PMF.pure {origin.application with clock := 2} := by
        rw [old, reactiveApplication_tick_eq_pure limits leakRule origin.application
          (starting_clear origin.application config)]
        congr 1
        simp only [clock]
      refine ⟨{withCommand execution (.application .advanceClock) with
        application := {origin.application with clock := 2}}, ?_, ?_, rfl, network, logs⟩
      · rw [step, scheduled_environment_round _ _ _ chosen changed]
      · exact (withCommand_length _ _).trans (congrArg (· + 1) length)

private def firstPacket : Message Player (WitnessedPacket compiled) :=
  ⟨(even, 0), ⟨.commitment (eventId 0) (even, .prepared 0), none, some ⟨eventId 0⟩⟩⟩

private theorem first_pending (before : app.Execution)
    (empty : before.network = .empty) (bit : Bool) :
    (firstOddIdleResponse before bit).network.pending = [firstPacket] := by
  unfold firstOddIdleResponse
  simp only [ReactiveApplication.Execution.respond, reactiveBinding, MessageNetwork.submit]
  rw [empty]
  change [_] = [firstPacket]
  congr 1

private theorem first_cut (before : app.Execution)
    (application : before.application = { startingApplication with clock := 1 })
    (bit : Bool) :
    (firstOddIdleResponse before bit).application.config = startingApplication.config := by
  change (((withCommand before (.activate even)).respond app even
    (firstAction bit)).application).config = startingApplication.config
  rw [(reactive_respond_application limits leakRule
    (withCommand before (.activate even)) even (firstAction bit)).1]
  change before.application.config = _
  rw [application]

private theorem first_bindingResult (before : app.Execution)
    (application : before.application = { startingApplication with clock := 1 }) (bit : Bool) :
    (firstOddIdleResponse before bit).application.bindingResult
      (even, .prepared 0) BaseTy.bool = .success bit := by
  change EventGraphRuntime.State.bindingResult
    (((withCommand before (.activate even)).respond app even (firstAction bit)).application)
      (even, .prepared 0) BaseTy.bool = .success bit
  exact reactiveBinding_result limits leakRule even (eventId 0) BaseTy.bool (.success bit) 0
    (withCommand before (.activate even)) (by
      change before.application.candidates.lookup (even, .prepared 0) = .fresh
      rw [application]
      exact State.initial_candidate _ _ _)

private theorem first_admission_tables (before : app.Execution)
    (application : before.application = { startingApplication with clock := 1 }) (bit : Bool) :
    (firstOddIdleResponse before bit).application.accepted = startingApplication.accepted ∧
    (firstOddIdleResponse before bit).application.activatedAt = startingApplication.activatedAt ∧
    (firstOddIdleResponse before bit).application.clock = 1 := by
  have same := (reactive_respond_application limits leakRule
    (withCommand before (.activate even)) even (firstAction bit)).2
  change (firstOddIdleResponse before bit).application.publicView = before.application.publicView
    at same
  rw [application] at same
  exact ⟨congrArg PublicView.accepted same, congrArg PublicView.activatedAt same,
    congrArg PublicView.clock same⟩

private theorem first_handle (execution : app.Execution)
    (config : execution.application.config = startingApplication.config)
    (accepted : execution.application.accepted = startingApplication.accepted)
    (activated : execution.application.activatedAt = startingApplication.activatedAt)
    (clock : execution.application.clock = 2) (bit : Bool)
    (result : execution.application.bindingResult (even, .prepared 0) BaseTy.bool = .success bit) :
    ∃ next, app.handle execution.application firstPacket = some next ∧
      next.config.outputs (eventId 0) = some (PublicationResult.success bit) := by
  let state := execution.application
  have ready : state.config.cut.Ready (eventId 0) := by
    change _ at config
    change execution.application.config.cut.Ready (eventId 0)
    rw [config]
    decide
  have timely : state.WithinDeadline limits (eventId 0) := by
    change (match execution.application.activatedAt (eventId 0) with
      | none => False
      | some entered => execution.application.clock - entered < (limits).duration (eventId 0))
    rw [activated, clock]
    rw [show startingApplication.activatedAt (eventId 0) = some 0 from rfl]
    decide
  have active : even ∉ state.config.defaulted := by
    change even ∉ execution.application.config.defaulted
    rw [config]
    decide
  have vacant : state.accepted (.inr (eventId 0)) = none := by
    change execution.application.accepted (.inr (eventId 0)) = none
    rw [accepted]
    rfl
  have unused : state.HandleUnused (even, .prepared 0) := by
    change ∀ field, execution.application.accepted field ≠ some (even, .prepared 0)
    rw [accepted]
    rintro (input | event)
    · exact Fin.elim0 input
    · change none ≠ _
      intro impossible
      cases impossible
  have native := handle_commitment_eq limits state (even, 0) (eventId 0) (even, .prepared 0)
    even BaseTy.bool rfl rfl rfl ready timely active rfl rfl vacant unused
  change _ = some _ at native
  change ∃ next, (EventGraphRuntime.handle limits state
    ⟨(even, 0), .commitment (eventId 0) (even, .prepared 0)⟩).map State.drain = some next ∧
      next.config.outputs (eventId 0) = some (PublicationResult.success bit)
  rw [native, Option.map_some]
  refine ⟨_, rfl, ?_⟩
  have decoded : state.bindingResult (even, .prepared 0) BaseTy.bool = .success bit := result
  simp only [decoded, cast_eq]
  let admitted := {state.complete (eventId 0) ready (some (PublicationResult.success bit))
      (PublicationResult.success bit) with
    accepted := Function.update state.accepted (.inr (eventId 0)) (some (even, .prepared 0))
    candidates := state.candidates.freeze (even, .prepared 0)}
  change admitted.drain.config.outputs (eventId 0) = _
  have clear : ∀ event, ¬ admitted.AutomaticReady event := by
    intro event automatic
    obtain ⟨_, _, defaulted⟩ := automatic.owned
    have noDefault : admitted.config.defaulted = state.config.defaulted := by
      change (state.config.complete _ ready _ _).defaults.defaulted = _
      rw [Config.complete_defaults]
      have event := state.config.completion_bind_some_defaultEvent (eventId 0)
        even BaseTy.bool rfl rfl (.success bit) (.success bit)
      dsimp only [cast_eq] at event
      rw [event]
      exact DefaultHistory.defaulted_record_none _
    rw [noDefault] at defaulted
    have original : state.config.defaulted = ∅ := by
      change execution.application.config.defaulted = _
      rw [config]
      rfl
    rw [original] at defaulted
    exact Finset.notMem_empty _ defaulted
  rw [admitted.drain_eq_of_clear clear]
  exact Config.complete_output_same ..

/-- Each fair bit branch is included by the periodic scheduler at its first
queue-processing command, and is recorded as the actual commitment value. -/
theorem periodic_first_commitment_supported (bit : Bool) :
    ∃ execution ∈ (app.roundsFrom startLaw schedule policy 143).support,
      execution.environmentRecall.length = 143 ∧
      execution.application.config.outputs (eventId 0) = some (PublicationResult.success bit) := by
  obtain ⟨before, prior, roundLaw⟩ := periodic_first_odd_activation
  obtain ⟨length, application, empty, _, _⟩ := periodic_before_first_activation before prior
  let origin := firstOddIdleResponse before bit
  have originLength : origin.environmentRecall.length = 137 := by
    change (withCommand ((withCommand before (.activate even)).respond app even (firstAction bit))
      (.activate odd)).environmentRecall.length = _
    rw [withCommand_length, firstAction_recall, withCommand_length, length]
  have originSupported : origin ∈ (app.roundsFrom startLaw schedule policy 137).support := by
    rw [roundLaw, PMF.support_map]
    exact ⟨bit, mem_support_uniformLaw bit, rfl⟩
  have config := first_cut before application bit
  obtain ⟨accepted, activated, clock⟩ := first_admission_tables before application bit
  obtain ⟨current, bookkeeping, currentLength, currentState, currentNetwork, _⟩ :=
    pending_bookkeeping origin originLength config activated clock 5 (by decide)
  have currentSupported : current ∈ (app.roundsFrom startLaw schedule policy 142).support :=
    app.roundsFrom_runRounds schedule policy startLaw 137 5 origin current originSupported (by
      rw [bookkeeping]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have pending : current.network.pending = [firstPacket] := by
    rw [currentNetwork]
    exact first_pending before empty bit
  let included := app.processPendingHead current
  have chosen : schedule current.environmentRecall (current.observeEnvironment app) =
      PMF.pure (app.pendingHeadCommand (current.observeEnvironment app)) := by
    change PMF.pure (PeriodicService.command compiled (Equiv.refl Bool) leakRule
      current.environmentRecall.length (current.observeEnvironment app)) = _
    rw [currentLength]
    rfl
  have step : app.round schedule policy current = PMF.pure included := by
    rw [ReactiveApplication.round, chosen, PMF.pure_bind, app.processPendingHead_dispatch]
  have nextSupported : included ∈ (app.roundsFrom startLaw schedule policy 143).support := by
    change included ∈ (app.roundsFrom startLaw schedule policy (142 + 1)).support
    rw [ReactiveApplication.roundsFrom_succ, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨current, currentSupported, by
      rw [step]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  have afterConfig : current.application.config = startingApplication.config := by
    rw [currentState]
    exact config
  have afterAccepted : current.application.accepted = startingApplication.accepted := by
    rw [currentState]
    exact accepted
  have afterActivated : current.application.activatedAt = startingApplication.activatedAt := by
    rw [currentState]
    exact activated
  have afterClock : current.application.clock = 2 := by
    rw [currentState]
    rfl
  have afterResult : current.application.bindingResult (even, .prepared 0) BaseTy.bool =
      .success bit := by
    rw [currentState]
    exact first_bindingResult before application bit
  obtain ⟨next, handled, value⟩ := first_handle current afterConfig afterAccepted afterActivated
    afterClock bit afterResult
  have found : current.network.lookup firstPacket.id = some firstPacket := by
    simp [MessageNetwork.lookup, pending]
  refine ⟨included, nextSupported, ?_, ?_⟩
  · simp [included, ReactiveApplication.processPendingHead, pending, currentLength,
      ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
  · simp only [included, ReactiveApplication.processPendingHead, pending, List.head?_cons,
      ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
    rw [handled]
    exact value

end Vegas.Examples.OddsEvensLedgerClient
