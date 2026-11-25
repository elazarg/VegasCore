module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensOnPathPosterior

@[expose] public section

/-! # The periodic interval before Odd's ready commitment callback -/

noncomputable section

namespace Vegas.Examples.OddsEvensLedgerClient

open OddsEvens EventGraphRuntime EventGraph Interaction GameTheory.Math.Probability

local notation "schedule" => OddsEvensService.scheduler
local notation "leakRule" => OddsEvensService.leaks
local notation "horizon" => OddsEvensService.horizon
local notation "oddEvent" => eventId 1

private def withSchedulerCommand (execution : app.Execution) (command : app.Command) :
    app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
    [⟨execution.observeEnvironment app, command⟩] }

private theorem withSchedulerCommand_length (execution : app.Execution) (command : app.Command) :
    (withSchedulerCommand execution command).environmentRecall.length =
      execution.environmentRecall.length + 1 := by
  simp [withSchedulerCommand]

private theorem phase_commands (execution : app.Execution) (cursor : Nat)
    (index : execution.environmentRecall.length = cursor)
    (pending : execution.network.pending = []) (lower : 143 ≤ cursor) (upper : cursor < 278) :
    ∃ command, schedule execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure command ∧
      ((command = .wait ∧ cursor ≠ 212) ∨
        (∃ event, command = .application (.expire event) ∧ cursor < 212) ∨
        (command = .application .advanceClock ∧ cursor = 212) ∨
        (command = .activate even ∧ cursor = 277)) := by
  let view := execution.observeEnvironment app
  unfold OddsEvensService.scheduler
  rw [PeriodicService.scheduler, index]
  have wait : app.pendingHeadCommand view = .wait := by
    simp [view, ReactiveApplication.pendingHeadCommand,
      ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView, pending]
  by_cases firstQueue : cursor < 206
  · refine ⟨.wait, ?_, Or.inl ⟨rfl, by omega⟩⟩
    have selected := PeriodicService.processing_command (graph := compiled)
      (roster := Equiv.refl Bool) (leaks := leakRule) 2 (cursor - 142) view (by
        change cursor - 142 < 64
        omega)
    rw [show 2 * PeriodicService.width + (cursor - 142) = cursor by
      change 142 + (cursor - 142) = cursor
      omega] at selected
    exact congrArg PMF.pure (selected.trans wait)
  by_cases firstCycle : cursor < 213
  · interval_cases cursor
    · exact ⟨.wait, rfl, Or.inl ⟨rfl, by decide⟩⟩
    · exact ⟨.wait, rfl, Or.inl ⟨rfl, by decide⟩⟩
    · exact ⟨_, rfl, Or.inr (Or.inl ⟨eventId 0, rfl, by decide⟩)⟩
    · exact ⟨_, rfl, Or.inr (Or.inl ⟨eventId 1, rfl, by decide⟩)⟩
    · exact ⟨_, rfl, Or.inr (Or.inl ⟨eventId 2, rfl, by decide⟩)⟩
    · exact ⟨_, rfl, Or.inr (Or.inl ⟨eventId 3, rfl, by decide⟩)⟩
    · exact ⟨_, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  by_cases secondQueue : cursor < 277
  · refine ⟨.wait, ?_, Or.inl ⟨rfl, by omega⟩⟩
    have selected := PeriodicService.processing_command (graph := compiled)
      (roster := Equiv.refl Bool) (leaks := leakRule) 3 (cursor - 213) view (by
        change cursor - 213 < 64
        omega)
    rw [show 3 * PeriodicService.width + (cursor - 213) = cursor by
      change 213 + (cursor - 213) = cursor
      omega] at selected
    exact congrArg PMF.pure (selected.trans wait)
  interval_cases cursor
  exact ⟨_, rfl, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

private theorem commit_ready (bit : Bool) : (afterFirstCommitment bit).cut.Ready oddEvent := by
  cases bit <;> decide

private theorem quiet (bit : Bool) (state : EventGraphRuntime.State compiled)
    (config : state.config = afterFirstCommitment bit) :
    ∀ event, ¬ state.AutomaticReady event := by
  intro event automatic
  obtain ⟨owner, _, inactive⟩ := automatic.owned
  have noDefault : (afterFirstCommitment bit).defaulted = ∅ := by cases bit <;> decide
  rw [config, noDefault] at inactive
  exact Finset.notMem_empty _ inactive

private theorem even_idle (bit : Bool) (state : EventGraphRuntime.State compiled)
    (config : state.config = afterFirstCommitment bit) :
    state.publicView.ownTurn? even = none := by
  cases turn : state.publicView.ownTurn? even with
  | none => rfl
  | some event =>
    obtain ⟨ready, actor⟩ := state.publicView.ownTurn?_spec even event turn
    have named := setup.dataflowGraph.sequentialize_ready_unique state.config.cut
      ((state.publicView_eventReady event).mp ready) (config.symm ▸ commit_ready bit)
    subst event
    change some odd = some even at actor
    cases actor

private theorem expiry_idle (bit : Bool) (state : EventGraphRuntime.State compiled)
    (config : state.config = afterFirstCommitment bit) (clock : state.clock = 2)
    (event : compiled.EventId) :
    app.environment state (.expire event) = PMF.pure state := by
  change (environmentStep timeouts state (.expire event)).map State.drain = _
  have same : environmentStep timeouts state (.expire event) = PMF.pure state := by
    by_cases ready : state.config.cut.Ready event
    · cases entered : state.activatedAt event with
      | none => exact environmentStep_expire_of_not_activated timeouts state event ready entered
      | some current =>
        apply environmentStep_expire_of_not_due timeouts state event ready current entered
        apply Nat.not_le.mpr
        change state.clock - current < 6
        omega
    · exact environmentStep_expire_of_not_ready timeouts state event ready
  rw [same, PMF.pure_map, state.drain_eq_of_clear (quiet bit state config)]

private theorem even_silent (bit : Bool) (execution : app.Execution)
    (config : execution.application.config = afterFirstCommitment bit) :
    policy even (execution.logs even) (execution.observe app even) = PMF.pure ⟨none⟩ := by
  have idle := even_idle bit execution.application config
  simp only [policy, ReactiveApplication.ledgerPolicy, respond,
    ReactiveApplication.PlayerView.ledgerOnly]
  split
  · rfl
  · change (match execution.application.publicView.ownTurn? even with
      | none => PMF.pure (⟨none⟩ : app.Action)
      | some _ => _) = _
    rw [idle]

private theorem environment_round (players : Player → app.Policy)
    (execution : app.Execution) (command : EnvironmentCommand compiled)
    (state : EventGraphRuntime.State compiled)
    (chosen : schedule execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.application command))
    (result : app.environment execution.application command = PMF.pure state) :
    app.round schedule players execution =
      PMF.pure {withSchedulerCommand execution (.application command) with application := state} :=
  by
    simp only [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch,
      ReactiveApplication.Execution.environmentStep, result, PMF.pure_map,
      ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl

private theorem activation_round (players : Player → app.Policy)
    (execution : app.Execution) (who : Player)
    (chosen : schedule execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.activate who)) :
    app.round schedule players execution =
      (players who (execution.logs who) (execution.observe app who)).map
        ((withSchedulerCommand execution (.activate who)).respond app who) := by
  have noDelivery : app.observePending who execution.network.pending =
      PMF.pure (∅ : Finset (MessageId Player)) := rfl
  simp only [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, ReactiveApplication.Command.actor?,
    noDelivery, PMF.pure_map, MessageNetwork.learn_empty, ReactiveApplication.resume]
  rfl

private theorem interval_run (bit : Bool) (origin : app.Execution)
    (cursor : origin.environmentRecall.length = 143)
    (config : origin.application.config = afterFirstCommitment bit)
    (clock : origin.application.clock = 2)
    (pending : origin.network.pending = []) (count : Nat) (bound : count ≤ 135) :
    ∃ execution,
      (∀ players : Player → app.Policy,
        (∀ current : app.Execution, current.application.config = afterFirstCommitment bit →
          players even (current.logs even) (current.observe app even) = PMF.pure ⟨none⟩) →
        app.runRounds schedule players count origin = PMF.pure execution) ∧
      execution.environmentRecall.length = 143 + count ∧
      execution.application.config = afterFirstCommitment bit ∧
      execution.application.clock = (if 70 ≤ count then 3 else 2) ∧
      execution.network.pending = [] ∧ execution.logs odd = origin.logs odd := by
  induction count with
  | zero => exact ⟨origin, fun _ _ => rfl, cursor, config, clock, pending, rfl⟩
  | succ count ih =>
    obtain ⟨execution, law, length, state, elapsed, empty, logs⟩ := ih (by omega)
    obtain ⟨command, selected, kind⟩ := phase_commands execution (143 + count)
      length empty (by omega) (by omega)
    have step (players : Player → app.Policy) (silent :
        ∀ current : app.Execution, current.application.config = afterFirstCommitment bit →
          players even (current.logs even) (current.observe app even) = PMF.pure ⟨none⟩) :
        app.runRounds schedule players (count + 1) origin = app.round schedule players execution :=
      by
        rw [app.runRounds_add schedule players count 1 origin, law players silent, PMF.pure_bind]
        simp only [ReactiveApplication.runRounds, PMF.bind_pure]
    have next_length (command : app.Command) :
        (withSchedulerCommand execution command).environmentRecall.length = 143 + (count + 1) := by
      rw [withSchedulerCommand_length, length]
      omega
    have sameClock (notTick : 143 + count ≠ 212) :
        execution.application.clock = (if 70 ≤ count + 1 then 3 else 2) := by
      rw [elapsed]
      have same : (70 ≤ count) = (70 ≤ count + 1) := propext (by omega)
      simp [same]
    rcases kind with ⟨rfl, notTick⟩ | ⟨event, rfl, beforeTick⟩ |
      ⟨rfl, atTick⟩ | ⟨rfl, atEven⟩
    · refine ⟨withSchedulerCommand execution .wait, ?_, next_length _, state,
        sameClock notTick, empty, logs⟩
      intro players silent
      rw [step players silent]
      simp only [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume]
      rfl
    · have now : execution.application.clock = 2 := by
        rw [elapsed, ite_eq_right (by omega)]
      have result := expiry_idle bit execution.application state now event
      refine ⟨withSchedulerCommand execution (.application (.expire event)), ?_, next_length _,
        state, sameClock (by omega), empty, logs⟩
      intro players silent
      rw [step players silent, environment_round _ _ _ _ selected result]
      rfl
    · have now : execution.application.clock = 2 := by
        rw [elapsed, ite_eq_right (by omega)]
      have result := reactiveApplication_tick_eq_pure timeouts leakRule execution.application
        (quiet bit execution.application state)
      refine ⟨{ withSchedulerCommand execution (.application .advanceClock) with
        application := {execution.application with clock := execution.application.clock + 1} },
        ?_, next_length _, state, ?_, empty, logs⟩
      · intro players silent
        rw [step players silent, environment_round _ _ _ _ selected result]
      · change execution.application.clock + 1 = _
        rw [now, ite_eq_left (by omega)]
    · let middle := withSchedulerCommand execution (.activate even)
      let next := middle.respond app even ⟨none⟩
      have remembered := app.respond_recall_other middle even odd (by decide) ⟨none⟩
      have same : next.logs odd = origin.logs odd := remembered.trans logs
      refine ⟨next, ?_, next_length _, state, sameClock (by omega), empty, same⟩
      intro players silent
      rw [step players silent, activation_round _ _ _ selected, silent execution state,
        PMF.pure_map]

abbrev quietPlayers : Player → app.Policy :=
  focalPlayers timeouts leakRule odd app.silentPolicy

private theorem quiet_even (execution : app.Execution) :
    quietPlayers even (execution.logs even) (execution.observe app even) = PMF.pure ⟨none⟩ := by
  simp only [quietPlayers, focalPlayers, Function.update_of_ne (show even ≠ odd by decide)]
  rfl

/-- From the first successful inclusion, the handwritten client and the silent
profile reach the same idle boundary just before the next Odd activation.
The pending queue stays empty and Odd's preceding callback recall is unchanged. -/
theorem readyCommitmentInterval (bit : Bool) (origin : app.Execution)
    (cursor : origin.environmentRecall.length = 143)
    (config : origin.application.config = afterFirstCommitment bit)
    (clock : origin.application.clock = 2) (pending : origin.network.pending = []) :
    ∃ execution,
      app.runRounds schedule policy 135 origin = PMF.pure execution ∧
      app.runRounds schedule quietPlayers 135 origin = PMF.pure execution ∧
      execution.environmentRecall.length = 278 ∧
      execution.application.config = afterFirstCommitment bit ∧
      execution.application.clock = 3 ∧
      execution.network.pending = [] ∧ execution.logs odd = origin.logs odd := by
  obtain ⟨execution, law, length, state, elapsed, empty, logs⟩ :=
    interval_run bit origin cursor config clock pending 135 le_rfl
  exact ⟨execution, law policy (even_silent bit), law quietPlayers (fun current _ =>
    quiet_even current), length, state, elapsed, empty, logs⟩

private theorem interval_traffic (leftBit rightBit : Bool) (left right : app.Execution)
    (lc : left.environmentRecall.length = 143) (rc : right.environmentRecall.length = 143)
    (ls : left.application.config = afterFirstCommitment leftBit)
    (rs : right.application.config = afterFirstCommitment rightBit)
    (lt : left.application.clock = 2) (rt : right.application.clock = 2)
    (lp : left.network.pending = []) (rp : right.network.pending = [])
    (equal : bindingTraffic timeouts leakRule odd left =
      bindingTraffic timeouts leakRule odd right)
    (count : Nat) (bound : count ≤ 135) :
    (app.runRounds schedule quietPlayers count left).map (bindingTraffic timeouts leakRule odd) =
      (app.runRounds schedule quietPlayers count right).map
        (bindingTraffic timeouts leakRule odd) := by
  induction count with
  | zero =>
    simpa only [ReactiveApplication.runRounds, PMF.pure_map] using congrArg PMF.pure equal
  | succ count ih =>
    obtain ⟨next, leftLaw, _, nextState, _, _, _⟩ := interval_run
      leftBit left lc ls lt lp count (by omega)
    obtain ⟨other, rightLaw, _, otherState, _, _, _⟩ := interval_run
      rightBit right rc rs rt rp count (by omega)
    have leftPure := leftLaw quietPlayers (fun execution _ => quiet_even execution)
    have rightPure := rightLaw quietPlayers (fun execution _ => quiet_even execution)
    have paired := ih (by omega)
    rw [leftPure, rightPure, PMF.pure_map, PMF.pure_map] at paired
    have same : bindingTraffic timeouts leakRule odd next =
        bindingTraffic timeouts leakRule odd other := by
      have member : bindingTraffic timeouts leakRule odd next ∈
          (PMF.pure (bindingTraffic timeouts leakRule odd next)).support :=
        (PMF.mem_support_pure_iff _ _).mpr rfl
      rwa [paired, PMF.mem_support_pure_iff] at member
    have focal (bit : Bool) (execution : app.Execution)
        (config : execution.application.config = afterFirstCommitment bit)
        (event : compiled.EventId) (ready : execution.application.config.cut.Ready event) :
        compiled.actor? event = none ∨ compiled.actor? event = some odd := by
      have named := setup.dataflowGraph.sequentialize_ready_unique
        execution.application.config.cut ready (config.symm ▸ commit_ready bit)
      subst event
      exact Or.inr rfl
    rw [app.runRounds_add schedule quietPlayers count 1 left,
      app.runRounds_add schedule quietPlayers count 1 right,
      leftPure, rightPure, PMF.pure_bind, PMF.pure_bind]
    simp only [ReactiveApplication.runRounds, PMF.bind_pure]
    exact focalRound_traffic_congr schedule odd app.silentPolicy
      (focal leftBit next nextState) (focal rightBit other otherState) same

/-- The actual next environment command activates Odd at its ready
commitment. No pending packet is delivered, so its view and preceding
recall agree exactly with the idle scheduler boundary. -/
theorem oddReadyActivation (bit : Bool) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 278)
    (config : execution.application.config = afterFirstCommitment bit) :
    ∃ activated,
      schedule execution.environmentRecall (execution.observeEnvironment app) =
        PMF.pure (.activate odd) ∧
      execution.environmentStep app (.activate odd) = PMF.pure activated ∧
      oddObservation activated = oddObservation execution ∧
      (activated.observe app odd).application.publicView.ownTurn? odd = some oddEvent ∧
      activated.application.config = afterFirstCommitment bit := by
  refine ⟨withSchedulerCommand execution (.activate odd), ?_, ?_, rfl, ?_, config⟩
  · change PMF.pure (PeriodicService.command compiled (Equiv.refl Bool) leakRule
      execution.environmentRecall.length (execution.observeEnvironment app)) = _
    rw [cursor]
    rfl
  · have noDelivery : app.observePending odd execution.network.pending =
        PMF.pure (∅ : Finset (MessageId Player)) := rfl
    simp only [ReactiveApplication.Execution.environmentStep, noDelivery, PMF.pure_map,
      MessageNetwork.learn_empty]
    rfl
  · exact execution.application.ownTurn?_of_ready
      (setup.dataflowGraph.sequentialize_solitary _).ownerSolitary
      (config.symm ▸ commit_ready bit) rfl

/-- The continuation from the fixed successful commitment through the actual
handwritten profile to the idle boundary before Odd's ready activation. -/
def oddReadyCommitmentRun (bit : Bool) : PMF app.Execution :=
  (fixedFirstCommitmentRun bit).bind (app.runRounds schedule policy 135)

private theorem readyRun_map_traffic (metadata : ∀ bit execution,
    execution ∈ (fixedFirstCommitmentRun bit).support →
      execution.environmentRecall.length = 143 ∧ execution.application.clock = 2 ∧
        execution.network.pending = []) :
    (oddReadyCommitmentRun false).map (bindingTraffic timeouts leakRule odd) =
      (oddReadyCommitmentRun true).map (bindingTraffic timeouts leakRule odd) := by
  let traffic := bindingTraffic timeouts leakRule odd
  unfold oddReadyCommitmentRun
  simp only [PMF.map_bind]
  apply bind_eq_of_map_eq _ _ traffic traffic fixedFirstCommitmentRun_traffic
  intro left leftPresent right rightPresent equal
  obtain ⟨lc, lt, lp⟩ := metadata false left leftPresent
  obtain ⟨rc, rt, rp⟩ := metadata true right rightPresent
  have ls := fixedFirstCommitmentRun_config false left leftPresent
  have rs := fixedFirstCommitmentRun_config true right rightPresent
  obtain ⟨leftReady, actualL, quietL, _⟩ := readyCommitmentInterval false left lc ls lt lp
  obtain ⟨rightReady, actualR, quietR, _⟩ := readyCommitmentInterval true right rc rs rt rp
  rw [actualL, actualR, ← quietL, ← quietR]
  exact interval_traffic false true left right lc rc ls rs lt rt lp rp equal 135 le_rfl

/-- At the actual next ready activation the two first-commitment branches
induce the same law of Odd's full recall and observation. -/
theorem oddReadyCommitmentRun_observation (metadata : ∀ bit execution,
    execution ∈ (fixedFirstCommitmentRun bit).support →
      execution.environmentRecall.length = 143 ∧ execution.application.clock = 2 ∧
        execution.network.pending = []) :
    (oddReadyCommitmentRun false).map oddObservation =
      (oddReadyCommitmentRun true).map oddObservation := by
  let observeTraffic := fun read : MessageNetwork Player app.Payload ×
      List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
        PlayerView compiled × PublicView compiled => (read.2.2.2.1,
    (⟨read.1.observe odd, read.2.2.2.2.1, read.2.1⟩ : app.PlayerView))
  have projected := congrArg (PMF.map observeTraffic) (readyRun_map_traffic metadata)
  rw [PMF.map_comp, PMF.map_comp] at projected
  exact projected

/-- Every supported branch reaches an actual ready Odd callback with Even's
chosen bit intact. -/
theorem oddReadyCommitmentRun_support (metadata : ∀ bit execution,
    execution ∈ (fixedFirstCommitmentRun bit).support →
      execution.environmentRecall.length = 143 ∧ execution.application.clock = 2 ∧
        execution.network.pending = [])
    (bit : Bool) (execution : app.Execution)
    (reached : execution ∈ (oddReadyCommitmentRun bit).support) :
    execution.environmentRecall.length = 278 ∧
      execution.application.config = afterFirstCommitment bit ∧
      evenBinding.get? execution.application.config.store = some (.success bit) := by
  obtain ⟨start, supported, stopped⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨cursor, clock, pending⟩ := metadata bit start supported
  have config := fixedFirstCommitmentRun_config bit start supported
  obtain ⟨ready, law, _, length, state, _⟩ :=
    readyCommitmentInterval bit start cursor config clock pending
  rw [law, PMF.mem_support_pure_iff] at stopped
  subst execution
  refine ⟨length, state, ?_⟩
  rw [state, ← config]
  exact fixedFirstCommitmentRun_stored bit start supported

private theorem fixed_boundary_metadata (bit : Bool) (execution : app.Execution)
    (supported : execution ∈ (fixedFirstCommitmentRun bit).support) :
    execution.environmentRecall.length = 143 ∧ execution.application.clock = 2 ∧
      execution.network.pending = [] := by
  obtain ⟨length, clock, _, pending⟩ :=
    periodic_fixed_commitment_boundary bit execution supported
  exact ⟨length, clock, pending⟩

local notation "startLaw" => OddsEvensService.initial

/-- The actual handwritten client reaches the idle boundary preceding the
ready Odd activation with the fair ordinary commitment mixture. -/
theorem periodic_ready_commitment_law :
    app.roundsFrom startLaw schedule policy 278 =
      (uniformLaw Bool).bind oddReadyCommitmentRun := by
  have split : app.roundsFrom startLaw schedule policy 278 =
      (app.roundsFrom startLaw schedule policy 143).bind
        (app.runRounds schedule policy 135) := by
    change app.roundsFrom startLaw schedule policy (143 + 135) = _
    unfold ReactiveApplication.roundsFrom
    rw [PMF.bind_bind]
    apply bind_congr_on_support _
    intro state _
    exact app.runRounds_add schedule policy 143 135
      (ReactiveApplication.Execution.initial app state)
  rw [split, periodic_commitment_law_eq_fixed, PMF.bind_bind]
  rfl

/-- The scheduler reaches Odd's ready commitment callback on every supported
execution. Its current view and full preceding recall are already determined
at the immediately preceding idle boundary. -/
theorem periodic_ready_commitment_activation (execution : app.Execution)
    (reached : execution ∈ (app.roundsFrom startLaw schedule policy 278).support) :
    ∃ activated,
      schedule execution.environmentRecall (execution.observeEnvironment app) =
        PMF.pure (.activate odd) ∧
      execution.environmentStep app (.activate odd) = PMF.pure activated ∧
      oddObservation activated = oddObservation execution ∧
      (activated.observe app odd).application.publicView.ownTurn? odd = some (eventId 1) ∧
      (∀ entry ∈ activated.logs odd,
        entry.beforeView.application.publicView.ownTurn? odd = none) := by
  rw [periodic_ready_commitment_law] at reached
  obtain ⟨bit, _, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨start, initialSupported, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨length, clock, pending⟩ := fixed_boundary_metadata bit start initialSupported
  obtain ⟨boundary, law, _, cursor, config, _, _, logs⟩ := readyCommitmentInterval
    bit start length (fixedFirstCommitmentRun_config bit start initialSupported) clock pending
  rw [law, PMF.mem_support_pure_iff] at moved
  subst execution
  obtain ⟨activated, selected, activatedLaw, observed, ready, _⟩ :=
    oddReadyActivation bit boundary cursor config
  have prior : activated.logs odd = start.logs odd :=
    (congrArg Prod.fst observed).trans logs
  refine ⟨activated, selected, activatedLaw, observed, ready, ?_⟩
  intro entry member
  rw [prior] at member
  exact periodic_fixed_commitment_odd_recall bit start initialSupported entry member

/-- Conditioning on the full observation at the boundary immediately before
Odd's ready callback leaves Even's actual committed bit fair. The activation
itself produces this same recall and view. -/
theorem periodic_ready_commitment_posterior
    (observed : List app.PlayerEntry × app.PlayerView)
    (present :
      observed ∈ ((app.roundsFrom startLaw schedule policy 278).map oddObservation).support) :
    (fiberPosterior (app.roundsFrom startLaw schedule policy 278) oddObservation observed).map
      (fun execution => evenBinding.get? execution.application.config.store) =
      (uniformLaw Bool).map (fun bit => some (.success bit)) := by
  rw [periodic_ready_commitment_law] at present ⊢
  exact fiberPosterior_evenBinding_of_equal_observations oddReadyCommitmentRun
    (oddReadyCommitmentRun_observation fixed_boundary_metadata)
    (fun bit execution supported =>
      (oddReadyCommitmentRun_support fixed_boundary_metadata bit execution supported).2.2)
    observed present

/-- The actual first ready Odd callback law, with the scheduler command
applied before Odd draws a response. -/
def periodicReadyOddCallback : PMF app.Execution :=
  (app.roundsFrom startLaw schedule policy 278).bind fun execution =>
    execution.environmentStep app (.activate odd)

private theorem readyCallbackLaw_eq :
    periodicReadyOddCallback =
      (uniformLaw Bool).bind fun bit =>
        (oddReadyCommitmentRun bit).bind fun execution =>
          execution.environmentStep app (.activate odd) := by
  unfold periodicReadyOddCallback
  rw [periodic_ready_commitment_law, PMF.bind_bind]

/-- The full observation at the actual first ready Odd callback preserves
Even's fair commitment posterior. -/
theorem periodic_ready_odd_callback_posterior
    (observed : List app.PlayerEntry × app.PlayerView)
    (present : observed ∈ (periodicReadyOddCallback.map oddObservation).support) :
    (fiberPosterior periodicReadyOddCallback oddObservation observed).map
      (fun execution => evenBinding.get? execution.application.config.store) =
      (uniformLaw Bool).map (fun bit => some (.success bit)) := by
  let branch := fun bit =>
    (oddReadyCommitmentRun bit).bind fun execution => execution.environmentStep app (.activate odd)
  have same (bit : Bool) :
      (branch bit).map oddObservation = (oddReadyCommitmentRun bit).map oddObservation := by
    unfold branch
    rw [PMF.map_bind, ← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro boundary supported
    obtain ⟨cursor, config, _⟩ := oddReadyCommitmentRun_support fixed_boundary_metadata
      bit boundary supported
    obtain ⟨activated, _, law, readout, _, _⟩ := oddReadyActivation bit boundary cursor config
    rw [law, PMF.pure_map, readout]
    rfl
  have stored (bit : Bool) (execution : app.Execution)
      (supported : execution ∈ (branch bit).support) :
      evenBinding.get? execution.application.config.store = some (.success bit) := by
    obtain ⟨boundary, reached, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    obtain ⟨cursor, config, value⟩ := oddReadyCommitmentRun_support fixed_boundary_metadata
      bit boundary reached
    obtain ⟨activated, _, law, _, _, activeConfig⟩ :=
      oddReadyActivation bit boundary cursor config
    rw [law, PMF.mem_support_pure_iff] at moved
    subst execution
    rw [activeConfig, ← config]
    exact value
  rw [readyCallbackLaw_eq] at present ⊢
  exact fiberPosterior_evenBinding_of_equal_observations branch
    ((same false).trans ((oddReadyCommitmentRun_observation fixed_boundary_metadata).trans
      (same true).symm)) stored observed present

end Vegas.Examples.OddsEvensLedgerClient
