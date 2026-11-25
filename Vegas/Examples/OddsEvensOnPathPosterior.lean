module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensFirstInclusion
public import Vegas.Examples.OddsEvensCommitmentObservation

@[expose] public section

/-! # The fair commitment lottery in the actual periodic Odds–Evens run -/

noncomputable section

namespace Vegas.Examples.OddsEvensLedgerClient

open OddsEvens EventGraphRuntime EventGraph Interaction GameTheory.Math.Probability

local notation "schedule" => OddsEvensService.scheduler
local notation "leakRule" => OddsEvensService.leaks
local notation "limits" => OddsEvensService.timeouts
local notation "startLaw" => OddsEvensService.initial
local notation "horizon" => OddsEvensService.horizon

private def fixedPlayers (bit : Bool) : Player → app.Policy :=
  Function.update (focalPlayers limits leakRule odd app.silentPolicy) even
    (decidedTurnPolicy limits leakRule (fun _ => 2) even (eventId 0) (some (.success bit)))

private def callback (execution : app.Execution) (who : Player) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
    [⟨execution.observeEnvironment app, .activate who⟩] }

private def fixedResponse (bit : Bool) : app.Action :=
  reactiveBinding limits leakRule even (eventId 0) BaseTy.bool (.success bit) 0

private theorem selected_callback_round (players : Player → app.Policy)
    (execution : app.Execution) (who : Player)
    (selected : schedule execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.activate who))
    (response : app.Action)
    (law : players who (execution.logs who) (execution.observe app who) = PMF.pure response) :
    app.round schedule players execution = PMF.pure ((callback execution who).respond app
      who response) := by
  have pendingObservation : app.observePending who execution.network.pending =
      PMF.pure (∅ : Finset (MessageId Player)) := rfl
  simp only [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, ReactiveApplication.Command.actor?,
    pendingObservation, PMF.pure_map, MessageNetwork.learn_empty, ReactiveApplication.resume]
  change app.invoke players who (callback execution who) = _
  unfold ReactiveApplication.invoke
  change (players who (execution.logs who) (execution.observe app who)).map _ = _
  rw [law, PMF.pure_map]

private theorem even_fixed_response (before : app.Execution)
    (prior : app.roundsFrom startLaw schedule policy 135 = PMF.pure before)
    (bit : Bool) :
    fixedPlayers bit even (before.logs even) (before.observe app even) =
      PMF.pure (fixedResponse bit) := by
  obtain ⟨_, state, _, _, logs⟩ := periodic_before_first_activation before prior
  let view := before.observe app even
  have ready : before.application.config.cut.Ready (eventId 0) := by rw [state]; decide
  have turn : view.application.publicView.ownTurn? even = some (eventId 0) :=
    before.application.ownTurn?_of_ready
      (setup.dataflowGraph.sequentialize_solitary _).ownerSolitary ready rfl
  have inactive : even ∉ view.application.publicView.observation.defaulted := by
    change even ∉ before.application.config.defaulted
    rw [state]
    decide
  have fits : view.application.publicView.InclusionFitsDeadline limits (fun _ => 2)
        (eventId 0) := by
    change before.application.publicView.InclusionFitsDeadline limits (fun _ => 2) (eventId 0)
    rw [state]
    exact (by decide : 1 - 0 + 2 < 6)
  have fresh : view.application.candidates
      (.prepared (view.application.publicView.bindingCount even)) = .fresh := by
    change before.application.candidates.lookup
      (even, .prepared (before.application.publicView.bindingCount even)) = .fresh
    rw [state]
    exact State.initial_candidate _ _ _
  have counted : view.application.publicView.bindingCount even = 0 := by
    change before.application.publicView.bindingCount even = 0
    rw [state]
    rfl
  have serial : canonicalFreshSlot even view.application = some 0 :=
    (canonicalFreshSlot_canonical even _ fresh).trans (congrArg some counted)
  have action : canonicalServiceDecision limits leakRule even (before.logs even) view
      (eventId 0) (some (.success bit)) = fixedResponse bit :=
    canonicalServiceDecision_binding limits leakRule even _ view (eventId 0) BaseTy.bool
      rfl rfl rfl inactive 0 serial (.success bit)
  have unrecorded : eventRecorded limits leakRule (before.logs even) (eventId 0) = false := by
    rw [logs]
    rfl
  have turnZero : turnIndex limits leakRule even (eventId 0) (before.logs even) view = some 0 := by
    rw [turnIndex, ite_eq_left turn, logs]
    rfl
  change fixedPlayers bit even (before.logs even) view = _
  simp only [fixedPlayers, Function.update_self, decidedTurnPolicy,
    ReactiveApplication.turnScheduledPolicy, turnZero, Fin.val_zero, ↓reduceIte, fixedOpportunity,
    unrecorded, Bool.false_eq_true, fits, action, fixedResponse, reactiveBinding, reduceCtorEq]

private theorem fixed_rounds137 (before : app.Execution)
    (prior : app.roundsFrom startLaw schedule policy 135 = PMF.pure before)
    (bit : Bool) :
    app.roundsFrom startLaw schedule (fixedPlayers bit) 137 =
      PMF.pure (firstOddIdleResponse before bit) := by
  obtain ⟨length, _⟩ := periodic_before_first_activation before prior
  let evenSent := (callback before even).respond app even (fixedResponse bit)
  have selectedEven : schedule before.environmentRecall (before.observeEnvironment app) =
      PMF.pure (.activate even) := by
    change PMF.pure (PeriodicService.command compiled (Equiv.refl Bool) leakRule
      before.environmentRecall.length (before.observeEnvironment app)) = _
    rw [length]
    rfl
  have evenLaw := selected_callback_round (fixedPlayers bit) before even selectedEven
    (fixedResponse bit) (even_fixed_response before prior bit)
  have afterEven : evenSent.environmentRecall.length = 136 := by
    change (before.environmentRecall ++
      [(⟨before.observeEnvironment app, .activate even⟩ : app.EnvironmentEntry)]).length = _
    simp [length]
  have selectedOdd : schedule evenSent.environmentRecall (evenSent.observeEnvironment app) =
      PMF.pure (.activate odd) := by
    change PMF.pure (PeriodicService.command compiled (Equiv.refl Bool) leakRule
      evenSent.environmentRecall.length (evenSent.observeEnvironment app)) = _
    rw [afterEven]
    rfl
  have silent : fixedPlayers bit odd (evenSent.logs odd) (evenSent.observe app odd) =
      PMF.pure ⟨none⟩ := by
    simp only [fixedPlayers, Function.update_of_ne (show odd ≠ even by decide)]
    rfl
  have oddLaw := selected_callback_round (fixedPlayers bit) evenSent odd selectedOdd ⟨none⟩ silent
  change app.roundsFrom startLaw schedule (fixedPlayers bit) (135 + 1 + 1) = _
  rw [ReactiveApplication.roundsFrom_succ, ReactiveApplication.roundsFrom_succ,
    periodic_first_activation_prior (fixedPlayers bit) before prior, PMF.pure_bind, evenLaw,
    PMF.pure_bind]
  exact oddLaw

private theorem runUntil_eq_runRounds_at_first_stop (players : Player → app.Policy)
    (stop : app.Execution → Prop) [DecidablePred stop]
    (count extra : Nat) (start : app.Execution)
    (before : ∀ cursor < count, ∀ current ∈ (app.runRounds schedule players cursor start).support,
      ¬ stop current)
    (after : ∀ current ∈ (app.runRounds schedule players count start).support, stop current) :
    app.runUntil schedule players stop (count + extra) start =
      app.runRounds schedule players count start := by
  induction count generalizing start with
  | zero =>
    simpa only [Nat.zero_add, ReactiveApplication.runRounds] using
      app.runUntil_of_stop schedule players stop extra start
        (after start ((PMF.mem_support_pure_iff _ _).mpr rfl))
  | succ count ih =>
    rw [show count + 1 + extra = (count + extra) + 1 by omega,
      ReactiveApplication.runUntil,
      ite_eq_right (before 0 (by omega) start ((PMF.mem_support_pure_iff _ _).mpr rfl)),
      ReactiveApplication.runRounds]
    apply bind_congr_on_support _
    intro middle firstStep
    have supports (cursor : Nat) (current : app.Execution)
        (reached : current ∈ (app.runRounds schedule players cursor middle).support) :
        current ∈ (app.runRounds schedule players (1 + cursor) start).support := by
      rw [ReactiveApplication.runRounds_add, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨middle, ?_, reached⟩
      simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using firstStep
    exact ih middle (fun cursor smaller current reached =>
      before (1 + cursor) (by omega) current (supports cursor current reached))
      (fun current reached => after current (by
        simpa only [Nat.add_comm] using supports count current reached))

private theorem fixed_stopped_at_inclusion (bit : Bool) (current included : app.Execution)
    (before : app.roundsFrom startLaw schedule (fixedPlayers bit) 142 = PMF.pure current)
    (incomplete : eventId 0 ∉ current.application.config.cut.completed)
    (after : app.roundsFrom startLaw schedule (fixedPlayers bit) 143 = PMF.pure included)
    (completed : eventId 0 ∈ included.application.config.cut.completed) :
    fixedFirstCommitmentRun bit = PMF.pure included := by
  have initial : startLaw = PMF.pure initialExecution.application := by
    change (PMF.pure _).map _ = _
    rw [PMF.pure_map]
    rfl
  have starts (count : Nat) :
      app.roundsFrom startLaw schedule (fixedPlayers bit) count =
        app.runRounds schedule (fixedPlayers bit) count initialExecution := by
    unfold ReactiveApplication.roundsFrom
    rw [initial, PMF.pure_bind]
    rfl
  rw [starts] at before after
  change app.runUntil schedule (fixedPlayers bit)
    (fun final => eventId 0 ∈ final.application.config.cut.completed) horizon initialExecution = _
  rw [← after]
  apply runUntil_eq_runRounds_at_first_stop _ _ 143 (horizon - 143)
  · intro cursor hCursor earlier reached done
    obtain ⟨later, last⟩ :=
      (app.runRounds schedule (fixedPlayers bit) (142 - cursor) earlier).support_nonempty
    have support : later ∈
        (app.runRounds schedule (fixedPlayers bit) 142 initialExecution).support := by
      rw [show 142 = cursor + (142 - cursor) by omega,
        app.runRounds_add, PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨earlier, reached, last⟩
    rw [before, PMF.mem_support_pure_iff] at support
    subst later
    exact incomplete (Config.Step.path_completed_mono
      (reactive_runRounds_graph_steps limits leakRule schedule (fixedPlayers bit)
        (142 - cursor) earlier current last) done)
  · intro final reached
    rw [after, PMF.mem_support_pure_iff] at reached
    exact reached ▸ completed

/-- The actual commitment lottery and the stopped fixed first commitments
reach the same two native executions, each after 143 scheduler rounds. -/
theorem periodic_fixed_commitment_branches :
    ∃ included : Bool → app.Execution,
      app.roundsFrom startLaw schedule policy 143 = (uniformLaw Bool).map included ∧
      ∀ bit, fixedFirstCommitmentRun bit = PMF.pure (included bit) ∧
        (included bit).environmentRecall.length = 143 ∧
        (included bit).application.clock = 2 ∧
        (included bit).application.activatedAt (eventId 1) = some 2 ∧
        (included bit).network.pending = [] ∧
        (∀ entry ∈ (included bit).logs odd,
          entry.beforeView.application.publicView.ownTurn? odd = none) := by
  obtain ⟨before, included, prior, actual, values, fixed⟩ := periodic_first_commitment_distribution
  refine ⟨included, actual, fun bit => ⟨?_, (values bit).1, (values bit).2.2⟩⟩
  obtain ⟨current, early, incomplete, completedLaw⟩ :=
    fixed (fixedPlayers bit) bit (fixed_rounds137 before prior bit)
  have completed : eventId 0 ∈ (included bit).application.config.cut.completed :=
    ((included bit).application.config.output_available _).mp (by rw [(values bit).2.1]; rfl)
  exact fixed_stopped_at_inclusion bit current (included bit) early incomplete completedLaw
    completed

/-- The actual two-branch commitment lottery has the exact initialized
execution law of the fixed first commitment experiments. -/
theorem periodic_commitment_law_eq_fixed :
    app.roundsFrom startLaw schedule policy 143 =
      (uniformLaw Bool).bind fixedFirstCommitmentRun := by
  obtain ⟨included, actual, stopped⟩ := periodic_fixed_commitment_branches
  rw [actual, PMF.map]
  apply bind_congr_on_support _
  intro bit _
  exact ((stopped bit).1).symm

/-- Conditioning the handwritten profile's actual run, immediately after
Even's first packet is included, leaves the committed bit fair at every
supported physical Odd observation. -/
theorem periodic_first_inclusion_posterior
    (observed : List app.PlayerEntry × app.PlayerView)
    (present :
      observed ∈ ((app.roundsFrom startLaw schedule policy 143).map oddObservation).support) :
    (fiberPosterior (app.roundsFrom startLaw schedule policy 143) oddObservation observed).map
      (fun execution => evenBinding.get? execution.application.config.store) =
      (uniformLaw Bool).map (fun bit => some (.success bit)) := by
  rw [periodic_commitment_law_eq_fixed] at present ⊢
  exact fixedFirstCommitment_posterior observed present

/-- Each stopped fixed commitment reaches the same scheduler boundary with
the queue empty and Odd's commitment newly activated. -/
theorem periodic_fixed_commitment_boundary (bit : Bool) (execution : app.Execution)
    (reached : execution ∈ (fixedFirstCommitmentRun bit).support) :
    execution.environmentRecall.length = 143 ∧ execution.application.clock = 2 ∧
      execution.application.activatedAt (eventId 1) = some 2 ∧
      execution.network.pending = [] := by
  obtain ⟨included, _, stopped⟩ := periodic_fixed_commitment_branches
  rw [(stopped bit).1, PMF.mem_support_pure_iff] at reached
  obtain ⟨_, length, clock, entered, queue, _⟩ := stopped bit
  exact reached ▸ ⟨length, clock, entered, queue⟩

/-- The initial Odd callback has taken place but selected no turn before
Even's first inclusion. -/
theorem periodic_fixed_commitment_odd_recall (bit : Bool) (execution : app.Execution)
    (reached : execution ∈ (fixedFirstCommitmentRun bit).support) :
    ∀ entry ∈ execution.logs odd,
      entry.beforeView.application.publicView.ownTurn? odd = none := by
  obtain ⟨included, _, stopped⟩ := periodic_fixed_commitment_branches
  rw [(stopped bit).1, PMF.mem_support_pure_iff] at reached
  obtain ⟨_, _, _, _, _, logTurn⟩ := stopped bit
  exact reached ▸ logTurn

end Vegas.Examples.OddsEvensLedgerClient
