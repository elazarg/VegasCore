import Vegas.Machine.MessageInFlight
import Vegas.Examples.BoolMessage

/-!
# Message-in-flight runtime refinement examples

Property boundary: these examples prove runtime refinement and payoff/Nash
preservation for inert message coordinates, not that message leaks are
strategically harmless in every protocol.

This module instantiates the message-in-flight machine wrapper on the Bool
fixture. The implementation state contains a pending queue and a delivered log;
send/deliver events project away, while the underlying source action projects
to the primitive Bool move.
-/

namespace Vegas

open GameTheory

namespace Examples
namespace Refinement

noncomputable def boolMessageInFlightMachine : Machine PUnit :=
  Machine.messageInFlight boolSpecMachine (fun _ : PUnit => Bool)

noncomputable def boolMessageInFlightRefinement :
    Machine.StochasticRefinement boolMessageInFlightMachine boolSpecMachine :=
  Machine.messageInFlight.refinement boolSpecMachine (fun _ : PUnit => Bool)

noncomputable def boolMessageInFlightLawFamily :
    boolMessageInFlightMachine.EventBatchLawFamily
      (fun _ : PUnit => Bool × Bool) where
  law := fun profile trace =>
    let message := (profile PUnit.unit).1
    let action := (profile PUnit.unit).2
    PMF.pure
      (Machine.messageInFlight.deliverAllThenEvents boolSpecMachine
          (fun _ : PUnit => Bool) trace.2.pending
        [.play PUnit.unit (.send message),
          .internal .deliver,
          .play PUnit.unit (.spec action)])
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨sourceState, pending, delivered⟩
    let message := (profile PUnit.unit).1
    let action := (profile PUnit.unit).2
    change batch ∈
      (PMF.pure
        (Machine.messageInFlight.deliverAllThenEvents boolSpecMachine
            (fun _ : PUnit => Bool) pending
          [.play PUnit.unit (.send message),
            .internal .deliver,
            .play PUnit.unit (.spec action)])).support at hbatch
    have hbatch_eq :
        batch =
          Machine.messageInFlight.deliverAllThenEvents boolSpecMachine
            (fun _ : PUnit => Bool) pending
            [.play PUnit.unit (.send message),
              .internal .deliver,
              .play PUnit.unit (.spec action)] := by
      simp only [PMF.support_pure] at hbatch
      exact hbatch
    subst batch
    cases sourceState with
    | none =>
        have hsourceBatch :
            boolSpecMachine.AvailableBatchFrom none
              [.play PUnit.unit action] :=
          Machine.AvailableBatchFrom.singleton
            (by
              change action ∈ Set.univ
              exact Set.mem_univ action)
        simpa [boolMessageInFlightMachine,
          Machine.messageInFlight.liftEvent] using
          Machine.messageInFlight.deliverAllThenSendDeliverLiftAvailableBatchFrom
            boolSpecMachine (fun _ : PUnit => Bool) pending delivered
            PUnit.unit message (by simp [boolSpecMachine]) hsourceBatch
    | some value =>
        exact False.elim
          (hnonterminal (by
            cases value <;>
              simp [boolMessageInFlightMachine, Machine.messageInFlight,
                boolSpecMachine]))

noncomputable def boolMessageInFlightLawLift :
    boolMessageInFlightRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × Bool)
      boolMessageSpecInertLawFamily.enriched where
  impl := boolMessageInFlightLawFamily
  compatible := by
    intro profile trace
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨sourceState, pending, delivered⟩
    change
      PMF.map (Machine.messageInFlight.projectEventBatch
          boolSpecMachine (fun _ : PUnit => Bool))
          (PMF.pure
            (Machine.messageInFlight.deliverAllThenEvents boolSpecMachine
                (fun _ : PUnit => Bool) pending
              [.play PUnit.unit (.send (profile PUnit.unit).1),
                .internal .deliver,
                .play PUnit.unit (.spec (profile PUnit.unit).2)])) =
        PMF.pure [.play PUnit.unit (profile PUnit.unit).2]
    rw [PMF.pure_map]
    rw [Machine.messageInFlight.projectEventBatch_deliverAllThenEvents]
    rfl

example (message action : Bool) :
    boolMessageInFlightRefinement.projectEventBatch
        [.play PUnit.unit (.send message),
          .internal .deliver,
          .play PUnit.unit (.spec action)] =
      [.play PUnit.unit action] := by
  rfl

theorem boolMessageInFlight_terminal_spec_unavailable_with_pending
    (message action : Bool) :
    Machine.MessageInFlightAction.spec action ∉
      boolMessageInFlightMachine.available
        { source := none,
          pending := [⟨PUnit.unit, message⟩],
          delivered := [] }
        PUnit.unit := by
  intro havailable
  let sent : Sigma (fun _ : PUnit => Bool) := ⟨PUnit.unit, message⟩
  let afterSend : boolMessageInFlightMachine.State :=
    { source := none,
      pending := [sent],
      delivered := [] }
  change action ∈ boolSpecMachine.available none PUnit.unit ∧
      (afterSend.pending = [] ∨
        ∀ target,
          target ∈ (boolSpecMachine.stepPlay PUnit.unit action none).support →
            ¬ boolSpecMachine.terminal target) at havailable
  rcases havailable with ⟨_, hqueue⟩
  cases hqueue with
  | inl hempty =>
      cases hempty
  | inr hnonterminal =>
      have hsupportAction :
          some action ∈
            (boolSpecMachine.stepPlay PUnit.unit action none).support := by
        change some action ∈ (PMF.pure (some action)).support
        rw [PMF.support_pure]
        exact Set.mem_singleton _
      have hterminal : boolSpecMachine.terminal (some action) := by
        cases action <;> simp [boolSpecMachine]
      exact hnonterminal (some action) hsupportAction hterminal

theorem boolMessageInFlight_send_terminal_without_delivery_unavailable
    (message action : Bool) :
    ¬ ∃ dst, boolMessageInFlightMachine.AvailableRunFrom
      boolMessageInFlightMachine.init
      [.play PUnit.unit (.send message),
        .play PUnit.unit (.spec action)]
      dst := by
  rintro ⟨dst, hrun⟩
  let sent : Sigma (fun _ : PUnit => Bool) := ⟨PUnit.unit, message⟩
  let afterSend : boolMessageInFlightMachine.State :=
    { source := none,
      pending := [sent],
      delivered := [] }
  change
    boolMessageInFlightMachine.AvailableRunFrom
      { source := none, pending := [], delivered := [] }
      [.play PUnit.unit (.send message),
        .play PUnit.unit (.spec action)]
      dst at hrun
  rcases Machine.AvailableRunFrom.cons_inv hrun with
    ⟨mid, _hsendAvailable, hsendSupport, htail⟩
  have hmid : mid = afterSend := by
    change mid ∈ (PMF.pure afterSend).support at hsendSupport
    rw [PMF.support_pure, Set.mem_singleton_iff] at hsendSupport
    exact hsendSupport
  subst mid
  rcases Machine.AvailableRunFrom.cons_inv htail with
    ⟨_, hspecAvailable, _, _⟩
  change Machine.MessageInFlightAction.spec action ∈
    boolMessageInFlightMachine.available afterSend PUnit.unit at hspecAvailable
  exact
    boolMessageInFlight_terminal_spec_unavailable_with_pending
      message action (by simpa [afterSend, sent] using hspecAvailable)

example (profile : ∀ _player : PUnit, Bool × Bool) :
    PMF.map boolMessageInFlightRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            boolMessageInFlightMachine (fun _ : PUnit => Bool × Bool)
            boolMessageInFlightLawLift.impl (fun _ => 0) 2).outcomeKernel
          profile) =
      ((Machine.eventBatchTraceKernelGame
          boolSpecMachine (fun _ : PUnit => Bool × Bool)
          boolMessageSpecInertLawFamily.enriched
          (fun _ => 0) 2).outcomeKernel profile) :=
  boolMessageInFlightRefinement.eventBatchTraceKernelGame_projectTrace_eq
    boolMessageInFlightLawLift (fun _ => 0) 2 profile

theorem boolMessageInFlightTraceUtility_bound
    (player : PUnit) (trace : boolMessageInFlightMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility boolMessageInFlightMachine (fun _ => 0)
        trace player| ≤ 1 := by
  cases player
  rcases trace with ⟨batches, state⟩
  rcases state with ⟨sourceState, pending, delivered⟩
  cases sourceState with
  | none =>
      simp [Machine.eventBatchTraceUtility, boolMessageInFlightMachine,
        Machine.messageInFlight, Machine.RoundView.optionOutcomeUtility,
        boolSpecMachine]
  | some value =>
      cases value <;>
        simp [Machine.eventBatchTraceUtility, boolMessageInFlightMachine,
          Machine.messageInFlight, Machine.RoundView.optionOutcomeUtility,
          boolSpecMachine]

example (message : Bool) :
    (Machine.eventBatchTraceKernelGame
        boolMessageInFlightMachine (fun _ : PUnit => Bool × Bool)
        boolMessageInFlightLawLift.impl (fun _ => 0) 2).IsNash
      (fun _ : PUnit => (message, true)) := by
  exact
    boolMessageInFlightRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_inert_projected_nash
        boolMessageSpecInertLawFamily boolMessageInFlightLawLift
        (fun _ => 0) 2
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        boolMessageInFlightTraceUtility_bound boolSpecTraceUtility_bound
        boolSpecTraceGame_true_nash

/-! ## Delayed delivery across an event-batch checkpoint -/

noncomputable def boolDelayedSpecLawFamily :
    boolSpecMachine.EventBatchLawFamily (fun _ : PUnit => Bool) where
  law := fun profile trace =>
    match trace.1 with
    | [] => PMF.pure []
    | _ :: _ => PMF.pure [.play PUnit.unit (profile PUnit.unit)]
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    cases batches with
    | nil =>
        rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
        subst batch
        exact Machine.AvailableBatchFrom.nil _
    | cons first rest =>
        rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
        subst batch
        cases state with
        | none =>
            exact Machine.AvailableBatchFrom.singleton
              (by simp [boolSpecMachine])
        | some value =>
            exact False.elim (hnonterminal (by
              cases value <;> simp [boolSpecMachine]))

noncomputable def boolDelayedMessageSpecLawFamily :
    boolSpecMachine.EventBatchLawFamily
      (fun _ : PUnit => Bool × Bool) where
  law := fun profile =>
    boolDelayedSpecLawFamily.law (fun player => (profile player).2)
  legal := fun profile =>
    boolDelayedSpecLawFamily.legal (fun player => (profile player).2)

noncomputable def boolDelayedMessageSpecInertLawFamily :
    Machine.StrategyInertLawFamily boolSpecMachine
      (fun _ : PUnit => Bool) (fun _ : PUnit => Bool × Bool)
      boolDelayedSpecLawFamily where
  proj := fun _ strategy => strategy.2
  embed := fun _ strategy => (false, strategy)
  section_proj := by
    intro player strategy
    rfl
  enriched := boolDelayedMessageSpecLawFamily
  law_inert := by
    intro profile
    rfl

noncomputable def boolMessageInFlightDelayedLawFamily :
    boolMessageInFlightMachine.EventBatchLawFamily
      (fun _ : PUnit => Bool × Bool) where
  law := fun profile trace =>
    let message := (profile PUnit.unit).1
    let action := (profile PUnit.unit).2
    match trace.1 with
    | [] => PMF.pure [.play PUnit.unit (.send message)]
    | _ :: _ =>
        PMF.pure
          (Machine.messageInFlight.deliverAllThenEvents boolSpecMachine
              (fun _ : PUnit => Bool) trace.2.pending
            [.play PUnit.unit (.spec action)])
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨sourceState, pending, delivered⟩
    let message := (profile PUnit.unit).1
    let action := (profile PUnit.unit).2
    cases batches with
    | nil =>
        change batch ∈
          (PMF.pure [.play PUnit.unit (.send message)]).support
          at hbatch
        rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
        subst batch
        cases sourceState with
        | none =>
            let src : boolMessageInFlightMachine.State :=
              { source := none,
                pending := pending,
                delivered := delivered }
            exact Machine.AvailableBatchFrom.singleton
              (by
                change Machine.MessageInFlightAction.send message ∈
                boolMessageInFlightMachine.available src PUnit.unit
                change ¬ boolSpecMachine.terminal none
                simp [boolSpecMachine])
        | some value =>
            exact False.elim (hnonterminal (by
              cases value <;>
                simp [boolMessageInFlightMachine, Machine.messageInFlight,
                  boolSpecMachine]))
    | cons first restBatches =>
        change batch ∈
          (PMF.pure
            (Machine.messageInFlight.deliverAllThenEvents boolSpecMachine
                (fun _ : PUnit => Bool) pending
              [.play PUnit.unit (.spec action)])).support
          at hbatch
        have hbatch_eq :
            batch =
              Machine.messageInFlight.deliverAllThenEvents boolSpecMachine
                (fun _ : PUnit => Bool) pending
                [.play PUnit.unit (.spec action)] := by
          simp only [PMF.support_pure] at hbatch
          exact hbatch
        subst batch
        cases sourceState with
        | none =>
            have hsourceBatch :
                boolSpecMachine.AvailableBatchFrom none
                  [.play PUnit.unit action] :=
              Machine.AvailableBatchFrom.singleton
                (by
                  change action ∈ Set.univ
                  exact Set.mem_univ action)
            simpa [boolMessageInFlightMachine,
              Machine.messageInFlight.liftEvent] using
              Machine.messageInFlight.deliverAllThenLiftAvailableBatchFrom
                boolSpecMachine (fun _ : PUnit => Bool)
                pending delivered (by simp [boolSpecMachine]) hsourceBatch
        | some value =>
            exact False.elim (hnonterminal (by
              cases value <;>
                simp [boolMessageInFlightMachine, Machine.messageInFlight,
                  boolSpecMachine]))

noncomputable def boolMessageInFlightDelayedLawLift :
    boolMessageInFlightRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × Bool)
      boolDelayedMessageSpecInertLawFamily.enriched where
  impl := boolMessageInFlightDelayedLawFamily
  compatible := by
    intro profile trace
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨sourceState, pending, delivered⟩
    cases batches with
    | nil =>
        change
          PMF.map (Machine.messageInFlight.projectEventBatch
              boolSpecMachine (fun _ : PUnit => Bool))
              (PMF.pure
                [.play PUnit.unit (.send (profile PUnit.unit).1)]) =
            PMF.pure []
        rw [PMF.pure_map]
        rfl
    | cons first restBatches =>
        change
          PMF.map (Machine.messageInFlight.projectEventBatch
              boolSpecMachine (fun _ : PUnit => Bool))
              (PMF.pure
                (Machine.messageInFlight.deliverAllThenEvents boolSpecMachine
                    (fun _ : PUnit => Bool) pending
                  [.play PUnit.unit (.spec (profile PUnit.unit).2)])) =
            PMF.pure [.play PUnit.unit (profile PUnit.unit).2]
        rw [PMF.pure_map]
        rw [Machine.messageInFlight.projectEventBatch_deliverAllThenEvents]
        rfl

theorem boolDelayedSpecTraceGame_outcomeKernel_two
    (profile : ∀ _player : PUnit, Bool) :
    ((Machine.eventBatchTraceKernelGame
        boolSpecMachine (fun _ : PUnit => Bool)
        boolDelayedSpecLawFamily (fun _ => 0) 2).outcomeKernel profile) =
      PMF.pure
        ([[], [.play PUnit.unit (profile PUnit.unit)]],
          some (profile PUnit.unit)) := by
  simp [Machine.eventBatchTraceKernelGame, Machine.eventBatchTraceDist,
    Machine.eventBatchTraceDistFrom, boolDelayedSpecLawFamily,
    boolSpecMachine, Machine.runEventBatchesFrom, Machine.runEventsFrom,
    Machine.step]

theorem boolDelayedSpecTraceGame_eu_two
    (profile : ∀ _player : PUnit, Bool) :
    (Machine.eventBatchTraceKernelGame
        boolSpecMachine (fun _ : PUnit => Bool)
        boolDelayedSpecLawFamily (fun _ => 0) 2).eu profile PUnit.unit =
      if profile PUnit.unit then 1 else 0 := by
  unfold KernelGame.eu
  rw [boolDelayedSpecTraceGame_outcomeKernel_two]
  change
    Math.Probability.expect
        (PMF.pure
          (([[], [.play PUnit.unit (profile PUnit.unit)]],
            some (profile PUnit.unit)) :
            boolSpecMachine.EventBatchTrace))
        (fun trace =>
          Machine.eventBatchTraceUtility boolSpecMachine (fun _ => 0)
            trace PUnit.unit) =
      if profile PUnit.unit then 1 else 0
  simp [Machine.eventBatchTraceUtility, boolSpecMachine,
    Machine.RoundView.optionOutcomeUtility]

theorem boolDelayedSpecTraceGame_true_nash_two :
    (Machine.eventBatchTraceKernelGame
        boolSpecMachine (fun _ : PUnit => Bool)
        boolDelayedSpecLawFamily (fun _ => 0) 2).IsNash
      (fun _ => true) := by
  intro player alternative
  cases player
  cases alternative <;>
    simp [boolDelayedSpecTraceGame_eu_two, Function.update]

example (message action : Bool) :
    ((Machine.eventBatchTraceKernelGame
        boolMessageInFlightMachine (fun _ : PUnit => Bool × Bool)
        boolMessageInFlightDelayedLawLift.impl (fun _ => 0) 1)
        |>.outcomeKernel (fun _ : PUnit => (message, action))) =
      PMF.pure
        ([[.play PUnit.unit (.send message)]],
          { source := none,
            pending := [⟨PUnit.unit, message⟩],
            delivered := [] }) := by
  simp [Machine.eventBatchTraceKernelGame, Machine.eventBatchTraceDist,
    Machine.eventBatchTraceDistFrom_succ_nonterminal,
    Machine.runEventBatchesFrom_singleton, Machine.runEventsFrom_cons_bind,
    Machine.messageInFlight_stepPlay_send,
    boolMessageInFlightDelayedLawLift, boolMessageInFlightDelayedLawFamily,
    boolMessageInFlightMachine, boolSpecMachine,
    boolMessageInFlightRefinement, PMF.pure_bind]

example (message action : Bool) :
    ((Machine.eventBatchTraceKernelGame
        boolMessageInFlightMachine (fun _ : PUnit => Bool × Bool)
        boolMessageInFlightDelayedLawLift.impl (fun _ => 0) 2)
        |>.outcomeKernel (fun _ : PUnit => (message, action))) =
      PMF.pure
        ([[.play PUnit.unit (.send message)],
          [.internal .deliver,
            .play PUnit.unit (.spec action)]],
          { source := some action,
            pending := [],
            delivered := [⟨PUnit.unit, message⟩] }) := by
  simp [Machine.eventBatchTraceKernelGame, Machine.eventBatchTraceDist,
    Machine.eventBatchTraceDistFrom_succ_nonterminal,
    Machine.runEventBatchesFrom_singleton, Machine.runEventsFrom_cons_bind,
    Machine.messageInFlight_stepPlay_send,
    Machine.messageInFlight_stepPlay_spec,
    Machine.messageInFlight_stepInternal_deliver,
    boolMessageInFlightDelayedLawLift, boolMessageInFlightDelayedLawFamily,
    boolMessageInFlightMachine, boolSpecMachine,
    boolMessageInFlightRefinement, PMF.pure_bind]

example (profile : ∀ _player : PUnit, Bool × Bool) :
    PMF.map boolMessageInFlightRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            boolMessageInFlightMachine (fun _ : PUnit => Bool × Bool)
            boolMessageInFlightDelayedLawLift.impl (fun _ => 0) 2)
          |>.outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          boolSpecMachine (fun _ : PUnit => Bool × Bool)
          boolDelayedMessageSpecInertLawFamily.enriched
          (fun _ => 0) 2).outcomeKernel profile) :=
  boolMessageInFlightRefinement.eventBatchTraceKernelGame_projectTrace_eq
    boolMessageInFlightDelayedLawLift (fun _ => 0) 2 profile

example (message : Bool) :
    (Machine.eventBatchTraceKernelGame
        boolMessageInFlightMachine (fun _ : PUnit => Bool × Bool)
        boolMessageInFlightDelayedLawLift.impl (fun _ => 0) 2).IsNash
      (fun _ : PUnit => (message, true)) := by
  exact
    boolMessageInFlightRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_inert_projected_nash
        boolDelayedMessageSpecInertLawFamily
        boolMessageInFlightDelayedLawLift
        (fun _ => 0) 2
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        boolMessageInFlightTraceUtility_bound boolSpecTraceUtility_bound
        boolDelayedSpecTraceGame_true_nash_two

/-! ## Audited message-in-flight composition -/

noncomputable def auditedBoolMessageInFlightRefinement :
    Machine.StochasticRefinement
      (Machine.audited boolMessageInFlightMachine)
      boolSpecMachine :=
  boolMessageInFlightRefinement.compose
    (Machine.audited.refinement boolMessageInFlightMachine)

noncomputable def auditedBoolMessageInFlightLawLift :
    auditedBoolMessageInFlightRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × Bool)
      boolMessageSpecInertLawFamily.enriched :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.compose
    boolMessageInFlightLawLift
    (Machine.audited.liftEventBatchLawFamily boolMessageInFlightMachine
      boolMessageInFlightLawLift.impl)

example (profile : ∀ _player : PUnit, Bool × Bool) :
    PMF.map auditedBoolMessageInFlightRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            (Machine.audited boolMessageInFlightMachine)
            (fun _ : PUnit => Bool × Bool)
            auditedBoolMessageInFlightLawLift.impl
            (fun _ => 0) 3).outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          boolSpecMachine (fun _ : PUnit => Bool × Bool)
          boolMessageSpecInertLawFamily.enriched
          (fun _ => 0) 3).outcomeKernel profile) :=
  auditedBoolMessageInFlightRefinement.eventBatchTraceKernelGame_projectTrace_eq
    auditedBoolMessageInFlightLawLift (fun _ => 0) 3 profile

theorem auditedBoolMessageInFlightTraceUtility_bound
    (player : PUnit)
    (trace : (Machine.audited boolMessageInFlightMachine).EventBatchTrace) :
    |Machine.eventBatchTraceUtility
        (Machine.audited boolMessageInFlightMachine) (fun _ => 0)
        trace player| ≤ 1 := by
  exact
    (Machine.audited.refinement boolMessageInFlightMachine)
      |>.eventBatchTraceUtility_bound_project (fun _ => 0)
        boolMessageInFlightTraceUtility_bound player trace

example (message : Bool) :
    (Machine.eventBatchTraceKernelGame
        (Machine.audited boolMessageInFlightMachine)
        (fun _ : PUnit => Bool × Bool)
        auditedBoolMessageInFlightLawLift.impl (fun _ => 0) 3).IsNash
      (fun _ : PUnit => (message, true)) := by
  exact
    auditedBoolMessageInFlightRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_inert_projected_nash
        boolMessageSpecInertLawFamily
        auditedBoolMessageInFlightLawLift
        (fun _ => 0) 3
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        auditedBoolMessageInFlightTraceUtility_bound
        boolSpecTraceUtility_bound
        boolSpecTraceGame_true_nash_three

/-! ## Message-in-flight below the encoded runtime -/

noncomputable def encodedMessageInFlightMachine : Machine PUnit :=
  Machine.messageInFlight encodedImplMachine (fun _ : PUnit => Bool)

noncomputable def encodedMessageInFlightRefinement :
    Machine.StochasticRefinement encodedMessageInFlightMachine
      encodedImplMachine :=
  Machine.messageInFlight.refinement encodedImplMachine
    (fun _ : PUnit => Bool)

noncomputable def encodedMessageInFlightComposedRefinement :
    Machine.StochasticRefinement encodedMessageInFlightMachine
      boolSpecMachine :=
  encodedRefinement.compose encodedMessageInFlightRefinement

noncomputable def encodedMessageInFlightLawFamily :
    encodedMessageInFlightMachine.EventBatchLawFamily
      (fun _ : PUnit => Bool × Bool) where
  law := fun profile trace =>
    let message := (profile PUnit.unit).1
    let action := (profile PUnit.unit).2
    PMF.pure
      (Machine.messageInFlight.deliverAllThenEvents encodedImplMachine
          (fun _ : PUnit => Bool) trace.2.pending
        [.play PUnit.unit (.send message),
          .internal .deliver,
          .internal (.spec PUnit.unit),
          .play PUnit.unit (.spec action)])
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨payload, audit⟩
    let message := (profile PUnit.unit).1
    let action := (profile PUnit.unit).2
    change batch ∈
      (PMF.pure
        (Machine.messageInFlight.deliverAllThenEvents encodedImplMachine
            (fun _ : PUnit => Bool) pending
          [.play PUnit.unit (.send message),
            .internal .deliver,
            .internal (.spec PUnit.unit),
            .play PUnit.unit (.spec action)])).support at hbatch
    have hbatch_eq :
        batch =
          Machine.messageInFlight.deliverAllThenEvents encodedImplMachine
            (fun _ : PUnit => Bool) pending
            [.play PUnit.unit (.send message),
              .internal .deliver,
              .internal (.spec PUnit.unit),
              .play PUnit.unit (.spec action)] := by
      simp only [PMF.support_pure] at hbatch
      exact hbatch
    subst batch
    cases payload with
    | none =>
        let afterInternalSource : EncodedState :=
          { payload := none, audit := audit + 1 }
        have hsourceBatch :
            encodedImplMachine.AvailableBatchFrom
              { payload := none, audit := audit }
              [.internal PUnit.unit, .play PUnit.unit action] := by
          refine Machine.AvailableBatchFrom.cons ?_ ?_
          · change PUnit.unit ∈ Set.univ
            trivial
          · intro mid hmid
            change mid ∈ (PMF.pure afterInternalSource).support at hmid
            rw [PMF.support_pure] at hmid
            subst mid
            exact Machine.AvailableBatchFrom.singleton
              (by
                change action ∈ Set.univ
                exact Set.mem_univ action)
        simpa [encodedMessageInFlightMachine,
          Machine.messageInFlight.liftEvent] using
          Machine.messageInFlight.deliverAllThenSendDeliverLiftAvailableBatchFrom
            encodedImplMachine (fun _ : PUnit => Bool) pending delivered
            PUnit.unit message (by simp [encodedImplMachine]) hsourceBatch
    | some value =>
        exact False.elim
          (hnonterminal (by
            simp [encodedMessageInFlightMachine, Machine.messageInFlight,
              encodedImplMachine]))

noncomputable def encodedMessageInFlightLawLift :
    encodedMessageInFlightRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × Bool)
      encodedMessageImplInertLawFamily.enriched where
  impl := encodedMessageInFlightLawFamily
  compatible := by
    intro profile trace
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨encodedState, pending, delivered⟩
    change
      PMF.map (Machine.messageInFlight.projectEventBatch
          encodedImplMachine (fun _ : PUnit => Bool))
          (PMF.pure
            (Machine.messageInFlight.deliverAllThenEvents encodedImplMachine
                (fun _ : PUnit => Bool) pending
              [.play PUnit.unit (.send (profile PUnit.unit).1),
                .internal .deliver,
                .internal (.spec PUnit.unit),
                .play PUnit.unit (.spec (profile PUnit.unit).2)])) =
        PMF.pure
          [.internal PUnit.unit,
            .play PUnit.unit (profile PUnit.unit).2]
    rw [PMF.pure_map]
    rw [Machine.messageInFlight.projectEventBatch_deliverAllThenEvents]
    rfl

noncomputable def encodedMessageInFlightComposedLawLift :
    encodedMessageInFlightComposedRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => Bool × Bool)
      boolMessageSpecInertLawFamily.enriched :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.compose
    encodedMessageLawLift
    encodedMessageInFlightLawLift

example (message action : Bool) :
    encodedMessageInFlightComposedRefinement.projectEventBatch
        [.play PUnit.unit (.send message),
          .internal .deliver,
          .internal (.spec PUnit.unit),
          .play PUnit.unit (.spec action)] =
      [.play PUnit.unit action] := by
  rfl

example (profile : ∀ _player : PUnit, Bool × Bool) :
    PMF.map encodedMessageInFlightComposedRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            encodedMessageInFlightMachine
            (fun _ : PUnit => Bool × Bool)
            encodedMessageInFlightComposedLawLift.impl
            (fun _ => 0) 3).outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          boolSpecMachine (fun _ : PUnit => Bool × Bool)
          boolMessageSpecInertLawFamily.enriched
          (fun _ => 0) 3).outcomeKernel profile) :=
  encodedMessageInFlightComposedRefinement
    |>.eventBatchTraceKernelGame_projectTrace_eq
      encodedMessageInFlightComposedLawLift (fun _ => 0) 3 profile

theorem encodedMessageInFlightTraceUtility_bound
    (player : PUnit)
    (trace : encodedMessageInFlightMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility encodedMessageInFlightMachine
        (fun _ => 0) trace player| ≤ 1 := by
  cases player
  rcases trace with ⟨batches, state⟩
  rcases state with ⟨encodedState, pending, delivered⟩
  rcases encodedState with ⟨payload, audit⟩
  cases payload with
  | none =>
      simp [Machine.eventBatchTraceUtility, encodedMessageInFlightMachine,
        Machine.messageInFlight, Machine.RoundView.optionOutcomeUtility,
        encodedImplMachine]
  | some value =>
      by_cases hdecode : decodeNat value
      · simp [Machine.eventBatchTraceUtility,
          encodedMessageInFlightMachine, Machine.messageInFlight,
          Machine.RoundView.optionOutcomeUtility, encodedImplMachine,
          hdecode]
      · simp [Machine.eventBatchTraceUtility,
          encodedMessageInFlightMachine, Machine.messageInFlight,
          Machine.RoundView.optionOutcomeUtility, encodedImplMachine,
          hdecode]

example (message : Bool) :
    (Machine.eventBatchTraceKernelGame
        encodedMessageInFlightMachine (fun _ : PUnit => Bool × Bool)
        encodedMessageInFlightComposedLawLift.impl
        (fun _ => 0) 3).IsNash
      (fun _ : PUnit => (message, true)) := by
  exact
    encodedMessageInFlightComposedRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_inert_projected_nash
        boolMessageSpecInertLawFamily
        encodedMessageInFlightComposedLawLift
        (fun _ => 0) 3
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        encodedMessageInFlightTraceUtility_bound
        boolSpecTraceUtility_bound
        boolSpecTraceGame_true_nash_three

end Refinement
end Examples
end Vegas
