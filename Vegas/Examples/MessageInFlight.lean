import Vegas.Machine.MessageInFlight
import Vegas.Examples.BoolMessage

/-!
# Message-in-flight runtime refinement examples

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
    match trace.2.pending with
    | [] =>
        PMF.pure
          [.play PUnit.unit (.send message),
            .internal .deliver,
            .play PUnit.unit (.spec action)]
    | _ :: _ =>
        PMF.pure
          [.play PUnit.unit (.send message),
            .play PUnit.unit (.spec action)]
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨sourceState, pending, delivered⟩
    cases sourceState with
    | none =>
        cases pending with
        | nil =>
            let message := (profile PUnit.unit).1
            let action := (profile PUnit.unit).2
            let sent : Sigma (fun _ : PUnit => Bool) :=
              ⟨PUnit.unit, message⟩
            rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
            subst batch
            let src : boolMessageInFlightMachine.State :=
              { source := none,
                pending := [],
                delivered := delivered }
            let afterSend : boolMessageInFlightMachine.State :=
              { source := none,
                pending := [sent],
                delivered := delivered }
            let afterDeliver : boolMessageInFlightMachine.State :=
              { source := none,
                pending := [],
                delivered := delivered ++ [sent] }
            let dst : boolMessageInFlightMachine.State :=
              { source := some action,
                pending := [],
                delivered := delivered ++ [sent] }
            let restore
                (sourceValue : Option Bool) :
                boolMessageInFlightMachine.State :=
              { source := sourceValue,
                pending := [],
                delivered := delivered ++ [sent] }
            refine ⟨dst, ?_⟩
            change
              boolMessageInFlightMachine.AvailableRunFrom src
                [.play PUnit.unit (.send message),
                  .internal .deliver,
                  .play PUnit.unit (.spec action)]
                dst
            refine Machine.AvailableRunFrom.cons (mid := afterSend) ?_ ?_ ?_
            · change Machine.MessageInFlightAction.send message ∈
                boolMessageInFlightMachine.available src PUnit.unit
              change ¬ boolSpecMachine.terminal none
              simp [boolSpecMachine]
            · change afterSend ∈ (PMF.pure afterSend).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
            · refine Machine.AvailableRunFrom.cons (mid := afterDeliver)
                ?_ ?_ ?_
              · change Machine.MessageInFlightInternal.deliver ∈
                  boolMessageInFlightMachine.availableInternal afterSend
                change afterSend.pending ≠ [] ∧
                  ¬ boolSpecMachine.terminal afterSend.source
                constructor
                · change [sent] ≠ []
                  intro hnil
                  cases hnil
                · change ¬ boolSpecMachine.terminal none
                  simp [boolSpecMachine]
              · change afterDeliver ∈ (PMF.pure afterDeliver).support
                rw [PMF.support_pure]
                exact Set.mem_singleton _
              · refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightAction.spec action ∈
                    boolMessageInFlightMachine.available afterDeliver
                      PUnit.unit
                  change action ∈
                    boolSpecMachine.available afterDeliver.source PUnit.unit
                  change action ∈ Set.univ
                  exact Set.mem_univ action
                · change dst ∈
                    (PMF.map restore (PMF.pure (some action))).support
                  rw [PMF.pure_map, PMF.support_pure]
                  exact Set.mem_singleton _
        | cons old rest =>
            let message := (profile PUnit.unit).1
            let action := (profile PUnit.unit).2
            let sent : Sigma (fun _ : PUnit => Bool) :=
              ⟨PUnit.unit, message⟩
            rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
            subst batch
            let src : boolMessageInFlightMachine.State :=
              { source := none,
                pending := old :: rest,
                delivered := delivered }
            let afterSend : boolMessageInFlightMachine.State :=
              { source := none,
                pending := old :: rest ++ [sent],
                delivered := delivered }
            let dst : boolMessageInFlightMachine.State :=
              { source := some action,
                pending := old :: rest ++ [sent],
                delivered := delivered }
            let restore
                (sourceValue : Option Bool) :
                boolMessageInFlightMachine.State :=
              { source := sourceValue,
                pending := old :: rest ++ [sent],
                delivered := delivered }
            refine ⟨dst, ?_⟩
            change
              boolMessageInFlightMachine.AvailableRunFrom src
                [.play PUnit.unit (.send message),
                  .play PUnit.unit (.spec action)]
                dst
            refine Machine.AvailableRunFrom.cons (mid := afterSend) ?_ ?_ ?_
            · change Machine.MessageInFlightAction.send message ∈
                boolMessageInFlightMachine.available src PUnit.unit
              change ¬ boolSpecMachine.terminal none
              simp [boolSpecMachine]
            · change afterSend ∈ (PMF.pure afterSend).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
            · refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                (Machine.AvailableRunFrom.nil _)
              · change Machine.MessageInFlightAction.spec action ∈
                  boolMessageInFlightMachine.available afterSend PUnit.unit
                change action ∈
                  boolSpecMachine.available afterSend.source PUnit.unit
                change action ∈ Set.univ
                exact Set.mem_univ action
              · change dst ∈
                  (PMF.map restore (PMF.pure (some action))).support
                rw [PMF.pure_map, PMF.support_pure]
                exact Set.mem_singleton _
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
    cases pending with
    | nil =>
        change
          PMF.map (Machine.messageInFlight.projectEventBatch
              boolSpecMachine (fun _ : PUnit => Bool))
              (PMF.pure
                [.play PUnit.unit (.send (profile PUnit.unit).1),
                  .internal .deliver,
                  .play PUnit.unit (.spec (profile PUnit.unit).2)]) =
            PMF.pure [.play PUnit.unit (profile PUnit.unit).2]
        rw [PMF.pure_map]
        rfl
    | cons old rest =>
        change
          PMF.map (Machine.messageInFlight.projectEventBatch
              boolSpecMachine (fun _ : PUnit => Bool))
              (PMF.pure
                [.play PUnit.unit (.send (profile PUnit.unit).1),
                  .play PUnit.unit (.spec (profile PUnit.unit).2)]) =
            PMF.pure [.play PUnit.unit (profile PUnit.unit).2]
        rw [PMF.pure_map]
        rfl

example (message action : Bool) :
    boolMessageInFlightRefinement.projectEventBatch
        [.play PUnit.unit (.send message),
          .internal .deliver,
          .play PUnit.unit (.spec action)] =
      [.play PUnit.unit action] := by
  rfl

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
        exact ⟨state, Machine.AvailableRunFrom.nil _⟩
    | cons first rest =>
        rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
        subst batch
        cases state with
        | none =>
            refine ⟨some (profile PUnit.unit), ?_⟩
            exact
              Machine.AvailableRunFrom.cons
                (by simp [boolSpecMachine])
                (by
                  change some (profile PUnit.unit) ∈
                    (PMF.pure (some (profile PUnit.unit))).support
                  rw [PMF.support_pure, Set.mem_singleton_iff])
                (Machine.AvailableRunFrom.nil _)
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
        match trace.2.pending with
        | [] => PMF.pure [.play PUnit.unit (.spec action)]
        | _ :: _ =>
            PMF.pure
              [.internal .deliver,
                .play PUnit.unit (.spec action)]
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
            let sent : Sigma (fun _ : PUnit => Bool) :=
              ⟨PUnit.unit, message⟩
            let src : boolMessageInFlightMachine.State :=
              { source := none,
                pending := pending,
                delivered := delivered }
            let dst : boolMessageInFlightMachine.State :=
              { source := none,
                pending := pending ++ [sent],
                delivered := delivered }
            refine ⟨dst, ?_⟩
            change
              boolMessageInFlightMachine.AvailableRunFrom src
                [.play PUnit.unit (.send message)] dst
            refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
              (Machine.AvailableRunFrom.nil _)
            · change Machine.MessageInFlightAction.send message ∈
                boolMessageInFlightMachine.available src PUnit.unit
              change ¬ boolSpecMachine.terminal none
              simp [boolSpecMachine]
            · change dst ∈ (PMF.pure dst).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
        | some value =>
            exact False.elim (hnonterminal (by
              cases value <;>
                simp [boolMessageInFlightMachine, Machine.messageInFlight,
                  boolSpecMachine]))
    | cons first restBatches =>
        cases pending with
        | nil =>
            change batch ∈
              (PMF.pure
                [.play PUnit.unit (.spec action)]).support
              at hbatch
            rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
            subst batch
            cases sourceState with
            | none =>
                let src : boolMessageInFlightMachine.State :=
                  { source := none,
                    pending := [],
                    delivered := delivered }
                let dst : boolMessageInFlightMachine.State :=
                  { source := some action,
                    pending := [],
                    delivered := delivered }
                let restore
                    (sourceValue : Option Bool) :
                    boolMessageInFlightMachine.State :=
                  { source := sourceValue,
                    pending := [],
                    delivered := delivered }
                refine ⟨dst, ?_⟩
                change
                  boolMessageInFlightMachine.AvailableRunFrom src
                    [.play PUnit.unit (.spec action)] dst
                refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightAction.spec action ∈
                    boolMessageInFlightMachine.available src PUnit.unit
                  change action ∈ boolSpecMachine.available none PUnit.unit
                  change action ∈ Set.univ
                  exact Set.mem_univ action
                · change dst ∈
                    (PMF.map restore (PMF.pure (some action))).support
                  rw [PMF.pure_map, PMF.support_pure]
                  exact Set.mem_singleton _
            | some value =>
                exact False.elim (hnonterminal (by
                  cases value <;>
                    simp [boolMessageInFlightMachine, Machine.messageInFlight,
                      boolSpecMachine]))
        | cons old rest =>
            change batch ∈
              (PMF.pure
                [.internal .deliver,
                  .play PUnit.unit (.spec action)]).support
              at hbatch
            rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
            subst batch
            cases sourceState with
            | none =>
                let src : boolMessageInFlightMachine.State :=
                  { source := none,
                    pending := old :: rest,
                    delivered := delivered }
                let afterDeliver : boolMessageInFlightMachine.State :=
                  { source := none,
                    pending := rest,
                    delivered := delivered ++ [old] }
                let dst : boolMessageInFlightMachine.State :=
                  { source := some action,
                    pending := rest,
                    delivered := delivered ++ [old] }
                let restore
                    (sourceValue : Option Bool) :
                    boolMessageInFlightMachine.State :=
                  { source := sourceValue,
                    pending := rest,
                    delivered := delivered ++ [old] }
                refine ⟨dst, ?_⟩
                change
                  boolMessageInFlightMachine.AvailableRunFrom src
                    [.internal .deliver,
                      .play PUnit.unit (.spec action)]
                    dst
                refine Machine.AvailableRunFrom.cons (mid := afterDeliver)
                  ?_ ?_ ?_
                · change Machine.MessageInFlightInternal.deliver ∈
                    boolMessageInFlightMachine.availableInternal src
                  change src.pending ≠ [] ∧
                    ¬ boolSpecMachine.terminal src.source
                  constructor
                  · change old :: rest ≠ []
                    intro hnil
                    cases hnil
                  · change ¬ boolSpecMachine.terminal none
                    simp [boolSpecMachine]
                · change afterDeliver ∈ (PMF.pure afterDeliver).support
                  rw [PMF.support_pure]
                  exact Set.mem_singleton _
                · refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                    (Machine.AvailableRunFrom.nil _)
                  · change Machine.MessageInFlightAction.spec action ∈
                      boolMessageInFlightMachine.available afterDeliver
                        PUnit.unit
                    change action ∈
                      boolSpecMachine.available afterDeliver.source PUnit.unit
                    change action ∈ Set.univ
                    exact Set.mem_univ action
                  · change dst ∈
                      (PMF.map restore (PMF.pure (some action))).support
                    rw [PMF.pure_map, PMF.support_pure]
                    exact Set.mem_singleton _
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
        cases pending with
        | nil =>
            change
              PMF.map (Machine.messageInFlight.projectEventBatch
                  boolSpecMachine (fun _ : PUnit => Bool))
                  (PMF.pure
                    [.play PUnit.unit (.spec (profile PUnit.unit).2)]) =
                PMF.pure [.play PUnit.unit (profile PUnit.unit).2]
            rw [PMF.pure_map]
            rfl
        | cons old rest =>
            change
              PMF.map (Machine.messageInFlight.projectEventBatch
                  boolSpecMachine (fun _ : PUnit => Bool))
                  (PMF.pure
                    [.internal .deliver,
                      .play PUnit.unit (.spec (profile PUnit.unit).2)]) =
                PMF.pure [.play PUnit.unit (profile PUnit.unit).2]
            rw [PMF.pure_map]
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
    Machine.eventBatchTraceDistFrom, boolMessageInFlightDelayedLawLift,
    boolMessageInFlightDelayedLawFamily, boolMessageInFlightMachine,
    Machine.messageInFlight,
    boolSpecMachine,
    Machine.runEventBatchesFrom, Machine.runEventsFrom, Machine.step,
    boolMessageInFlightRefinement]

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
    Machine.eventBatchTraceDistFrom, boolMessageInFlightDelayedLawLift,
    boolMessageInFlightDelayedLawFamily, boolMessageInFlightMachine,
    Machine.messageInFlight,
    boolSpecMachine,
    Machine.runEventBatchesFrom, Machine.runEventsFrom, Machine.step,
    boolMessageInFlightRefinement]

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
  cases player
  rcases trace with ⟨batches, state⟩
  rcases state with ⟨messageState, audit⟩
  rcases messageState with ⟨sourceState, pending, delivered⟩
  cases sourceState with
  | none =>
      simp [Machine.eventBatchTraceUtility, Machine.audited,
        boolMessageInFlightMachine, Machine.messageInFlight,
        Machine.RoundView.optionOutcomeUtility, boolSpecMachine]
  | some value =>
      cases value <;>
        simp [Machine.eventBatchTraceUtility, Machine.audited,
          boolMessageInFlightMachine, Machine.messageInFlight,
          Machine.RoundView.optionOutcomeUtility, boolSpecMachine]

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
    match trace.2.pending with
    | [] =>
        PMF.pure
          [.play PUnit.unit (.send message),
            .internal .deliver,
            .internal (.spec PUnit.unit),
            .play PUnit.unit (.spec action)]
    | _ :: _ =>
        PMF.pure
          [.play PUnit.unit (.send message),
            .internal (.spec PUnit.unit),
            .play PUnit.unit (.spec action)]
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨payload, audit⟩
    cases payload with
    | none =>
        cases pending with
        | nil =>
            let message := (profile PUnit.unit).1
            let action := (profile PUnit.unit).2
            let sent : Sigma (fun _ : PUnit => Bool) :=
              ⟨PUnit.unit, message⟩
            rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
            subst batch
            let src : encodedMessageInFlightMachine.State :=
              { source := { payload := none, audit := audit },
                pending := [],
                delivered := delivered }
            let afterSend : encodedMessageInFlightMachine.State :=
              { source := { payload := none, audit := audit },
                pending := [sent],
                delivered := delivered }
            let afterDeliver : encodedMessageInFlightMachine.State :=
              { source := { payload := none, audit := audit },
                pending := [],
                delivered := delivered ++ [sent] }
            let afterInternalSource : EncodedState :=
              { payload := none, audit := audit + 1 }
            let finalSource : EncodedState :=
              { payload := some (encodeBool action),
                audit := audit + 1 }
            let afterInternal : encodedMessageInFlightMachine.State :=
              { source := afterInternalSource,
                pending := [],
                delivered := delivered ++ [sent] }
            let dst : encodedMessageInFlightMachine.State :=
              { source := finalSource,
                pending := [],
                delivered := delivered ++ [sent] }
            let restoreInternal
                (sourceValue : EncodedState) :
                encodedMessageInFlightMachine.State :=
              { source := sourceValue,
                pending := [],
                delivered := delivered ++ [sent] }
            refine ⟨dst, ?_⟩
            change
              encodedMessageInFlightMachine.AvailableRunFrom src
                [.play PUnit.unit (.send message),
                  .internal .deliver,
                  .internal (.spec PUnit.unit),
                  .play PUnit.unit (.spec action)]
                dst
            refine Machine.AvailableRunFrom.cons (mid := afterSend) ?_ ?_ ?_
            · change Machine.MessageInFlightAction.send message ∈
                encodedMessageInFlightMachine.available src PUnit.unit
              change ¬ encodedImplMachine.terminal src.source
              simp [encodedImplMachine, src]
            · change afterSend ∈ (PMF.pure afterSend).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
            · refine Machine.AvailableRunFrom.cons (mid := afterDeliver)
                ?_ ?_ ?_
              · change Machine.MessageInFlightInternal.deliver ∈
                  encodedMessageInFlightMachine.availableInternal afterSend
                change afterSend.pending ≠ [] ∧
                  ¬ encodedImplMachine.terminal afterSend.source
                constructor
                · change [sent] ≠ []
                  intro hnil
                  cases hnil
                · change ¬ encodedImplMachine.terminal
                    { payload := none, audit := audit }
                  simp [encodedImplMachine]
              · change afterDeliver ∈ (PMF.pure afterDeliver).support
                rw [PMF.support_pure]
                exact Set.mem_singleton _
              · refine Machine.AvailableRunFrom.cons (mid := afterInternal)
                  ?_ ?_ ?_
                · change Machine.MessageInFlightInternal.spec PUnit.unit ∈
                    encodedMessageInFlightMachine.availableInternal
                      afterDeliver
                  change PUnit.unit ∈
                    encodedImplMachine.availableInternal afterDeliver.source
                  change PUnit.unit ∈ Set.univ
                  trivial
                · change afterInternal ∈
                    (PMF.map restoreInternal
                      (PMF.pure afterInternalSource)).support
                  rw [PMF.pure_map, PMF.support_pure]
                  exact Set.mem_singleton _
                · refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                    (Machine.AvailableRunFrom.nil _)
                  · change Machine.MessageInFlightAction.spec action ∈
                      encodedMessageInFlightMachine.available afterInternal
                        PUnit.unit
                    change action ∈
                      encodedImplMachine.available afterInternal.source
                        PUnit.unit
                    change action ∈ Set.univ
                    exact Set.mem_univ action
                  · change dst ∈
                      (PMF.map restoreInternal
                        (PMF.pure finalSource)).support
                    rw [PMF.pure_map, PMF.support_pure]
                    exact Set.mem_singleton _
        | cons old rest =>
            let message := (profile PUnit.unit).1
            let action := (profile PUnit.unit).2
            let sent : Sigma (fun _ : PUnit => Bool) :=
              ⟨PUnit.unit, message⟩
            rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
            subst batch
            let src : encodedMessageInFlightMachine.State :=
              { source := { payload := none, audit := audit },
                pending := old :: rest,
                delivered := delivered }
            let afterSend : encodedMessageInFlightMachine.State :=
              { source := { payload := none, audit := audit },
                pending := old :: rest ++ [sent],
                delivered := delivered }
            let afterInternalSource : EncodedState :=
              { payload := none, audit := audit + 1 }
            let finalSource : EncodedState :=
              { payload := some (encodeBool action),
                audit := audit + 1 }
            let afterInternal : encodedMessageInFlightMachine.State :=
              { source := afterInternalSource,
                pending := old :: rest ++ [sent],
                delivered := delivered }
            let dst : encodedMessageInFlightMachine.State :=
              { source := finalSource,
                pending := old :: rest ++ [sent],
                delivered := delivered }
            let restore
                (sourceValue : EncodedState) :
                encodedMessageInFlightMachine.State :=
              { source := sourceValue,
                pending := old :: rest ++ [sent],
                delivered := delivered }
            refine ⟨dst, ?_⟩
            change
              encodedMessageInFlightMachine.AvailableRunFrom src
                [.play PUnit.unit (.send message),
                  .internal (.spec PUnit.unit),
                  .play PUnit.unit (.spec action)]
                dst
            refine Machine.AvailableRunFrom.cons (mid := afterSend) ?_ ?_ ?_
            · change Machine.MessageInFlightAction.send message ∈
                encodedMessageInFlightMachine.available src PUnit.unit
              change ¬ encodedImplMachine.terminal src.source
              simp [encodedImplMachine, src]
            · change afterSend ∈ (PMF.pure afterSend).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
            · refine Machine.AvailableRunFrom.cons (mid := afterInternal)
                ?_ ?_ ?_
              · change Machine.MessageInFlightInternal.spec PUnit.unit ∈
                  encodedMessageInFlightMachine.availableInternal afterSend
                change PUnit.unit ∈
                  encodedImplMachine.availableInternal afterSend.source
                change PUnit.unit ∈ Set.univ
                trivial
              · change afterInternal ∈
                  (PMF.map restore
                    (PMF.pure afterInternalSource)).support
                rw [PMF.pure_map, PMF.support_pure]
                exact Set.mem_singleton _
              · refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightAction.spec action ∈
                    encodedMessageInFlightMachine.available afterInternal
                      PUnit.unit
                  change action ∈
                    encodedImplMachine.available afterInternal.source
                      PUnit.unit
                  change action ∈ Set.univ
                  exact Set.mem_univ action
                · change dst ∈
                    (PMF.map restore
                      (PMF.pure finalSource)).support
                  rw [PMF.pure_map, PMF.support_pure]
                  exact Set.mem_singleton _
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
    cases pending with
    | nil =>
        change
          PMF.map (Machine.messageInFlight.projectEventBatch
              encodedImplMachine (fun _ : PUnit => Bool))
              (PMF.pure
                [.play PUnit.unit (.send (profile PUnit.unit).1),
                  .internal .deliver,
                  .internal (.spec PUnit.unit),
                  .play PUnit.unit (.spec (profile PUnit.unit).2)]) =
            PMF.pure
              [.internal PUnit.unit,
                .play PUnit.unit (profile PUnit.unit).2]
        rw [PMF.pure_map]
        rfl
    | cons old rest =>
        change
          PMF.map (Machine.messageInFlight.projectEventBatch
              encodedImplMachine (fun _ : PUnit => Bool))
              (PMF.pure
                [.play PUnit.unit (.send (profile PUnit.unit).1),
                  .internal (.spec PUnit.unit),
                  .play PUnit.unit (.spec (profile PUnit.unit).2)]) =
            PMF.pure
              [.internal PUnit.unit,
                .play PUnit.unit (profile PUnit.unit).2]
        rw [PMF.pure_map]
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
