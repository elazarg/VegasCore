/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory
import Interaction.ReactiveResponseMenu
import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Decision depths from a fixed activation schedule

A player's remembered response count identifies its occurrence in a fixed
activation schedule, even when that player occurs repeatedly. This yields a
common depth for every information site without exposing scheduler memory.
The scheduler may still choose arbitrary commands with the scheduled actor.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

private theorem occurrence_unique (schedule : List (Option Principal)) (who : Principal)
    (first second : Nat)
    (left : schedule[first]? = some (some who))
    (right : schedule[second]? = some (some who))
    (counted : (schedule.take first).count (some who) =
      (schedule.take second).count (some who)) : first = second := by
  induction schedule generalizing first second with
  | nil => simp at left
  | cons head rest ih =>
      cases first with
      | zero =>
          cases second with
          | zero => rfl
          | succ second =>
              have same : head = some who := Option.some.inj left
              simp [same] at counted
      | succ first =>
          cases second with
          | zero =>
              have same : head = some who := Option.some.inj right
              simp [same] at counted
          | succ second =>
              have counts : (rest.take first).count (some who) =
                  (rest.take second).count (some who) := by
                simpa only [List.take_succ_cons, List.count_cons,
                  Nat.add_right_cancel_iff] using counted
              exact congrArg Nat.succ (ih first second left right counts)

private def ScheduledTrace (schedule : List (Option Principal))
    (state : app.ProtocolState) (depth : Nat) : Prop :=
  match state with
  | none => depth = 0
  | some control =>
      depth + control.actor.toList.length =
        1 + control.execution.environmentRecall.length +
          ((schedule.take control.execution.environmentRecall.length).filterMap id).length ∧
      (∀ who, (control.execution.recall who).length +
        (if control.actor = some who then 1 else 0) =
          (schedule.take control.execution.environmentRecall.length).count (some who)) ∧
      (∀ who, control.actor = some who → ∃ position,
        control.execution.environmentRecall.length = position + 1 ∧
          schedule[position]? = some (some who))

private theorem schedule_counts (schedule : List (Option Principal)) (position : Nat)
    (actor : Option Principal) (selected : (schedule[position]?).join = actor) :
    ((schedule.take (position + 1)).filterMap id).length =
        ((schedule.take position).filterMap id).length + actor.toList.length ∧
      ∀ who, (schedule.take (position + 1)).count (some who) =
        (schedule.take position).count (some who) + if actor = some who then 1 else 0 := by
  rw [List.take_add_one]
  cases found : schedule[position]? with
  | none =>
      simp only [found, Option.join_none] at selected
      subst actor
      simp
  | some entry =>
      simp only [found, Option.join_some] at selected
      subst actor
      cases entry with
      | none => simp
      | some owner =>
          simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, id_eq,
            List.length_append, List.length_singleton, Option.toList_some, List.count_append]
          refine ⟨trivial, ?_⟩
          intro who
          by_cases same : owner = who <;> simp [same]

private theorem trace_scheduled (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (schedule : List (Option Principal))
    (scheduled : ∀ history view command, command ∈ (scheduler history view).support →
      command.actor? app = (schedule[history.length]?).join) :
    ∀ {state} (trace : (app.protocol initial horizon scheduler).Trace state),
      ScheduledTrace app schedule state trace.length
  | _, .start => rfl
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := trace_scheduled initial horizon scheduler schedule scheduled before
      have reached : target ∈ (app.transition initial horizon scheduler source joint).support :=
        realized
      cases source with
      | none =>
          obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ reached
          have counted : before.length = 0 := inherited
          simp only [ScheduledTrace, Trace.length, Execution.initial, List.length_nil,
            Option.toList_none, Nat.add_zero, List.take_zero, List.filterMap_nil, List.count_nil,
            reduceCtorEq, ↓reduceIte, counted]
          exact ⟨trivial, fun _ => trivial, fun _ impossible => impossible.elim⟩
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some owner =>
              cases FinDist.mem_support_pure.mp reached
              rcases inherited with ⟨depth, counts, _⟩
              refine ⟨?_, ?_, by simp⟩
              · simpa only [Trace.length, app.respond_environmentRecall, Option.toList_some,
                  Option.toList_none, List.length_singleton, List.length_nil, Nat.add_zero]
                    using depth
              · intro who
                simpa only [app.respond_recall_length, app.respond_environmentRecall,
                  reduceCtorEq, ↓reduceIte, Nat.add_zero, Option.some.injEq] using counts who
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
                  have recall := app.environmentStep_recall execution next command supported
                  have advanced : next.environmentRecall = execution.environmentRecall ++
                      [⟨execution.observeEnvironment app, command⟩] := by
                    obtain ⟨updated, _, equal⟩ := FinDist.support_map .. ▸ supported
                    cases equal
                    rfl
                  have actorEq := scheduled execution.environmentRecall
                    (execution.observeEnvironment app) command selected
                  have increments := schedule_counts schedule execution.environmentRecall.length
                    (command.actor? app) actorEq.symm
                  rcases inherited with ⟨depth, counts, _⟩
                  simp only [Option.toList_none, List.length_nil, Nat.add_zero] at depth
                  refine ⟨?_, ?_, ?_⟩
                  · simp only [Trace.length, advanced, List.length_append, List.length_singleton,
                      increments.1]
                    omega
                  · intro who
                    simp only [recall, advanced, List.length_append, List.length_singleton,
                      increments.2]
                    simpa only [reduceCtorEq, ↓reduceIte, Nat.add_zero] using
                      congrArg (· + if command.actor? app = some who then 1 else 0) (counts who)
                  · intro who active
                    refine ⟨execution.environmentRecall.length, ?_, ?_⟩
                    · simp only [advanced, List.length_append, List.length_singleton]
                    · change command.actor? app = some who at active
                      rw [active] at actorEq
                      cases found : schedule[execution.environmentRecall.length]? with
                      | none => simp [found] at actorEq
                      | some entry =>
                          simp only [found, Option.join_some] at actorEq
                          exact congrArg some actorEq.symm

/-- Equal own response counts at two decisions identify the same scheduler
position and the same full protocol depth, for arbitrary native responses. -/
theorem scheduled_decision_position (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (schedule : List (Option Principal))
    (scheduled : ∀ history view command, command ∈ (scheduler history view).support →
      command.actor? app = (schedule[history.length]?).join)
    (who : Principal) (first second : app.Control)
    (left : (app.protocol initial horizon scheduler).Trace (some first))
    (right : (app.protocol initial horizon scheduler).Trace (some second))
    (firstActive : first.actor = some who) (secondActive : second.actor = some who)
    (same : (first.execution.recall who).length = (second.execution.recall who).length) :
    first.execution.environmentRecall.length = second.execution.environmentRecall.length ∧
      left.length = right.length := by
  obtain ⟨leftDepth, leftCounts, leftPosition⟩ :=
    trace_scheduled app initial horizon scheduler schedule scheduled left
  obtain ⟨rightDepth, rightCounts, rightPosition⟩ :=
    trace_scheduled app initial horizon scheduler schedule scheduled right
  obtain ⟨firstIndex, firstAt, firstFound⟩ := leftPosition who firstActive
  obtain ⟨secondIndex, secondAt, secondFound⟩ := rightPosition who secondActive
  have leftIncrement := (schedule_counts schedule firstIndex (some who)
    (by rw [firstFound]; rfl)).2 who
  have rightIncrement := (schedule_counts schedule secondIndex (some who)
    (by rw [secondFound]; rfl)).2 who
  have firstCount := leftCounts who
  have secondCount := rightCounts who
  simp only [firstActive, secondActive, ↓reduceIte, firstAt, secondAt,
    leftIncrement, rightIncrement] at firstCount secondCount
  have indices : firstIndex = secondIndex := occurrence_unique schedule who _ _
    firstFound secondFound (by omega)
  have position : first.execution.environmentRecall.length =
      second.execution.environmentRecall.length := by omega
  refine ⟨position, ?_⟩
  rw [firstActive, position] at leftDepth
  rw [secondActive] at rightDepth
  omega

/-- Exact schedule occurrence and response counts at every raw decision. -/
theorem scheduled_decision_counts (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (schedule : List (Option Principal))
    (scheduled : ∀ history view command, command ∈ (scheduler history view).support →
      command.actor? app = (schedule[history.length]?).join)
    (who : Principal) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (active : control.actor = some who) :
    ∃ position, control.execution.environmentRecall.length = position + 1 ∧
      schedule[position]? = some (some who) ∧
      (∀ observer, (control.execution.recall observer).length +
        (if who = observer then 1 else 0) =
          (schedule.take (position + 1)).count (some observer)) ∧
      trace.length = position + 1 +
        ((schedule.take (position + 1)).filterMap id).length := by
  obtain ⟨depth, counts, located⟩ :=
    trace_scheduled app initial horizon scheduler schedule scheduled trace
  obtain ⟨position, atPosition, found⟩ := located who active
  refine ⟨position, atPosition, found, ?_, ?_⟩
  · intro observer
    simpa only [active, atPosition, Option.some.injEq] using counts observer
  · simp only [active, atPosition, Option.toList_some, List.length_singleton] at depth
    omega

/-- Every information site of any response restriction of the scheduled
runtime has a common protocol depth. The actual input representation is unchanged. -/
theorem scheduled_menu_common_depth (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (schedule : List (Option Principal))
    (scheduled : ∀ history view command, command ∈ (scheduler history view).support →
      command.actor? app = (schedule[history.length]?).join)
    (menu : app.ResponseMenu) (who : Principal)
    (site : (menu.information initial horizon scheduler).InformationSite who) :
    ∃ depth, InformationModel.InformationSite.CommonDepth
      (menu.information initial horizon scheduler) site depth := by
  obtain ⟨witness, _, _⟩ := site.2
  refine ⟨witness.1.trace.length, ?_⟩
  intro history
  have leftActive := InformationModel.InformationSite.active _ site history
  have rightActive := InformationModel.InformationSite.active _ site witness
  rcases history with ⟨⟨leftState, leftTrace⟩, leftInfo⟩
  rcases witness with ⟨⟨rightState, rightTrace⟩, rightInfo⟩
  cases leftState with
  | none => cases leftActive
  | some left =>
      cases rightState with
      | none => cases rightActive
      | some right =>
          change left.actor = some who at leftActive
          change right.actor = some who at rightActive
          have observations := leftInfo.trans rightInfo.symm
          change (menu.signals initial horizon scheduler).infoOf who leftTrace =
            (menu.signals initial horizon scheduler).infoOf who rightTrace at observations
          rw [menu.info, menu.info] at observations
          simp only [observe, leftActive, rightActive, ↓reduceIte] at observations
          have recalls := congrArg Prod.fst (Option.some.inj observations)
          have equalDepth := (app.scheduled_decision_position initial horizon scheduler schedule
            scheduled who left right (menu.toRawTrace _ _ _ leftTrace)
              (menu.toRawTrace _ _ _ rightTrace) leftActive rightActive
                (congrArg List.length recalls)).2
          simpa only [menu.toRawTrace_length] using equalDepth

end Interaction.ReactiveApplication
