/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedCountedLog
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveLocalSeedRun
import Vegas.Pending.ReactiveLocalSeedSurvivorLog
import Vegas.Pending.ReactiveLocalSeedReplay
import Vegas.Pending.ReactiveCountedSeedOwnerLog
import Vegas.Pending.ReactiveCountedSeedEmissionLog
import Vegas.Pending.ReactiveLocalSeedActivationLog
import Interaction.ReactiveResponseAccounting
import Vegas.Pending.ReactiveSeedBayes

/-! # Actual seeded event completion from finite information sites

Actual Bayes controls and latent seeds recover genuine initialized runs.
A pending response aligns the physical recall and replay counters before
extracting the first actual local resolving reply.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {LocalSeed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks LocalSeed owner event)

local notation "app" => runtime.reactiveApplication leaks

private theorem resume_config (players : Player → (app).Policy) (actor : Option Player)
    (execution next : (app).Execution)
    (reached : next ∈ ((app).resume players actor execution).support) :
    next.application.config = execution.application.config := by
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | some actor =>
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ reached
      exact (runtime.reactive_respond_application leaks execution actor response).1

private theorem activation_config (players : Player → (app).Policy)
    (execution next : (app).Execution)
    (reached : next ∈ ((app).dispatch players (.activate owner) execution).support) :
    next.application.config = execution.application.config := by
  obtain ⟨middle, moved, responded⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [resume_config players _ middle next responded]
  obtain ⟨updated, observed, rfl⟩ := PMF.support_map .. ▸ moved
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ observed
  rfl

private theorem remainder_unfinished
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (players : Player → (app).Policy) (execution next : (app).Execution)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (reached : next ∈ ((app).dispatch players
      (remainder.choose memory.remainderSeed execution.environmentRecall
        (execution.observeEnvironment app)).2 execution).support) :
    event ∉ next.application.config.cut.completed := by
  obtain ⟨middle, moved, responded⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [resume_config players _ middle next responded]
  exact (remainder.safe memory.remainderSeed execution.environmentRecall
    (execution.observeEnvironment app)).2 execution middle rfl unfinished moved

/-- A first completion in the actual dispatch must be the selected seed's
resolving reply, recorded with its exact query in the private local log. -/
theorem dispatch_completed_resolution
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (players : Player → (app).Policy) (execution next : (app).Execution)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (completed : event ∈ next.application.config.cut.completed)
    (reached : next ∈ ((app).dispatch players
      (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).1 execution).support) :
    ∃ (query : CurrentSeedQuery graph) (command : (app).Command),
      controller.reply memory.localSeed query = .resolution command ∧
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).2.log =
            memory.log ++ [⟨query, .resolution command⟩] := by
  classical
  generalize stepEq : controller.step remainder memory execution.environmentRecall
    (execution.observeEnvironment app) = result at reached ⊢
  dsimp only [step] at stepEq
  split_ifs at stepEq with ready closed polled
  · exfalso
    exact remainder_unfinished remainder memory players execution next unfinished
      (by simpa only [← stepEq] using reached) completed
  · rw [← stepEq] at reached ⊢
    let query : CurrentSeedQuery graph :=
      ⟨runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app),
        memory.activationIndex⟩
    change next ∈ ((app).dispatch players
      (finishReply owner memory _ query (controller.reply memory.localSeed query)).1
        execution).support at reached
    cases answer : controller.reply memory.localSeed query with
    | activation =>
        simp only [answer, finishReply] at reached
        exact False.elim (unfinished
          ((activation_config players execution next reached) ▸ completed))
    | resolution command =>
        refine ⟨query, command, answer, ?_⟩
        rfl
    | exhausted =>
        simp only [answer, finishReply] at reached
        exact False.elim (remainder_unfinished remainder memory players execution next
          unfinished reached completed)
  · exfalso
    exact remainder_unfinished remainder memory players execution next unfinished
      (by simpa only [← stepEq] using reached) completed
  · exfalso
    exact remainder_unfinished remainder memory players execution next unfinished
      (by simpa only [← stepEq] using reached) completed

/-- If the selected unfinished event completes during an actual private
scheduler run, a new resolving query occurs after the starting local log. -/
theorem runJoint_completed_resolution
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (players : Player → (app).Policy) (count : Nat)
    (execution next : (app).Execution)
    (memory after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (completed : event ∈ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support) :
    ∃ (before : List (LocalSeedEntry graph (app).Command))
      (query : CurrentSeedQuery graph) (command : (app).Command)
      (later : List (LocalSeedEntry graph (app).Command)),
      after.log = memory.log ++ before ++ [⟨query, .resolution command⟩] ++ later := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact False.elim (unfinished completed)
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      by_cases done : event ∈ middle.application.config.cut.completed
      · obtain ⟨query, command, _, logged⟩ := controller.dispatch_completed_resolution
          remainder memory players execution middle unfinished done moved
        obtain ⟨later, laterEq⟩ := controller.runJoint_log_prefix localLaw remainderLaw
          remainder players count middle _ next after continued
        refine ⟨[], query, command, later, ?_⟩
        rw [← laterEq, logged]
        simp only [List.append_nil]
      · obtain ⟨before, query, command, later, logEq⟩ := ih middle _ done continued
        obtain ⟨front, frontEq⟩ := controller.step_log_prefix remainder memory
          execution.environmentRecall (execution.observeEnvironment app)
        refine ⟨front ++ before, query, command, later, ?_⟩
        rw [logEq, ← frontEq]
        simp only [List.append_assoc]

/-- A completed event has an actual first completing dispatch after a supported
unfinished run prefix, with a strictly smaller used-round count. -/
theorem runJoint_first_completion
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (players : Player → (app).Policy) (count : Nat)
    (execution next : (app).Execution)
    (memory after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (completed : event ∈ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support) :
    ∃ (used : Nat) (before final : (app).Execution)
      (prior : LocalSeedMemory runtime leaks LocalSeed RestSeed),
      used < count ∧
        (before, prior) ∈
          ((controller.implementation localLaw remainderLaw remainder).runJoint players used
            execution memory).support ∧
        event ∉ before.application.config.cut.completed ∧
        event ∈ final.application.config.cut.completed ∧
        final ∈ ((app).dispatch players
          (controller.step remainder prior before.environmentRecall
            (before.observeEnvironment app)).1 before).support ∧
        (next, after) ∈
          ((controller.implementation localLaw remainderLaw remainder).runJoint players
            (count - used - 1) final (controller.step remainder prior before.environmentRecall
              (before.observeEnvironment app)).2).support := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact False.elim (unfinished completed)
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      by_cases done : event ∈ middle.application.config.cut.completed
      · refine ⟨0, execution, middle, memory, Nat.zero_lt_succ _,
          (PMF.mem_support_pure_iff _ _).mpr rfl, unfinished, done, moved, ?_⟩
        simpa only [Nat.sub_zero, Nat.add_sub_cancel_right] using continued
      · obtain ⟨used, before, final, prior, within, supported, incomplete, complete, dispatched,
            suffix⟩ :=
          ih middle _ done continued
        refine ⟨used + 1, before, final, prior, by omega, ?_, incomplete, complete, dispatched, ?_⟩
        · rw [controller.runJoint_succ, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨middle, moved, supported⟩
        · simpa only [Nat.add_sub_add_right] using suffix

/-- The actual first completing service extends a genuinely surviving prefix
by one correctly counted resolving query. No local success law is assumed. -/
theorem runJoint_first_counted_resolution
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy) (entered : Nat)
    (preserves : ∀ execution memory next, controller.domain execution →
      execution.application.Invariant inputs →
      execution.application.activatedAt event = some entered →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next)
    (count : Nat) (execution next : (app).Execution)
    (memory after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (completed : event ∈ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support)
    (genuine : controller.domain execution) (valid : execution.application.Invariant inputs)
    (activated : execution.application.activatedAt event = some entered)
    (recalled : execution.InputRecall app) (counted : CountedQueryLog memory.log)
    (unresolved : ∀ entry ∈ memory.log,
      entry.reply = .activation ∨ entry.reply = .exhausted)
    (positiveMatch : positiveQueries memory.log =
      runtime.ownerActivationQueries leaks event (execution.recall owner))
    (indexMatch : memory.activationIndex =
      runtime.readyActivationCount leaks event (execution.recall owner))
    (clocks : exhaustedClocks memory.log =
      List.range (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).elapsed ++
      if memory.closedAt = some (runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed then
        [(runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed] else []) :
    ∃ (used : Nat) (before final : (app).Execution)
      (prior : LocalSeedMemory runtime leaks LocalSeed RestSeed)
      (query : CurrentSeedQuery graph) (command : (app).Command),
      used < count ∧
        (before, prior) ∈
          ((controller.implementation localLaw remainderLaw remainder).runJoint players used
            execution memory).support ∧
        event ∉ before.application.config.cut.completed ∧
        event ∈ final.application.config.cut.completed ∧
        final ∈ ((app).dispatch players
          (controller.step remainder prior before.environmentRecall
            (before.observeEnvironment app)).1 before).support ∧
        CountedQueryLog (prior.log ++ [⟨query, .resolution command⟩]) ∧
        (∀ entry ∈ prior.log, entry.reply = .activation ∨ entry.reply = .exhausted) ∧
        controller.reply prior.localSeed query = .resolution command ∧
        (controller.step remainder prior before.environmentRecall
          (before.observeEnvironment app)).2.log =
            prior.log ++ [⟨query, .resolution command⟩] ∧
        (next, after) ∈
          ((controller.implementation localLaw remainderLaw remainder).runJoint players
            (count - used - 1) final (controller.step remainder prior before.environmentRecall
              (before.observeEnvironment app)).2).support := by
  obtain ⟨used, before, final, prior, within, supported, incomplete, complete, dispatched,
      suffix⟩ :=
    controller.runJoint_first_completion localLaw remainderLaw remainder players count
      execution next memory after unfinished completed reached
  obtain ⟨priorCounted, priorUnresolved, priorPositive, priorIndex, priorClocks⟩ :=
    controller.runJoint_survivorLog localLaw remainderLaw remainder inputs players entered
      preserves used execution memory before prior incomplete supported genuine valid activated
        recalled counted unresolved positiveMatch indexMatch clocks
  have indexed : prior.activationIndex = (positiveQueries prior.log).length := by
    rw [priorPositive, runtime.ownerActivationQueries_length]
    exact priorIndex
  have finalCounted := controller.step_countedLog remainder prior before.environmentRecall
    (before.observeEnvironment app) priorCounted indexed priorClocks
  obtain ⟨query, command, answer, logged⟩ := controller.dispatch_completed_resolution
    remainder prior players before final incomplete complete dispatched
  refine ⟨used, before, final, prior, query, command, within, supported, incomplete, complete,
    dispatched, ?_, priorUnresolved, answer, logged, suffix⟩
  rwa [logged] at finalCounted

variable (remainder : SeedRemainderController runtime leaks RestSeed owner event)
  (localSeed : LocalSeed) (remainderSeed : RestSeed)

local notation "baseMemory" => initialMemory (runtime := runtime) (leaks := leaks)
  localSeed remainderSeed
local notation "recalledMemory" execution:max =>
  controller.replay remainder baseMemory
    (ReactiveApplication.Execution.environmentRecall execution)

/-- A genuine fixed-seed run reaches its first completion through a correctly
counted resolving transcript reconstructed from actual environment recall.
Every reply retains the original seed, including after arbitrary remainder commands. -/
theorem runRounds_first_counted_resolution
    (inputs : graph.Inputs) (players : Player → (app).Policy) (entered : Nat)
    (preserves : ∀ execution memory next, controller.domain execution →
      execution.application.Invariant inputs →
      execution.application.activatedAt event = some entered →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next)
    (count : Nat) (execution next : (app).Execution)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (completed : event ∈ next.application.config.cut.completed)
    (reached : next ∈ ((app).runRounds (controller.fixedScheduler remainder baseMemory)
      players count execution).support)
    (genuine : controller.domain execution) (valid : execution.application.Invariant inputs)
    (activated : execution.application.activatedAt event = some entered)
    (recalled : execution.InputRecall app)
    (counted : CountedQueryLog (recalledMemory execution).log)
    (unresolved : ∀ entry ∈ (recalledMemory execution).log,
      entry.reply = .activation ∨ entry.reply = .exhausted)
    (positiveMatch : positiveQueries (recalledMemory execution).log =
      runtime.ownerActivationQueries leaks event (execution.recall owner))
    (indexMatch : (recalledMemory execution).activationIndex =
      runtime.readyActivationCount leaks event (execution.recall owner))
    (clocks : exhaustedClocks (recalledMemory execution).log =
      List.range (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).elapsed ++
      if (recalledMemory execution).closedAt = some (runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed then
        [(runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).elapsed] else []) :
    ∃ (used : Nat) (before final : (app).Execution)
      (query : CurrentSeedQuery graph) (command : (app).Command),
      used < count ∧
        before ∈ ((app).runRounds (controller.fixedScheduler remainder baseMemory)
          players used execution).support ∧
        event ∉ before.application.config.cut.completed ∧
        event ∈ final.application.config.cut.completed ∧
        final ∈ ((app).dispatch players
          (controller.step remainder (recalledMemory before) before.environmentRecall
            (before.observeEnvironment app)).1 before).support ∧
        CountedQueryLog ((recalledMemory before).log ++ [⟨query, .resolution command⟩]) ∧
        (∀ entry ∈ (recalledMemory before).log,
          entry.reply = .activation ∨ entry.reply = .exhausted) ∧
        controller.reply localSeed query = .resolution command ∧
        (recalledMemory final).log =
          (recalledMemory before).log ++ [⟨query, .resolution command⟩] ∧
        next ∈ ((app).runRounds (controller.fixedScheduler remainder baseMemory) players
          (count - used - 1) final).support := by
  have joint : (next, recalledMemory next) ∈
      ((controller.implementation (PMF.pure localSeed) (PMF.pure remainderSeed) remainder).runJoint
        players count execution (recalledMemory execution)).support := by
    rw [controller.runJoint_replay]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨next, reached, rfl⟩
  obtain ⟨used, before, final, prior, query, command, within, supported, incomplete, complete,
      dispatched, recorded, priorUnresolved, _, logged, suffix⟩ :=
    controller.runJoint_first_counted_resolution (PMF.pure localSeed) (PMF.pure remainderSeed)
      remainder inputs players entered preserves count execution next (recalledMemory execution)
        (recalledMemory next) unfinished completed joint genuine valid activated recalled counted
          unresolved positiveMatch indexMatch clocks
  rw [controller.runJoint_replay] at supported
  obtain ⟨point, pointSupported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have pointEq : point = before := congrArg Prod.fst same
  subst point
  have priorEq : recalledMemory before = prior := congrArg Prod.snd same
  subst prior
  have finalReplay : recalledMemory final =
      (controller.step remainder (recalledMemory before) before.environmentRecall
        (before.observeEnvironment app)).2 := by
    rw [(app).dispatch_environmentRecall players _ before final dispatched]
    exact controller.replay_snoc remainder baseMemory before.environmentRecall _
  refine ⟨used, before, final, query, command, within, pointSupported, incomplete, complete,
    dispatched, recorded, priorUnresolved, ?_, ?_, ?_⟩
  · have answers := controller.replayFrom_answers remainder baseMemory [] final.environmentRecall
      (by simp only [initialMemory, List.not_mem_nil, false_implies, implies_true])
    apply answers ⟨query, .resolution command⟩
    change LocalSeedEntry.mk query (.resolution command) ∈ (recalledMemory final).log
    rw [finalReplay, logged]
    exact List.mem_append_right _ (by simp)
  · rw [finalReplay, logged]
  · rw [← finalReplay, controller.runJoint_replay] at suffix
    obtain ⟨point, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp suffix
    have identified : point = next := congrArg Prod.fst same
    exact identified ▸ supported

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {LocalSeed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks LocalSeed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- Actual supported clean owner decisions determine the complete replayed
query log by genuine owner information, with no query-log recovery premise. -/
theorem runRounds_response_log_signature
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (bounds.onePacketMenu runtime leaks).actions who past view)
    (owned : graph.actor? event = some owner)
    (setup : graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace
        (some ⟨remaining, none, ReactiveApplication.Execution.initial app (State.initial setup)⟩))
    (localSeed : LocalSeed) (remainderSeed : RestSeed)
    (count : Nat) (before active : (app).Execution)
    (reached : before ∈ ((app).runRounds
      (controller.fixedScheduler remainder (initialMemory localSeed remainderSeed)) players count
        (ReactiveApplication.Execution.initial app (State.initial setup))).support)
    (chosen : .activate owner ∈ (controller.fixedScheduler remainder
      (initialMemory localSeed remainderSeed) before.environmentRecall
        (before.observeEnvironment app)).support)
    (observed : active ∈ (before.environmentStep app (.activate owner)).support)
    (ready : before.application.publicView.EventReady event)
    (unmissed : before.application.publicView.missedBindingBy owner = false)
    (response : (app).Action) :
    let after := active.respond app owner response
    let memory := controller.replay remainder (initialMemory localSeed remainderSeed)
      after.environmentRecall
    after.application.Invariant setup ∧ after.InputRecall app ∧
      CountedQueryLog memory.log ∧
      (∀ entry ∈ memory.log, entry.reply = .activation ∨ entry.reply = .exhausted) ∧
      positiveQueries memory.log =
        runtime.ownerActivationQueries leaks event (after.recall owner) ∧
      memory.activationIndex = runtime.readyActivationCount leaks event (after.recall owner) ∧
      (∀ entry ∈ memory.log,
        entry.query.activationIndex <
          runtime.readyActivationCount leaks event (after.recall owner) ∧
        entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
          (after.recall owner) entry.query.activationIndex) ∧
      exhaustedClocks memory.log =
        List.range (runtime.environmentSeedInput leaks owner event
          (after.observeEnvironment app)).elapsed ++
        if memory.closedAt = some (runtime.environmentSeedInput leaks owner event
            (after.observeEnvironment app)).elapsed then
          [(runtime.environmentSeedInput leaks owner event
            (after.observeEnvironment app)).elapsed] else [] := by
  classical
  let memory := controller.replay remainder (initialMemory localSeed remainderSeed)
    before.environmentRecall
  let after := active.respond app owner response
  let replies : Player → (app).Policy := fun _ _ _ => PMF.pure response
  have joint : (before, memory) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        (ReactiveApplication.Execution.initial app (State.initial setup))
          (initialMemory localSeed remainderSeed)).support := by
    rw [controller.runJoint_initial]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨before, reached, rfl⟩
  obtain ⟨counted, unresolved, positives, indexed, clocks⟩ :=
    controller.runJoint_counted_ownerLog localLaw remainderLaw remainder bounds inputs ordered
      domainEq players covered owned setup horizon scheduler remaining trace localSeed remainderSeed
        count before memory joint ready unmissed
  have remembered := controller.runJoint_counted_log_emittedAtActivation localLaw remainderLaw
    remainder bounds inputs ordered domainEq players covered owned setup horizon scheduler remaining
      trace localSeed remainderSeed count before memory joint ready unmissed
  obtain ⟨extended, ⟨beforeTrace⟩⟩ := controller.runJoint_trace localLaw remainderLaw remainder
    (bounds.onePacketMenu runtime leaks) (inputs.map State.initial) players covered count horizon
      scheduler remaining (ReactiveApplication.Execution.initial app (State.initial setup))
        (initialMemory localSeed remainderSeed) before memory trace joint
  have genuine : controller.domain before := by
    rw [domainEq]
    exact runtime.countedSeedDomain_of_history leaks bounds inputs (horizon + count) extended
      ⟨remaining, none, before⟩ beforeTrace owner rfl unmissed
  have recalled := (app).history_inputRecall (inputs.map State.initial) (horizon + count) extended
    ((bounds.onePacketMenu runtime leaks).toRawTrace _ _ _ beforeTrace)
  obtain ⟨ticks, progress⟩ := controller.runJoint_progress localLaw remainderLaw remainder setup
    players count (ReactiveApplication.Execution.initial app (State.initial setup))
      (initialMemory localSeed remainderSeed) before memory (State.initial_invariant setup) joint
  have beforeValid := progress.invariant
  have activeApp : active.application = before.application := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at observed
    obtain ⟨selected, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
    rfl
  have physical : after.application.config = before.application.config :=
    (runtime.reactive_respond_application leaks active owner response).1.trans
      (congrArg State.config activeApp)
  have unfinished : event ∉ after.application.config.cut.completed := by
    rw [physical]
    exact ((before.application.publicView_eventReady event).mp ready).1
  have commandEq : (controller.step remainder memory before.environmentRecall
      (before.observeEnvironment app)).1 = .activate owner :=
    ((PMF.mem_support_pure_iff _ _).mp chosen).symm
  have dispatched : after ∈ ((app).dispatch replies
      (controller.step remainder memory before.environmentRecall
        (before.observeEnvironment app)).1 before).support := by
    rw [commandEq, ReactiveApplication.dispatch, PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨active, observed, ?_⟩
    change after ∈ ((PMF.pure response).map (active.respond app owner)).support
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨response, by simp, rfl⟩
  have indexedLength : memory.activationIndex = (positiveQueries memory.log).length := by
    rw [positives, runtime.ownerActivationQueries_length]
    exact indexed
  have afterCounted := controller.step_countedLog remainder memory before.environmentRecall
    (before.observeEnvironment app) counted indexedLength clocks
  have afterUnresolved := controller.dispatch_log_unresolved remainder setup replies before after
    memory beforeValid genuine unfinished unresolved dispatched
  have afterMatched := controller.dispatch_ownerLog remainder memory before after replies genuine
    recalled positives indexed dispatched
  have afterRemembered := controller.dispatch_log_emittedAtActivation remainder memory replies
    before after recalled ready indexed remembered dispatched
  have priorBound : ∀ entry ∈ (controller.step remainder memory before.environmentRecall
      (before.observeEnvironment app)).2.log,
      entry.query.activationIndex ≤
        runtime.readyActivationCount leaks event (before.recall owner) :=
    by
      rw [controller.activation_log remainder memory before genuine recalled ready commandEq]
      intro entry member
      rcases List.mem_append.mp member with earlier | last
      · exact (remembered entry earlier).1
      · cases List.mem_singleton.mp last
        exact Nat.le_of_eq indexed
  have afterCount := congrArg List.length (runtime.dispatch_ownerActivationQueries leaks replies
    before after _ owner event dispatched)
  rw [commandEq, ite_eq_left ⟨rfl, ready⟩, List.length_append, List.length_singleton,
    runtime.ownerActivationQueries_length, runtime.ownerActivationQueries_length] at afterCount
  have afterRememberedStrict : ∀ entry ∈ (controller.step remainder memory before.environmentRecall
      (before.observeEnvironment app)).2.log,
      entry.query.activationIndex < runtime.readyActivationCount leaks event (after.recall owner) ∧
      entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        (after.recall owner) entry.query.activationIndex := by
    intro entry member
    refine ⟨?_, (afterRemembered entry member).2⟩
    rw [afterCount]
    exact Nat.lt_succ_of_le (priorBound entry member)
  have enteredPresent := (beforeValid.activated_iff event).mpr
    ⟨(before.application.publicView_eventReady event).mp ready, by simp [owned]⟩
  obtain ⟨entered, enteredEq⟩ := Option.isSome_iff_exists.mp enteredPresent
  have afterClocks := controller.dispatch_exhaustionRange remainder setup replies before after
    memory entered beforeValid enteredEq unfinished genuine clocks dispatched
  have afterValid := (runtime.reactive_dispatch_progress leaks setup replies before after _
    beforeValid dispatched).invariant
  have activeRecall := (app).environment_inputRecall before active (.activate owner)
    recalled observed
  have afterRecall := (app).respond_inputRecall active owner response activeRecall
  have replayEq : controller.replay remainder (initialMemory localSeed remainderSeed)
      after.environmentRecall =
        (controller.step remainder memory before.environmentRecall
          (before.observeEnvironment app)).2 := by
    rw [(app).dispatch_environmentRecall replies _ before after dispatched, commandEq]
    exact controller.replay_snoc remainder (initialMemory localSeed remainderSeed)
      before.environmentRecall ⟨before.observeEnvironment app, .activate owner⟩
  dsimp only
  rw [replayEq]
  exact ⟨afterValid, afterRecall, afterCounted, afterUnresolved, afterMatched.1, afterMatched.2,
    afterRememberedStrict, afterClocks⟩

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)
  (laws : (side : Bool) → PMF (A side)) (bounds : MessageBounds graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => runtime.reactiveApplication leaks
local notation "family" => fun values : (side : Bool) → A side =>
  controller.fixedScheduler remainder (initialMemory (values false) (values true))
local notation "mixture" => ReactiveApplication.schedulerMixture app
  (independentProduct laws) family
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "model" => ReactiveApplication.ResponseMenu.information menu
  (inputs.map State.initial) horizon (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "players" profile =>
  ReactiveApplication.ResponseMenu.decodeProfile menu
    (inputs.map State.initial) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler mixture) profile
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => independentProduct laws
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
    (ReactiveApplication.Execution.environmentRecall
      (ReactiveApplication.Control.execution current))

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (bounds.onePacketMenu runtime leaks)
    (PMF.map (State.initial (graph := graph)) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.schedulerMixture (runtime.reactiveApplication leaks)
        (independentProduct laws) (fun values => controller.fixedScheduler remainder
          (initialMemory (values false) (values true)))))))]

/-- Every supported actual Bayes control and latent original seed has a genuine
initialized fixed-seed run ending at that owner's selected activation. -/
theorem bayesBelief_fixed_activation
    (profile : ∀ who, (model).BehavioralPolicy who)
    (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (current : (app).Control) (acting : current.actor = some owner)
    (supported : some current ∈ (((model).bayesBelief profile owner site
      ((menu).decisionInformationAntichain (inputs.map State.initial) horizon
        (mixture).scheduler owner site) positive).map (β := (app).ProtocolState)
          (fun history => history.1.state)).support)
    (values : (side : Bool) → A side)
    (valueSupport : values ∈ ((mixture).posterior current.execution.environmentRecall).support) :
    ∃ (setup : graph.Inputs) (count : Nat) (before : (app).Execution),
      setup ∈ inputs.support ∧ count < horizon ∧ values ∈ (independentProduct laws).support ∧
        before ∈ ((app).runRounds (family values) (players profile) count
          (ReactiveApplication.Execution.initial app (State.initial setup))).support ∧
        .activate owner ∈ (family values before.environmentRecall
          (before.observeEnvironment app)).support ∧
        current.execution ∈ (before.environmentStep app (.activate owner)).support := by
  classical
  have horizonPositive := (menu).informationSite_horizon_pos
    (inputs.map State.initial) horizon (mixture).scheduler owner site
  let : NeZero horizon := ⟨ne_of_gt horizonPositive⟩
  let counts := (PMF.uniformOfFintype (Fin horizon)).map Fin.val
  let source := controller.seededSampledRoundDecisionLaw remainder laws inputs
    (players profile) counts
  let observe := fun outcome :
      (Nat × graph.Inputs × (app).Command × (app).Execution) × ((side : Bool) → A side) =>
    decisionObservation (owner := owner) outcome.1.2
  have paired : ((some current : (app).ProtocolState), values) ∈
      ((((model).bayesBelief profile owner site
        ((menu).decisionInformationAntichain (inputs.map State.initial) horizon
          (mixture).scheduler owner site) positive).map (β := (app).ProtocolState)
            (fun history => history.1.state)).bind
            fun state => (draws state).map (Prod.mk state)).support := by
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨some current, supported, ?_⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨values, valueSupport, rfl⟩
  have joint := controller.bayesBelief_seededDecision remainder laws bounds inputs horizon
    profile site positive
  have original := (congrArg
    (fun law : PMF ((app).ProtocolState × ((side : Bool) → A side)) =>
      (some current, values) ∈ law.support) joint).mpr paired
  obtain ⟨outcome, conditioned, same⟩ := (PMF.mem_support_map_iff _ _ _).mp original
  have sourceSupport : outcome ∈ source.support := by
    by_cases present : site.1 ∈ (source.map observe).support
    · exact (mem_support_fiberPosterior present conditioned).2
    · rwa [fiberPosterior_of_not_mem_support source observe present] at conditioned
  have marginal := controller.seededSampledRoundDecisionLaw_eq remainder laws inputs
    (players profile) counts
  have tagged := (congrArg (fun law :
      PMF ((Nat × graph.Inputs × (app).Command × (app).Execution) × ((side : Bool) → A side)) =>
    outcome ∈ law.support) marginal).mp sourceSupport
  rw [PMF.support_bind] at tagged
  obtain ⟨point, pointSupport, tagged⟩ := Set.mem_iUnion₂.mp tagged
  obtain ⟨latent, _, pairEq⟩ := (PMF.mem_support_map_iff _ _ _).mp tagged
  have pointSupported : outcome.1 ∈
      (controller.sampledRoundDecisionLaw remainder laws inputs (players profile) counts).support :=
    (congrArg Prod.fst pairEq) ▸ pointSupport
  obtain ⟨countSupport, decisionSupport⟩ := controller.sampledRoundDecisionLaw_support
    remainder laws inputs (players profile) counts outcome.1 pointSupported
  obtain ⟨setupSupport, before, runs, chosen, observed⟩ := controller.decisionLaw_support
    remainder laws inputs (players profile) outcome.1.1 outcome.1.2 decisionSupport
  have stateEq := congrArg Prod.fst same
  change some (⟨horizon - outcome.1.1 - 1, outcome.1.2.2.1.actor? app,
    outcome.1.2.2.2⟩ : (app).Control) = some current at stateEq
  have executionEq := congrArg ReactiveApplication.Control.execution (Option.some.inj stateEq)
  change outcome.1.2.2.2 = current.execution at executionEq
  have actorEq := (congrArg ReactiveApplication.Control.actor
    (Option.some.inj stateEq)).trans acting
  have commandEq : outcome.1.2.2.1 = .activate owner := by
    change outcome.1.2.2.1.actor? app = some owner at actorEq
    generalize named : outcome.1.2.2.1 = command at actorEq ⊢
    cases command with
    | activate actor =>
        exact congrArg (fun actor : Player => (.activate actor : (app).Command))
          (Option.some.inj actorEq)
    | application operation => cases actorEq
    | «include» id => cases actorEq
    | wait => cases actorEq
  rw [commandEq] at chosen observed
  have latentSupport : values ∈
      ((mixture).posterior outcome.1.2.2.2.environmentRecall).support := by
    rw [executionEq]
    exact valueSupport
  obtain ⟨priorSupport, actualBefore, actualRuns, actualChosen, actualObserved⟩ :=
    (app).schedulerMixture_decision_of_posterior_support (independentProduct laws) family
      (players profile) outcome.1.1 (State.initial outcome.1.2.1) before outcome.1.2.2.2
        (.activate owner) values runs chosen observed latentSupport
  obtain ⟨index, _, indexEq⟩ := (PMF.mem_support_map_iff _ _ _).mp countSupport
  refine ⟨outcome.1.2.1, outcome.1.1, actualBefore, setupSupport, ?_, priorSupport, actualRuns,
    actualChosen, ?_⟩
  · rw [← indexEq]
    exact index.isLt
  · rwa [executionEq] at actualObserved

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)
  (laws : (side : Bool) → PMF (A side)) (bounds : MessageBounds graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => runtime.reactiveApplication leaks
local notation "family" => fun values : (side : Bool) → A side =>
  controller.fixedScheduler remainder (initialMemory (values false) (values true))
local notation "mixture" => ReactiveApplication.schedulerMixture app
  (independentProduct laws) family
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "model" => ReactiveApplication.ResponseMenu.information menu
  (inputs.map State.initial) horizon (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "players" profile =>
  ReactiveApplication.ResponseMenu.decodeProfile menu
    (inputs.map State.initial) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler mixture) profile
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => independentProduct laws
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
    (ReactiveApplication.Execution.environmentRecall
      (ReactiveApplication.Control.execution current))

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (bounds.onePacketMenu runtime leaks)
    (PMF.map (State.initial (graph := graph)) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.schedulerMixture (runtime.reactiveApplication leaks)
        (independentProduct laws) (fun values => controller.fixedScheduler remainder
          (initialMemory (values false) (values true)))))))]

/-- A genuine active Bayes history initializes all replay counters after its
actual legal response, for each supported original persistent scheduler seed. -/
theorem bayesBelief_response_log_signature
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (owned : graph.actor? event = some owner)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (current : (app).Control) (acting : current.actor = some owner)
    (supported : some current ∈ (((model).bayesBelief profile owner site
      ((menu).decisionInformationAntichain (inputs.map State.initial) horizon
        (mixture).scheduler owner site) positive).map (β := (app).ProtocolState)
          (fun history => history.1.state)).support)
    (values : (side : Bool) → A side)
    (valueSupport : values ∈ ((mixture).posterior current.execution.environmentRecall).support)
    (ready : current.execution.application.publicView.EventReady event)
    (unmissed : current.execution.application.publicView.missedBindingBy owner = false)
    (response : (app).Action)
    (permitted : response ∈ (menu).actions owner (current.execution.recall owner)
      (current.execution.observe app owner)) :
    let after := current.execution.respond app owner response
    let memory := controller.replay remainder (initialMemory (values false) (values true))
      after.environmentRecall
    ∃ (setup : graph.Inputs) (entered : Nat),
      setup ∈ inputs.support ∧ after.application.Invariant setup ∧ after.InputRecall app ∧
      controller.domain after ∧ after.application.activatedAt event = some entered ∧
      CountedQueryLog memory.log ∧
      (∀ entry ∈ memory.log, entry.reply = .activation ∨ entry.reply = .exhausted) ∧
      positiveQueries memory.log =
        runtime.ownerActivationQueries leaks event (after.recall owner) ∧
      memory.activationIndex = runtime.readyActivationCount leaks event (after.recall owner) ∧
      (∀ entry ∈ memory.log,
        entry.query.activationIndex <
          runtime.readyActivationCount leaks event (after.recall owner) ∧
        entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
          (after.recall owner) entry.query.activationIndex) ∧
      exhaustedClocks memory.log =
        List.range (runtime.environmentSeedInput leaks owner event
          (after.observeEnvironment app)).elapsed ++
        if memory.closedAt = some (runtime.environmentSeedInput leaks owner event
            (after.observeEnvironment app)).elapsed then
          [(runtime.environmentSeedInput leaks owner event
            (after.observeEnvironment app)).elapsed] else [] := by
  classical
  let after := current.execution.respond app owner response
  obtain ⟨setup, count, before, setupSupport, _, _, runs, chosen, observed⟩ :=
    controller.bayesBelief_fixed_activation remainder laws bounds inputs horizon profile site
      positive current acting supported values valueSupport
  have initialSupported : State.initial setup ∈ (inputs.map State.initial).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨setup, setupSupport, rfl⟩
  let startup : (app).Scheduler := fun _ _ => PMF.pure .wait
  obtain ⟨initialTrace⟩ := (menu).trace_initial (inputs.map State.initial) 0 startup
    (State.initial setup) initialSupported
  have covered : ∀ who previous view action,
      action ∈ ((players profile) who previous view).support →
      action ∈ (menu).actions who previous view := by
    intro who previous view action selected
    exact (menu).decode_embedPolicy_covered (inputs.map State.initial) horizon
      (mixture).scheduler who (profile who) previous view action selected
  have unchanged : current.execution.application = before.application := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at observed
    obtain ⟨selected, _, effectEq⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
    have appEq := congrArg (fun execution : (app).Execution => execution.application) effectEq
    change before.application = current.execution.application at appEq
    exact appEq.symm
  have beforeReady : before.application.publicView.EventReady event := by rwa [← unchanged]
  have beforeClear : before.application.publicView.missedBindingBy owner = false := by
    rwa [← unchanged]
  obtain ⟨valid, recalled, counted, unresolved, positives, indexed, remembered, clocks⟩ :=
    controller.runRounds_response_log_signature (laws false) (laws true) remainder bounds inputs
      ordered domainEq (players profile) covered owned setup 0 startup 0 initialTrace
        (values false) (values true) count before current.execution runs chosen observed
          beforeReady beforeClear response
  obtain ⟨history, _, stateEq⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have activeTrace : ((menu).protocol (inputs.map State.initial) horizon
      (mixture).scheduler).Trace (some ⟨current.remaining, some owner, current.execution⟩) := by
    have trace := stateEq ▸ history.1.trace
    convert trace using 1
    cases current
    simp_all only
  obtain ⟨respondedTrace⟩ := (menu).trace_respond (inputs.map State.initial) horizon
    (mixture).scheduler current.remaining current.execution owner response activeTrace permitted
  have publicEq := (runtime.reactive_respond_application leaks current.execution owner response).2
  have afterClear : after.application.publicView.missedBindingBy owner = false := by
    change (current.execution.respond app owner response).application.publicView.missedBindingBy
      owner = false
    rw [publicEq]
    exact unmissed
  have genuine : controller.domain after := by
    rw [domainEq]
    exact runtime.countedSeedDomain_of_history leaks bounds inputs horizon (mixture).scheduler
      ⟨current.remaining, none, after⟩ respondedTrace owner rfl afterClear
  have afterReady : after.application.publicView.EventReady event := by
    change (current.execution.respond app owner response).application.publicView.EventReady event
    rw [publicEq]
    exact ready
  have present := (valid.activated_iff event).mpr
    ⟨(after.application.publicView_eventReady event).mp afterReady, by simp [owned]⟩
  obtain ⟨entered, enteredEq⟩ := Option.isSome_iff_exists.mp present
  exact ⟨setup, entered, setupSupport, valid, recalled, genuine, enteredEq, counted, unresolved,
    positives, indexed, remembered, clocks⟩

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)
  (laws : (side : Bool) → PMF (A side)) (bounds : MessageBounds graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => runtime.reactiveApplication leaks
local notation "family" => fun values : (side : Bool) → A side =>
  controller.fixedScheduler remainder (initialMemory (values false) (values true))
local notation "mixture" => ReactiveApplication.schedulerMixture app
  (independentProduct laws) family
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "model" => ReactiveApplication.ResponseMenu.information menu
  (inputs.map State.initial) horizon (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "players" profile =>
  ReactiveApplication.ResponseMenu.decodeProfile menu
    (inputs.map State.initial) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler mixture) profile
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => independentProduct laws
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
    (ReactiveApplication.Execution.environmentRecall
      (ReactiveApplication.Control.execution current))

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (bounds.onePacketMenu runtime leaks)
    (PMF.map (State.initial (graph := graph)) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.schedulerMixture (runtime.reactiveApplication leaks)
        (independentProduct laws) (fun values => controller.fixedScheduler remainder
          (initialMemory (values false) (values true)))))))]

/-- Every completed selected event in the actual remaining continuation from
a supported finite Bayes decision is caused by an original-seed resolving query.
Initial replay invariants come from the genuine pending response. -/
theorem bayesBelief_response_first_resolution
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (owned : graph.actor? event = some owner)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (current : (app).Control) (acting : current.actor = some owner)
    (supported : some current ∈ (((model).bayesBelief profile owner site
      ((menu).decisionInformationAntichain (inputs.map State.initial) horizon
        (mixture).scheduler owner site) positive).map (β := (app).ProtocolState)
          (fun history => history.1.state)).support)
    (values : (side : Bool) → A side)
    (valueSupport : values ∈ ((mixture).posterior current.execution.environmentRecall).support)
    (ready : current.execution.application.publicView.EventReady event)
    (unmissed : current.execution.application.publicView.missedBindingBy owner = false)
    (response : (app).Action)
    (permitted : response ∈ (menu).actions owner (current.execution.recall owner)
      (current.execution.observe app owner))
    (future : Player → (app).Policy)
    (coveredFuture : ∀ who past view action, action ∈ (future who past view).support →
      action ∈ (menu).actions who past view)
    (next : (app).Execution)
    (reached : next ∈ ((app).runRounds (family values) future current.remaining
      (current.execution.respond app owner response)).support)
    (completed : event ∈ next.application.config.cut.completed) :
    let start := current.execution.respond app owner response
    let memory := fun execution : (app).Execution => controller.replay remainder
      (initialMemory (values false) (values true)) execution.environmentRecall
    ∃ (used : Nat) (before final : (app).Execution)
      (query : CurrentSeedQuery graph) (command : (app).Command),
      used < current.remaining ∧
        before ∈ ((app).runRounds (family values) future used start).support ∧
        event ∉ before.application.config.cut.completed ∧
        event ∈ final.application.config.cut.completed ∧
        final ∈ ((app).dispatch future
          (controller.step remainder (memory before) before.environmentRecall
            (before.observeEnvironment app)).1 before).support ∧
        CountedQueryLog ((memory before).log ++ [⟨query, .resolution command⟩]) ∧
        (∀ entry ∈ (memory before).log,
          entry.reply = .activation ∨ entry.reply = .exhausted) ∧
        controller.reply (values false) query = .resolution command ∧
        (memory final).log = (memory before).log ++ [⟨query, .resolution command⟩] ∧
        next ∈ ((app).runRounds (family values) future
          (current.remaining - used - 1) final).support := by
  classical
  let after := current.execution.respond app owner response
  obtain ⟨setup, entered, _, valid, recalled, genuine, enteredEq, counted, unresolved,
      positiveMatch, indexMatch, _, clocks⟩ :=
    controller.bayesBelief_response_log_signature remainder laws bounds inputs horizon ordered
      domainEq owned profile site positive current acting supported values valueSupport ready
        unmissed response permitted
  have publicEq := (runtime.reactive_respond_application leaks current.execution owner response).2
  have afterReady : after.application.publicView.EventReady event := by
    change (current.execution.respond app owner response).application.publicView.EventReady event
    rw [publicEq]
    exact ready
  have unfinished := ((after.application.publicView_eventReady event).mp afterReady).1
  have preserves : ∀ execution memory next, controller.domain execution →
      execution.application.Invariant setup →
      execution.application.activatedAt event = some entered →
      next ∈ ((app).dispatch future
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next := by
    intro execution memory next genuine valid active moved incomplete
    rw [domainEq] at genuine ⊢
    exact runtime.countedSeedDomain_dispatch_of_activated_survives leaks bounds inputs ordered
      future coveredFuture owner event owned execution next genuine setup valid entered active
        _ moved incomplete
  exact controller.runRounds_first_counted_resolution remainder (values false) (values true)
    setup future entered preserves current.remaining after next unfinished completed reached
      genuine valid enteredEq recalled counted unresolved positiveMatch indexMatch clocks

end Vegas.EventGraphRuntime.LocalSeedController

end
