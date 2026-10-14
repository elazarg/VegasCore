/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountedSeedDecisionLog
import Vegas.Pending.ReactiveLocalSeedRecoveredPosterior
import Vegas.Pending.ReactiveLocalSeedTranscript
import Interaction.ReactiveSchedulerSeedSupport

/-! # Actual seed posterior at a genuine clean unsent owner decision

Every supported posterior seed realizes a genuine original execution at the
same active-owner observation. Actual query-log recovery fixes its raw log,
so the concrete scheduler posterior factors with the locally filtered seed.
-/

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

local notation "app" => runtime.reactiveApplication leaks

omit [Fintype Player] in
private theorem activation_application (before active : (app).Execution)
    (observed : active ∈ (before.environmentStep app (.activate owner)).support) :
    active.application = before.application := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at observed
  obtain ⟨selected, possible, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
  rfl

omit [Fintype Player] in
private theorem follows_of_fixed_decision
    (laws : (side : Bool) → PMF (A side)) (players : Player → (app).Policy)
    (state : State graph) (count : Nat) (values : (side : Bool) → A side)
    (before active : (app).Execution)
    (reached : before ∈ ((app).runRounds (controller.fixedScheduler remainder
      (initialMemory (values false) (values true))) players count
        (ReactiveApplication.Execution.initial app state)).support)
    (chosen : .activate owner ∈ (controller.fixedScheduler remainder
      (initialMemory (values false) (values true)) before.environmentRecall
        (before.observeEnvironment app)).support)
    (observed : active ∈ (before.environmentStep app (.activate owner)).support) :
    controller.followsFrom remainder (initialMemory (values false) (values true)) []
      active.environmentRecall := by
  let initial : LocalSeedMemory runtime leaks (A false) (A true) :=
    initialMemory (values false) (values true)
  have joint : (before, controller.replay remainder initial before.environmentRecall) ∈
      ((controller.implementation (laws false) (laws true) remainder).runJoint players count
        (ReactiveApplication.Execution.initial app state) initial).support := by
    rw [controller.runJoint_initial]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨before, reached, rfl⟩
  obtain ⟨suffix, recordEq, compatible, _⟩ := controller.runJoint_transcript remainder
    (laws false) (laws true) players count (ReactiveApplication.Execution.initial app state)
      initial before (controller.replay remainder initial before.environmentRecall) joint
  change before.environmentRecall = [] ++ suffix at recordEq
  simp only [List.nil_append] at recordEq
  change controller.followsFrom remainder initial [] suffix at compatible
  have beforeCompatible : controller.followsFrom remainder initial [] before.environmentRecall := by
    rwa [recordEq]
  rw [(app).environmentStep_environmentRecall before active (.activate owner) observed]
  apply (controller.follows_snoc remainder initial before.environmentRecall
    ⟨before.observeEnvironment app, .activate owner⟩).mpr
  exact ⟨beforeCompatible, ((PMF.mem_support_pure_iff _ _).mp chosen).symm⟩

/-- The concrete scheduler posterior at an actual clean unsent active-owner
site has the product law obtained by filtering exactly its recovered local queries. -/
theorem posterior_unsent_activation
    (laws : (side : Bool) → PMF (A side))
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
    (count : Nat) (before active : (app).Execution)
    (reached : before ∈ ((app).runRounds
      ((app).schedulerMixture (independentProduct laws) (fun values =>
        controller.fixedScheduler remainder (initialMemory (values false) (values true)))).scheduler
          players count (ReactiveApplication.Execution.initial app (State.initial setup))).support)
    (chosen : .activate owner ∈ (((app).schedulerMixture (independentProduct laws) (fun values =>
      controller.fixedScheduler remainder (initialMemory (values false) (values true)))).scheduler
        before.environmentRecall (before.observeEnvironment app)).support)
    (observed : active ∈ (before.environmentStep app (.activate owner)).support)
    (ready : active.application.publicView.EventReady event)
    (unmissed : active.application.publicView.missedBindingBy owner = false)
    (empty : (runtime.ownerSeedInput leaks event (active.recall owner)
      (active.observe app owner)).emitted = []) :
    ∃ (log : List (LocalSeedEntry graph (app).Command))
      (localPositive : ∃ seed ∈ {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply}, seed ∈ (laws false).support)
      (updated : (side : Bool) → PMF (A side)),
      (∀ values ∈
        (((app).schedulerMixture (independentProduct laws) (fun values =>
          controller.fixedScheduler remainder
            (initialMemory (values false) (values true)))).posterior
              active.environmentRecall).support,
        (controller.replay remainder (initialMemory (values false) (values true))
          active.environmentRecall).log = log) ∧
      (((app).schedulerMixture (independentProduct laws) (fun values =>
        controller.fixedScheduler remainder
          (initialMemory (values false) (values true)))).posterior active.environmentRecall) =
            independentProduct updated ∧
      updated false = (laws false).filter {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply} localPositive := by
  classical
  let family := fun values : (side : Bool) → A side =>
    controller.fixedScheduler remainder (initialMemory (values false) (values true))
  let current := ((app).schedulerMixture (independentProduct laws) family).posterior
    active.environmentRecall
  have actual (values) (supported : values ∈ current.support) :
      values ∈ (independentProduct laws).support ∧ ∃ original,
        original ∈ ((app).runRounds (family values) players count
          (ReactiveApplication.Execution.initial app (State.initial setup))).support ∧
        .activate owner ∈ (family values original.environmentRecall
          (original.observeEnvironment app)).support ∧
        active ∈ (original.environmentStep app (.activate owner)).support :=
    (app).schedulerMixture_decision_of_posterior_support _ family players count
      (State.initial setup) before active (.activate owner) values reached chosen observed supported
  have signature (values) (supported : values ∈ current.support) :
      ∃ word : List Bool,
        (controller.replay remainder (initialMemory (values false) (values true))
          active.environmentRecall).log =
            encodeUnsentLogFrom (runtime := runtime) (leaks := leaks) 0 0 word ∧
        positiveQueries (encodeUnsentLogFrom (runtime := runtime) (leaks := leaks) 0 0 word) =
          runtime.ownerActivationQueries leaks event (active.recall owner) ++
            [⟨runtime.ownerSeedInput leaks event (active.recall owner) (active.observe app owner),
                runtime.readyActivationCount leaks event (active.recall owner)⟩] ∧
        (exhaustedClocks
          (encodeUnsentLogFrom (runtime := runtime) (leaks := leaks) 0 0 word)).length =
            (runtime.ownerSeedInput leaks event (active.recall owner)
              (active.observe app owner)).elapsed := by
    obtain ⟨_, original, runs, commands, effects⟩ := actual values supported
    have unchanged := activation_application original active effects
    apply controller.runRounds_unsent_activation_signature (laws false) (laws true) remainder
      bounds inputs ordered domainEq players covered owned setup horizon scheduler remaining trace
        (values false) (values true) count original active runs commands effects
    · rwa [← unchanged]
    · rwa [← unchanged]
    · exact empty
  obtain ⟨witness, witnessSupport⟩ := current.support_nonempty
  obtain ⟨word, wordLog, wordPositive, wordClock⟩ := signature witness witnessSupport
  let log := (controller.replay remainder (initialMemory (witness false) (witness true))
    active.environmentRecall).log
  have recovered : ∀ values ∈ current.support,
      (controller.replay remainder (initialMemory (values false) (values true))
        active.environmentRecall).log = log := by
    intro values supported
    obtain ⟨other, otherLog, otherPositive, otherClock⟩ := signature values supported
    have same := encodeUnsentLogFrom_signature_injective other word 0 0
      (otherPositive.trans wordPositive.symm) (otherClock.trans wordClock.symm)
    dsimp only [log]
    rw [otherLog, wordLog, same]
  obtain ⟨priorSupport, original, runs, commands, effects⟩ := actual witness witnessSupport
  have compatible := controller.follows_of_fixed_decision remainder laws players
    (State.initial setup) count witness original active runs commands effects
  have positive : ∃ values ∈ {values : (side : Bool) → A side |
        controller.followsFrom remainder (initialMemory (values false) (values true)) []
            active.environmentRecall ∧
          (controller.replay remainder (initialMemory (values false) (values true))
            active.environmentRecall).log = log}, values ∈ (independentProduct laws).support :=
    ⟨witness, ⟨compatible, rfl⟩, priorSupport⟩
  obtain ⟨localPositive, updated, productEq, localEq⟩ :=
    controller.posterior_of_recovered_log remainder laws active.environmentRecall log positive
      recovered
  exact ⟨log, localPositive, updated, recovered, productEq, localEq⟩

end Vegas.EventGraphRuntime.LocalSeedController
