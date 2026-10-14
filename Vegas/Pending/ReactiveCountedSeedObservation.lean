/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedDecisionLaw
import Vegas.Pending.ReactiveCountedSeedPosterior
import Vegas.Pending.ReactiveCountedSeedOwnerFiber
import GameTheoryExtensions.Math.Probability.ConditionalProductMixture

/-! # Actual owner-observation conditioning of the local seed channel

The complete decision law retains hidden initial game inputs and residual
runtime state. Conditioning uses the actual native active-owner observation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}

local notation "app" => runtime.reactiveApplication leaks

/-- The native observation at the actual command/environment decision boundary. -/
def decisionObservation (point : graph.Inputs × (app).Command × (app).Execution) :
    (app).Info :=
  (app).observe owner (some ⟨0, point.2.1.actor? app, point.2.2⟩)

private theorem decisionObservation_active_eq
    (first second : graph.Inputs × (app).Command × (app).Execution)
    (acting : second.2.1 = .activate owner)
    (same : decisionObservation (owner := owner) (runtime := runtime) (leaks := leaks) first =
      decisionObservation (owner := owner) (runtime := runtime) (leaks := leaks) second) :
    first.2.1 = .activate owner ∧
      (first.2.2.recall owner, first.2.2.observe app owner) =
        (second.2.2.recall owner, second.2.2.observe app owner) := by
  classical
  have present : ((app).observe owner
      (some ⟨0, first.2.1.actor? app, first.2.2⟩)).isSome := by
    change (decisionObservation (owner := owner) first).isSome
    rw [same]
    simp only [decisionObservation, acting, ReactiveApplication.Command.actor?,
      ReactiveApplication.observe, ↓reduceIte, Option.isSome_some]
  have actorEq := ((app).observe_isSome owner
    (some ⟨0, first.2.1.actor? app, first.2.2⟩)).mp present
  change first.2.1.actor? app = some owner at actorEq
  have firstActing : first.2.1 = .activate owner := by
    cases commandEq : first.2.1 with
    | activate actor =>
        rw [commandEq] at actorEq
        change some actor = some owner at actorEq
        exact congrArg (fun actor : Player => (.activate actor : (app).Command))
          (Option.some.inj actorEq)
    | application operation => simp only [commandEq, ReactiveApplication.Command.actor?,
        reduceCtorEq] at actorEq
    | «include» id => simp only [commandEq, ReactiveApplication.Command.actor?,
        reduceCtorEq] at actorEq
    | wait => simp only [commandEq, ReactiveApplication.Command.actor?, reduceCtorEq] at actorEq
  refine ⟨firstActing, ?_⟩
  simpa only [decisionObservation, firstActing, acting, ReactiveApplication.Command.actor?,
    ReactiveApplication.observe, ↓reduceIte, Option.some.injEq] using same

variable [Fintype Player]

private theorem initial_menu_trace (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (setup : graph.Inputs) (supported : setup ∈ inputs.support) :
    ∃ scheduler : (app).Scheduler,
      Nonempty (((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial) 0
        scheduler).Trace
          (some ⟨0, none, ReactiveApplication.Execution.initial app (State.initial setup)⟩)) := by
  let scheduler : (app).Scheduler := fun _ _ => PMF.pure .wait
  let protocol := (bounds.onePacketMenu runtime leaks).protocol
    (inputs.map State.initial) 0 scheduler
  have running : ¬ protocol.terminal none := by change ¬ False; trivial
  obtain ⟨joint, available⟩ := protocol.progress none running
  refine ⟨scheduler, ⟨.extend .start joint ⟨running, available⟩ ?_⟩⟩
  change (some (⟨0, none, ReactiveApplication.Execution.initial app
      (State.initial setup)⟩ : (app).Control)) ∈
    (((inputs.map State.initial).map fun state =>
      some (⟨0, none, ReactiveApplication.Execution.initial app state⟩ : (app).Control))).support
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨State.initial setup, (PMF.mem_support_map_iff _ _ _).mpr ⟨setup, supported, rfl⟩, rfl⟩

variable (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)

private theorem decision_recovered_logs_eq
    (laws : (side : Bool) → PMF (A side)) (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (bounds.onePacketMenu runtime leaks).actions who past view)
    (owned : graph.actor? event = some owner) (count : Nat)
    (point : Bool → graph.Inputs × (app).Command × (app).Execution)
    (supported : ∀ side, point side ∈
      (controller.decisionLaw remainder laws inputs players count).support)
    (acting : ∀ side, (point side).2.1 = .activate owner)
    (ready : ∀ side, (point side).2.2.application.publicView.EventReady event)
    (unmissed : ∀ side, (point side).2.2.application.publicView.missedBindingBy owner = false)
    (informationEq : ((point false).2.2.recall owner, (point false).2.2.observe app owner) =
      ((point true).2.2.recall owner, (point true).2.2.observe app owner))
    (log : Bool → List (LocalSeedEntry graph (app).Command))
    (recovered : ∀ side, ∀ values ∈
        (((app).schedulerMixture (independentProduct laws) (fun values =>
          controller.fixedScheduler remainder
            (initialMemory (values false) (values true)))).posterior
            (point side).2.2.environmentRecall).support,
      (controller.replay remainder (initialMemory (values false) (values true))
        (point side).2.2.environmentRecall).log = log side) :
    log false = log true := by
  classical
  let family := fun values : (side : Bool) → A side =>
    controller.fixedScheduler remainder (initialMemory (values false) (values true))
  have seedPresent (side) :=
    (((app).schedulerMixture (independentProduct laws) family).posterior
      (point side).2.2.environmentRecall).support_nonempty
  choose values valueSupport using seedPresent
  have realized (side) : ∃ original,
      original ∈ ((app).runRounds (family (values side)) players count
        (ReactiveApplication.Execution.initial app (State.initial (point side).1))).support ∧
      .activate owner ∈ (family (values side) original.environmentRecall
        (original.observeEnvironment app)).support ∧
      (point side).2.2 ∈ (original.environmentStep app (.activate owner)).support := by
    obtain ⟨_, before, runs, chosen, observed⟩ :=
      controller.decisionLaw_support remainder laws inputs players count (point side)
        (supported side)
    rw [acting side] at chosen observed
    exact ((app).schedulerMixture_decision_of_posterior_support _ family players count
      (State.initial (point side).1) before (point side).2.2 (.activate owner) (values side)
        runs chosen observed (valueSupport side)).2
  choose original runs chosen observed using realized
  have sources (side) := initial_menu_trace (runtime := runtime) (leaks := leaks)
    bounds inputs (point side).1
    (controller.decisionLaw_support remainder laws inputs players count (point side)
      (supported side)).1
  choose scheduler sourceTrace using sources
  have applicationEq (side) : (point side).2.2.application = (original side).application := by
    have effects := observed side
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at effects
    obtain ⟨selected, possible, pointEq⟩ := (PMF.mem_support_map_iff _ _ _).mp effects
    rw [← pointEq]
    rfl
  have readyBefore (side) : (original side).application.publicView.EventReady event := by
    rw [← applicationEq side]
    exact ready side
  have clearBefore (side) :
      (original side).application.publicView.missedBindingBy owner = false := by
    rw [← applicationEq side]
    exact unmissed side
  have same := controller.runRounds_log_eq_of_owner_info (laws false) (laws true)
    remainder bounds inputs ordered domainEq players covered owned (fun side => (point side).1)
      (fun _ => 0) scheduler (fun _ => 0) (fun side => Classical.choice (sourceTrace side))
        (fun side => values side false) (fun side => values side true) (fun _ => count)
          original (fun side => (point side).2.2) runs chosen observed readyBefore clearBefore
            informationEq
  rw [recovered false (values false) (valueSupport false),
    recovered true (values true) (valueSupport true)] at same
  exact same

/-- Conditioning the actual joint decision law on a genuine clean ready
owner observation makes its filtered local seed independent of all residual
initial game inputs, command/execution state and other seed coordinates. -/
theorem ownerObservation_seed_product
    (laws : (side : Bool) → PMF (A side)) (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (bounds.onePacketMenu runtime leaks).actions who past view)
    (owned : graph.actor? event = some owner) (count : Nat)
    (witness : graph.Inputs × (app).Command × (app).Execution)
    (witnessSupport : witness ∈
      (controller.decisionLaw remainder laws inputs players count).support)
    (acting : witness.2.1 = .activate owner)
    (ready : witness.2.2.application.publicView.EventReady event)
    (unmissed : witness.2.2.application.publicView.missedBindingBy owner = false) :
    ∃ (log : List (LocalSeedEntry graph (app).Command))
      (localPositive : ∃ seed ∈ {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply}, seed ∈ (laws false).support)
      (residual : PMF ((graph.Inputs × (app).Command × (app).Execution) ×
        ((side : {side : Bool // side ≠ false}) → A side))),
      (∀ point ∈ (fiberPosterior (controller.decisionLaw remainder laws inputs players count)
          (decisionObservation (owner := owner))
            (decisionObservation (owner := owner) witness)).support,
        ∀ values ∈ (((app).schedulerMixture (independentProduct laws) (fun values =>
          controller.fixedScheduler remainder
            (initialMemory (values false) (values true)))).posterior
              point.2.2.environmentRecall).support,
          (controller.replay remainder (initialMemory (values false) (values true))
            point.2.2.environmentRecall).log = log) ∧
      (fiberPosterior (controller.seededDecisionLaw remainder laws inputs players count)
        (fun outcome => decisionObservation (owner := owner) outcome.1)
          (decisionObservation (owner := owner) witness)).map
            (fun outcome => (outcome.2 false,
              (outcome.1, fun side : {side : Bool // side ≠ false} => outcome.2 side))) =
        ((laws false).filter {seed | ∀ entry ∈ log,
          controller.reply seed entry.query = entry.reply} localPositive).bind fun localSeed =>
            residual.map (Prod.mk localSeed) := by
  classical
  let law := controller.decisionLaw remainder laws inputs players count
  let observe := decisionObservation (owner := owner) (runtime := runtime) (leaks := leaks)
  let conditioned := fiberPosterior law observe (observe witness)
  let draws := fun point : graph.Inputs × (app).Command × (app).Execution =>
    (((app).schedulerMixture (independentProduct laws) (fun values =>
      controller.fixedScheduler remainder (initialMemory (values false) (values true)))).posterior
        point.2.2.environmentRecall)
  have present : observe witness ∈ (law.map observe).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨witness, witnessSupport, rfl⟩
  have guarded (point) (supported : point ∈ conditioned.support) :
      point.2.1 = .activate owner ∧
      (point.2.2.recall owner, point.2.2.observe app owner) =
        (witness.2.2.recall owner, witness.2.2.observe app owner) ∧
      point.2.2.application.publicView.EventReady event ∧
      point.2.2.application.publicView.missedBindingBy owner = false := by
    have matched := (mem_support_fiberPosterior present supported).1
    obtain ⟨active, infoEq⟩ := decisionObservation_active_eq point witness acting matched
    have viewEq := congrArg Prod.snd infoEq
    have publicEq := congrArg (fun view : (app).PlayerView => view.application.publicView) viewEq
    change point.2.2.application.publicView = witness.2.2.application.publicView at publicEq
    refine ⟨active, infoEq, ?_, ?_⟩
    · rwa [publicEq]
    · rwa [publicEq]
  have decomposition (point) (supported : point ∈ conditioned.support) :
      ∃ (log : List (LocalSeedEntry graph (app).Command))
        (localPositive : ∃ seed ∈ {seed | ∀ entry ∈ log,
          controller.reply seed entry.query = entry.reply}, seed ∈ (laws false).support)
        (updated : (side : Bool) → PMF (A side)),
        (∀ values ∈ (draws point).support,
          (controller.replay remainder (initialMemory (values false) (values true))
            point.2.2.environmentRecall).log = log) ∧
        draws point = independentProduct updated ∧
        updated false = (laws false).filter {seed | ∀ entry ∈ log,
          controller.reply seed entry.query = entry.reply} localPositive := by
    have original := (mem_support_fiberPosterior present supported).2
    obtain ⟨setupSupport, before, reached, chosen, observed⟩ :=
      controller.decisionLaw_support remainder laws inputs players count point original
    obtain ⟨active, _, readyAtPoint, clearAtPoint⟩ := guarded point supported
    rw [active] at chosen observed
    obtain ⟨scheduler, ⟨trace⟩⟩ := initial_menu_trace (runtime := runtime) (leaks := leaks)
      bounds inputs point.1 setupSupport
    exact controller.posterior_ready_activation remainder laws bounds inputs ordered domainEq
      players
      covered owned point.1 0 scheduler 0 trace count before point.2.2 reached chosen observed
        readyAtPoint clearAtPoint
  choose logOf localPositive updated recovery product localEq using decomposition
  have witnessIn : witness ∈ conditioned.support := by
    rw [fiberPosterior_support law observe (observe witness) present]
    exact ⟨rfl, witnessSupport⟩
  let log := logOf witness witnessIn
  let localLaw := (laws false).filter {seed | ∀ entry ∈ log,
    controller.reply seed entry.query = entry.reply} (localPositive witness witnessIn)
  have sameLog (point) (supported : point ∈ conditioned.support) :
      logOf point supported = log := by
    have source := (mem_support_fiberPosterior present supported).2
    obtain ⟨pointActing, pointInfo, pointReady, pointClear⟩ := guarded point supported
    exact controller.decision_recovered_logs_eq remainder laws bounds inputs ordered domainEq
      players covered owned count (Bool.rec point witness)
        (by
          intro side
          cases side
          · exact source
          · exact witnessSupport)
        (by
          intro side
          cases side
          · exact pointActing
          · exact acting)
        (by
          intro side
          cases side
          · exact pointReady
          · exact ready)
        (by
          intro side
          cases side
          · exact pointClear
          · exact unmissed)
        pointInfo
        (Bool.rec (logOf point supported) log)
        (by
          intro side
          cases side
          · exact recovery point supported
          · exact recovery witness witnessIn)
  let factors := fun point : graph.Inputs × (app).Command × (app).Execution =>
    if supported : point ∈ conditioned.support then updated point supported else laws
  have products (point) (supported : point ∈ conditioned.support) :
      draws point = independentProduct (factors point) := by
    simpa only [factors, dite_eq_left supported] using product point supported
  have commons (point) (supported : point ∈ conditioned.support) :
      factors point false = localLaw := by
    simp only [factors, dite_eq_left supported]
    rw [localEq point supported]
    dsimp only [localLaw]
    congr 1
    rw [sameLog point supported]
  let residual := conditioned.bind fun point =>
    (independentProduct (fun side : {side : Bool // side ≠ false} => factors point side)).map
      (Prod.mk point)
  have integrated := fiberPosterior_tagged_product_splitAt law draws observe (observe witness)
    present factors products false localLaw commons
  refine ⟨log, localPositive witness witnessIn, residual, ?_, ?_⟩
  · intro point supported values valueSupport
    rw [recovery point supported values valueSupport]
    exact sameLog point supported
  · rw [controller.seededDecisionLaw_eq]
    exact integrated

end Vegas.EventGraphRuntime.LocalSeedController
