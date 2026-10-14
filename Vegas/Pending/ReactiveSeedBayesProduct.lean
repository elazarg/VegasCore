/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSeedBayes
import Vegas.Pending.ReactiveSeedDecisionFields

/-! # Local seed filtering at genuine finite native information sites -/

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


/-- At a genuine clean ready native decision site, standard Bayes conditioning
of the original immutable seed law separates the locally filtered seed from
all remaining seed coordinates and the full current runtime control. -/
theorem bayesBelief_seed_product
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (owned : graph.actor? event = some owner)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (siteInfo : site.1 = some (past, view))
    (ready : view.application.publicView.EventReady event)
    (unmissed : view.application.publicView.missedBindingBy owner = false) :
    ∃ (log : List (LocalSeedEntry graph (app).Command))
      (localPositive : ∃ seed ∈ {seed | ∀ entry ∈ log,
        controller.reply seed entry.query = entry.reply}, seed ∈ (laws false).support)
      (residual : PMF ((app).ProtocolState ×
        ((side : {side : Bool // side ≠ false}) → A side))),
      (∀ current, some current ∈
          (((model).bayesBelief profile owner site
            ((menu).decisionInformationAntichain (inputs.map State.initial)
              horizon (mixture).scheduler owner site) positive).map
                (fun history => history.1.state)).support →
        ∀ values ∈ ((mixture).posterior current.execution.environmentRecall).support,
          (controller.replay remainder (initialMemory (values false) (values true))
            current.execution.environmentRecall).log = log) ∧
      ((((model).bayesBelief profile owner site
        ((menu).decisionInformationAntichain (inputs.map State.initial)
          horizon (mixture).scheduler owner site) positive).map
            (fun history => history.1.state)).bind fun state =>
              (draws state).map fun values : (side : Bool) → A side => (values false,
                (state, fun side : {side : Bool // side ≠ false} => values side))) =
        ((laws false).filter {seed | ∀ entry ∈ log,
          controller.reply seed entry.query = entry.reply} localPositive).bind fun localSeed =>
            residual.map (Prod.mk localSeed) := by
  classical
  have horizonPositive := (menu).informationSite_horizon_pos
    (inputs.map State.initial) horizon (mixture).scheduler owner site
  let : NeZero horizon := ⟨ne_of_gt horizonPositive⟩
  let counts := (PMF.uniformOfFintype (Fin horizon)).map Fin.val
  let source := controller.sampledRoundDecisionLaw remainder laws inputs (players profile) counts
  let sourceObserve := fun point : Nat × graph.Inputs × (app).Command × (app).Execution =>
    decisionObservation (owner := owner) (runtime := runtime) (leaks := leaks) point.2
  let sourcePosterior := fiberPosterior source sourceObserve site.1
  let bayesStates : PMF (app).ProtocolState :=
    ((model).bayesBelief profile owner site
      ((menu).decisionInformationAntichain (inputs.map State.initial)
        horizon (mixture).scheduler owner site) positive).map (fun history => history.1.state)
  have sampledEq := controller.sampledRoundDecisionLaw_control remainder laws inputs
    (players profile) horizon
  have observationEq : source.map sourceObserve =
      ((app).occupationControlLaw (mixture).scheduler (players profile)
        (inputs.map State.initial) horizon).map ((app).observe owner) := by
    rw [← sampledEq, PMF.map_comp]
    rfl
  have present : site.1 ∈ (source.map sourceObserve).support := by
    rw [observationEq]
    exact controller.occupation_observation_support remainder laws bounds inputs horizon
      profile site positive
  obtain ⟨witness, witnessSupport, observed⟩ := (PMF.mem_support_map_iff _ _ _).mp present
  obtain ⟨acting, information⟩ := decisionObservation_fields owner witness.2 past view
    (observed.trans siteInfo)
  have viewEq := congrArg Prod.snd information
  change witness.2.2.2.observe app owner = view at viewEq
  have publicEq := congrArg
    (fun current : (app).PlayerView => current.application.publicView) viewEq
  change witness.2.2.2.application.publicView = view.application.publicView at publicEq
  have witnessReady : witness.2.2.2.application.publicView.EventReady event := by
    rwa [publicEq]
  have witnessClear : witness.2.2.2.application.publicView.missedBindingBy owner = false := by
    rwa [publicEq]
  have covered : ∀ who previous current response,
      response ∈ ((players profile) who previous current).support →
        response ∈ (menu).actions who previous current := by
    intro who previous current response supported
    exact (menu).decode_embedPolicy_covered (inputs.map State.initial) horizon
      (mixture).scheduler who (profile who) previous current response supported
  obtain ⟨log, localPositive, sourceResidual, recovered, product⟩ :=
    controller.ownerObservation_seed_product remainder laws bounds inputs ordered domainEq
      (players profile) covered owned counts witness witnessSupport acting witnessReady witnessClear
  change decisionObservation (owner := owner) witness.2 = site.1 at observed
  rw [observed] at recovered product
  have sourceState : sourcePosterior.map
      (decisionControl (runtime := runtime) (leaks := leaks) horizon) = bayesStates := by
    have transported := map_fiberPosterior_readout source
      (decisionControl (runtime := runtime) (leaks := leaks) horizon) ((app).observe owner)
        site.1 present
    have bayes := (menu).bayesBelief_state_eq_occupationPosterior
      (inputs.map State.initial) horizon (mixture).scheduler profile owner site
        ((menu).decisionInformationAntichain
          (inputs.map State.initial) horizon (mixture).scheduler owner site) positive
    change sourcePosterior.map
      (decisionControl (runtime := runtime) (leaks := leaks) horizon) = _ at transported
    rw [sampledEq] at transported
    exact transported.trans bayes.symm
  let residual := sourceResidual.map fun result =>
    (decisionControl (runtime := runtime) (leaks := leaks) horizon result.1, result.2)
  refine ⟨log, localPositive, residual, ?_, ?_⟩
  · intro current supported values valueSupport
    change some current ∈ bayesStates.support at supported
    rw [← sourceState] at supported
    obtain ⟨point, pointSupport, pointEq⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    change some (⟨horizon - point.1 - 1, point.2.2.1.actor? app,
      point.2.2.2⟩ : (app).Control) = some current at pointEq
    have executionEq := congrArg ReactiveApplication.Control.execution (Option.some.inj pointEq)
    rw [← executionEq] at valueSupport ⊢
    exact recovered point pointSupport values valueSupport
  · have transported := controller.bayesBelief_seededDecision remainder laws bounds inputs
      horizon profile site positive
    have compared := congrArg (PMF.map fun result :
        (app).ProtocolState × ((side : Bool) → A side) =>
      (result.2 false, (result.1, fun side : {side : Bool // side ≠ false} => result.2 side)))
        transported
    have projected := congrArg (PMF.map fun result :
        A false × ((Nat × graph.Inputs × (app).Command × (app).Execution) ×
          ((side : {side : Bool // side ≠ false}) → A side)) =>
      (result.1, (decisionControl (runtime := runtime) (leaks := leaks) horizon result.2.1,
        result.2.2))) product
    simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at compared projected
    have combined := compared.symm.trans projected
    simp only [residual, PMF.map_comp, Function.comp_def]
    convert combined using 1

end Vegas.EventGraphRuntime.LocalSeedController
