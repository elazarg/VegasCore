module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealDeviationSimulation

@[expose] public section

/-! # The ledger law of a deviation with concurrent reveals

The deviator's initial traffic is read from its normalized view of the initial
configuration, and every initial execution is the first phase boundary. So the
ledger law of the erased key reached by a deviation from honest
effective-opening clients is the last-served erased-key law of a normalized
graph deviation of the base from the initial configuration.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- Initial configurations with equal normalized views of a player give it equal
graph observations. -/
theorem initial_playerObserve_eq_of_keyView {graph : Vegas.EventGraph Player L} (who : Player)
    (left right : graph.Inputs)
    (views : keyView who (runKey (Config.initial left)) =
      keyView who (runKey (Config.initial right))) :
    graph.playerObserve who (Config.initial left) =
      graph.playerObserve who (Config.initial right) := by
  rw [keyView_runKey, keyView_runKey] at views
  have stores := congrArg (fun observation : graph.PlayerObservation who => observation.store)
    (Option.some.inj views)
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at stores
  simp only at stores
  unfold EventGraph.playerObserve
  rw [stores]
  rfl

/-- The deviator's initial traffic is read from its normalized view of the
initial configuration. -/
theorem initial_bindingTraffic_eq_of_keyView (who : Player)
    (left right : (serviceGraph setup deps).Inputs)
    (views : keyView who (runKey (Config.initial left)) =
      keyView who (runKey (Config.initial right))) :
    (bindingTraffic (serviceTimeouts setup deps duration)) leaks who
        (ReactiveApplication.Execution.initial (serviceApplication setup deps duration leaks)
          (EventGraphRuntime.State.initial left)) =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks who
        (ReactiveApplication.Execution.initial (serviceApplication setup deps duration leaks)
          (EventGraphRuntime.State.initial right)) := by
  exact initial_bindingTraffic_eq_of_observation (serviceTimeouts setup deps duration)
    leaks who left right (initial_playerObserve_eq_of_keyView who left right views)

/-- Every initial execution is the first phase boundary. -/
theorem initial_phaseBoundary {horizon : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (state : EventGraphRuntime.State (serviceGraph setup deps))
    (supported : state ∈ (serviceInitialLaw setup deps).support) :
    PhaseBoundary scheduler players horizon 0
      (ReactiveApplication.Execution.initial (serviceApplication setup deps duration leaks)
        state) := by
  obtain ⟨initial, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  refine ⟨?_, Nat.zero_le _, fun event smaller => absurd smaller (Nat.not_lt_zero _),
    fun event _ done => ?_, fun who entry member => ?_, fun completion member => ?_⟩
  · change ReactiveApplication.Execution.initial _ _ ∈
      ((serviceInitialLaw setup deps).bind fun state =>
        (serviceApplication setup deps duration leaks).runRounds scheduler players 0
          (ReactiveApplication.Execution.initial _ state)).support
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨_, supported, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  · change event ∈ (EventGraph.Config.initial (setup.eventInputs initial) :
      (serviceGraph setup deps).Config).cut.completed at done
    simp [EventGraph.Config.initial, EventOrder.Cut.empty] at done
  · change entry ∈ ([] : List _) at member
    cases member
  · change completion ∈ ([] : List _) at member
    cases member

/-- **The ledger law of a deviation.** Against honest effective-opening clients,
the ledger law of the erased key a deviation of one player reaches by the horizon
is the last-served erased-key law of a normalized graph deviation of the base
from the initial configuration. -/
theorem concurrent_deviation_erased_law {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay : (serviceGraph setup deps).EventId → Nat}
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (base : (serviceGraph setup deps).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup deps).Config)
      (event : (serviceGraph setup deps).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup deps).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup deps).layout payload))
      (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
        ((serviceGraph setup deps).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup deps) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup deps).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup deps).playerObserve owner config).defaulted),
        (serviceGraph setup deps).normalizeProfile base owner event actor
          ((serviceGraph setup deps).playerObserve owner config) active =
          PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (referenceIndependent : ReadyIndependent ((serviceGraph setup deps).normalizeProfile base))
    (who : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup deps).lastDeviationProfile base who policy) who)
    (relaxed : RelaxedOrder (serviceGraph setup deps))
    (runs : FlatRevealRuns (serviceGraph setup deps))
    (concurrent : (serviceGraph setup deps).RevealsOnlyConcurrent) :
    ∃ policy : (serviceGraph setup deps).BehavioralPolicy who,
      (serviceInitialLaw setup deps).bind (fun state =>
        ((serviceApplication setup deps duration leaks).runToHorizon scheduler
          (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
            (firstTurnTiming setup turns deps) ((serviceGraph setup deps).normalizeProfile base))
            who deviation) horizon
          (ReactiveApplication.Execution.initial (serviceApplication setup deps duration leaks)
            state)).map fun final => readErased (runKey final.application.config)) =
      (serviceInitialLaw setup deps).bind fun state =>
        lastErasedLaw ((serviceGraph setup deps).lastDeviationProfile base who policy) who
          state.config := by
  classical
  let app := serviceApplication setup deps duration leaks
  let players := Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound
    turns (firstTurnTiming setup turns deps) ((serviceGraph setup deps).normalizeProfile base))
    who deviation
  let traffic := (bindingTraffic (serviceTimeouts setup deps duration)) leaks who
  let start := fun state : EventGraphRuntime.State (serviceGraph setup deps) =>
    ReactiveApplication.Execution.initial app state
  obtain ⟨noise, initialFactor⟩ := initial_bindingTraffic_factorization_of_view
    (serviceTimeouts setup deps duration) leaks who setup.initialLaw setup.eventInputs
    (fun initial => runKey (Config.initial (graph := serviceGraph setup deps)
      (setup.eventInputs initial))) (keyView who)
    (fun left _ right _ same =>
      initial_playerObserve_eq_of_keyView (graph := serviceGraph setup deps) who
        (setup.eventInputs left) (setup.eventInputs right)
        same)
  have factor : (serviceInitialLaw setup deps).map (fun state =>
      (runKey (start state).application.config, traffic (start state))) =
      ((serviceInitialLaw setup deps).map fun state => runKey (start state).application.config).bind
        fun current => (noise (keyView who current)).map fun extra => (current, extra) := by
    simp only [serviceInitialLaw, PMF.map_comp, Function.comp_def]
    exact initialFactor
  obtain ⟨policy, law⟩ := concurrentDeviationSimulation bound turns contract timely base decides
    referenceIndependent who deviation independent relaxed runs concurrent 0 (Nat.zero_le _)
    (serviceInitialLaw setup deps) start
    (fun state supported => initial_phaseBoundary scheduler players state supported) noise
    factor
  refine ⟨policy, law.trans (bind_congr_on_support _ fun state _ => ?_)⟩
  exact keyTarget_runKey (independent policy) _

end Vegas
