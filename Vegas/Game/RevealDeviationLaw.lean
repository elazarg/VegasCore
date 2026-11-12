module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealDeviationSimulation
public import Vegas.Pending.EventInitialObservation

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
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

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
    (left right : (serviceGraph setup mode).Inputs)
    (views : keyView who (runKey (Config.initial left)) =
      keyView who (runKey (Config.initial right))) :
    (bindingTraffic (serviceTimeouts setup mode duration)) leaks who
        (ReactiveApplication.Execution.initial (serviceApplication setup mode duration leaks)
          (EventGraphRuntime.State.initial left)) =
      (bindingTraffic (serviceTimeouts setup mode duration)) leaks who
        (ReactiveApplication.Execution.initial (serviceApplication setup mode duration leaks)
          (EventGraphRuntime.State.initial right)) := by
  have observed := initial_playerObserve_eq_of_keyView who left right views
  have publics := EventGraphRuntime.State.initial_publicView_eq_of_observation who left right
    observed
  have candidates := EventGraphRuntime.State.initial_candidates_eq_of_observation who left
    right observed
  have playerViews : (EventGraphRuntime.State.initial left).playerView who =
      (EventGraphRuntime.State.initial right).playerView who := by
    unfold EventGraphRuntime.State.playerView
    congr 1
  unfold EventGraphRuntime.bindingTraffic
  dsimp only [ReactiveApplication.Execution.initial]
  rw [playerViews, publics]

/-- Every initial execution is the first phase boundary. -/
theorem initial_phaseBoundary {horizon : Nat}
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler)
    (players : Player → (serviceApplication setup mode duration leaks).Policy)
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    (supported : state ∈ (serviceInitialLaw setup mode).support) :
    PhaseBoundary scheduler players horizon 0
      (ReactiveApplication.Execution.initial (serviceApplication setup mode duration leaks)
        state) := by
  obtain ⟨initial, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  refine ⟨?_, Nat.zero_le _, fun event smaller => absurd smaller (Nat.not_lt_zero _),
    fun event _ done => ?_, fun who entry member => ?_, fun completion member => ?_⟩
  · change ReactiveApplication.Execution.initial _ _ ∈
      ((serviceInitialLaw setup mode).bind fun state =>
        (serviceApplication setup mode duration leaks).runRounds scheduler players 0
          (ReactiveApplication.Execution.initial _ state)).support
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨_, supported, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  · change event ∈ (EventGraph.Config.initial (setup.eventInputs initial) :
      (serviceGraph setup mode).Config).cut.completed at done
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
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup mode duration) delay bound)
    (base : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        (serviceGraph setup mode).normalizeProfile base owner event actor
          ((serviceGraph setup mode).playerObserve owner config) active =
          PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (referenceIndependent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (who : Player) (deviation : (serviceApplication setup mode duration leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (relaxed : RelaxedOrder (serviceGraph setup mode))
    (runs : FlatRevealRuns (serviceGraph setup mode))
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent) :
    ∃ policy : (serviceGraph setup mode).BehavioralPolicy who,
      (serviceInitialLaw setup mode).bind (fun state =>
        ((serviceApplication setup mode duration leaks).runToHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
            (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
            who deviation) horizon
          (ReactiveApplication.Execution.initial (serviceApplication setup mode duration leaks)
            state)).map fun final => readErased (runKey final.application.config)) =
      (serviceInitialLaw setup mode).bind fun state =>
        lastErasedLaw ((serviceGraph setup mode).lastDeviationProfile base who policy) who
          state.config := by
  classical
  let app := serviceApplication setup mode duration leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound
    turns (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
    who deviation
  let traffic := (bindingTraffic (serviceTimeouts setup mode duration)) leaks who
  let start := fun state : EventGraphRuntime.State (serviceGraph setup mode) =>
    ReactiveApplication.Execution.initial app state
  let noise := fun view : Option ((serviceGraph setup mode).PlayerObservation who) =>
    if present : ∃ state ∈ (serviceInitialLaw setup mode).support,
        keyView who (runKey (start state).application.config) = view then
      PMF.pure (traffic (start present.choose))
    else PMF.pure (traffic (start (serviceInitialLaw setup mode).support_nonempty.choose))
  have trafficOf : ∀ first ∈ (serviceInitialLaw setup mode).support,
      ∀ second ∈ (serviceInitialLaw setup mode).support,
      keyView who (runKey (start first).application.config) =
        keyView who (runKey (start second).application.config) →
      traffic (start first) = traffic (start second) := by
    intro first firstMember second secondMember same
    obtain ⟨firstInitial, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp firstMember
    obtain ⟨secondInitial, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp secondMember
    exact initial_bindingTraffic_eq_of_keyView (duration := duration) (leaks := leaks) who _ _
      same
  have factor : (serviceInitialLaw setup mode).map (fun state =>
      (runKey (start state).application.config, traffic (start state))) =
      ((serviceInitialLaw setup mode).map fun state => runKey (start state).application.config).bind
        fun current => (noise (keyView who current)).map fun extra => (current, extra) := by
    rw [PMF.bind_map]
    change (serviceInitialLaw setup mode).bind (fun state => PMF.pure
      (runKey (start state).application.config, traffic (start state))) = _
    apply bind_congr_on_support _
    intro state supported
    have present : ∃ other ∈ (serviceInitialLaw setup mode).support,
        keyView who (runKey (start other).application.config) =
          keyView who (runKey (start state).application.config) :=
      ⟨state, supported, rfl⟩
    simp only [noise, Function.comp_apply, dite_eq_left present, PMF.pure_map]
    obtain ⟨member, same⟩ := present.choose_spec
    rw [trafficOf state supported present.choose member same.symm]
  obtain ⟨policy, law⟩ := concurrentDeviationSimulation bound turns contract timely base decides
    referenceIndependent who deviation independent relaxed runs concurrent 0 (Nat.zero_le _)
    (serviceInitialLaw setup mode) start
    (fun state supported => initial_phaseBoundary scheduler players state supported) noise
    factor
  refine ⟨policy, law.trans (bind_congr_on_support _ fun state _ => ?_)⟩
  exact keyTarget_runKey (independent policy) _

end Vegas
