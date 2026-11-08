/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.LastOwnedPhase
import Vegas.Game.SourceServiceChanceContinuation

/-! # A visible chance event, served last

At a boundary where a chance event is ready alone and its output is visible to
the deviator, the reference clients are silent until it completes, and the
sampled value is read from the deviator's own view. The order-free key of the
drained configuration is a function of the key before the event and that
value, so the deviator's final traffic is again noise read from its normalized
view. The last-served erased-key law of every normalized deviation is
invariant under the phase seed by seed: chance is drawn by the graph law.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Graph

variable {graph : Vegas.EventGraph Player L}

/-- The key after a chance event outputs a value and automatic completion
drains; the key itself when no configuration of the key has the event ready. -/
def chanceAdvance (event : graph.EventId) (ownerless : (graph.nodes event).actor = none)
    (key : RunKey graph) : Option (graph.outputLayout event).Value → RunKey graph
  | none => key
  | some value =>
      open scoped Classical in
      if found : ∃ config : graph.Config, runKey config = key ∧ config.cut.Ready event then
        runKey (State.drainConfig (found.choose.complete event found.choose_spec.2
          (EventCode.actionOfActorNone (graph.nodes event) ownerless) value))
      else key

theorem chanceAdvance_runKey (event : graph.EventId) (ownerless : (graph.nodes event).actor = none)
    (config : graph.Config) (ready : config.cut.Ready event)
    (value : (graph.outputLayout event).Value) :
    chanceAdvance event ownerless (runKey config) (some value) =
      runKey (State.drainConfig (config.complete event ready
        (EventCode.actionOfActorNone (graph.nodes event) ownerless) value)) := by
  have found : ∃ other : graph.Config, runKey other = runKey config ∧ other.cut.Ready event :=
    ⟨config, rfl, ready⟩
  dsimp only [chanceAdvance]
  rw [dite_eq_left found]
  exact State.drain_runKey_congr (runKey_complete_congr found.choose_spec.1 event
    found.choose_spec.2 ready _ value)

theorem chanceAdvance_of_not_ready (event : graph.EventId)
    (ownerless : (graph.nodes event).actor = none) (key : RunKey graph)
    (blocked : ∀ config : graph.Config, runKey config = key → ¬ config.cut.Ready event)
    (choice : Option (graph.outputLayout event).Value) :
    chanceAdvance event ownerless key choice = key := by
  cases choice with
  | none => rfl
  | some value =>
      dsimp only [chanceAdvance]
      rw [dite_eq_right]
      rintro ⟨config, keyEq, ready⟩
      exact blocked config keyEq ready

/-- Completing an event and draining keeps its output, completes it, and is a
graph path from the completion. -/
theorem complete_drain (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    Relation.ReflTransGen Config.Step (config.complete event ready action value)
        (State.drainConfig (config.complete event ready action value)) ∧
      event ∈ (State.drainConfig (config.complete event ready action value)).cut.completed ∧
      (State.drainConfig (config.complete event ready action value)).store (.inr event) =
        some value := by
  have drained := (State.ofConfig (config.complete event ready action value)).drain_graph_steps
  refine ⟨drained, ?_, ?_⟩
  · apply Config.Step.path_completed_mono drained
    change event ∈ (config.cut.complete event ready).completed
    rw [EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  · apply Config.Step.path_store_of_some drained (.inr event) value
    change (config.complete event ready action value).outputs event = some value
    simp [Config.complete]

end Graph

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **A visible chance event.** From a coupled prior whose deviator traffic is
noise read from its normalized view of the order-free key, the phase that
completes a chance event ready alone, whose output the deviator sees, has a
successor key and final traffic of the same factored form, and leaves the
last-served erased-key law of every normalized deviation unchanged. -/
theorem lastChance_phase
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler) (horizon : Nat)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode)
    (reference base : (serviceGraph setup mode).BehavioralProfile) (who : Player)
    (deviation : (serviceApplication setup mode duration leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (event : (serviceGraph setup mode).EventId)
    (ownerless : (serviceGraph setup mode).actor? event = none)
    (visible : (serviceGraph setup mode).fieldVisibleTo who (.inr event))
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    {Seed : Type} (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode duration leaks).Execution)
    (quiescent : ∀ seed ∈ prior.support, ∀ query,
      ¬ (execution seed).application.AutomaticReady query)
    (ordered : ∀ seed ∈ prior.support,
      (execution seed).application.config.cut.IsPrefix event.val)
    (completes : ∀ seed ∈ prior.support, ∀ final ∈
      ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
        (Function.update
          (serviceReferenceTurnPolicy setup mode duration leaks bound turns timing reference) who
          deviation)
        (fun current => event ∈ current.application.config.cut.completed) horizon
        (execution seed)).support,
      event ∈ final.application.config.cut.completed)
    (noise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _)
    (factor : prior.map (fun seed => (runKey (execution seed).application.config,
        (bindingTraffic (serviceTimeouts setup mode duration)) leaks who (execution seed))) =
      (prior.map fun seed => runKey (execution seed).application.config).bind fun current =>
        (noise (keyView who current)).map fun extra => (current, extra)) :
    ∃ nextNoise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _,
      (prior.bind fun seed =>
        ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
          (Function.update
            (serviceReferenceTurnPolicy setup mode duration leaks bound turns timing reference)
            who deviation)
          (fun current => event ∈ current.application.config.cut.completed) horizon
          (execution seed)).map fun final => (runKey final.application.config,
            (bindingTraffic (serviceTimeouts setup mode duration)) leaks who final)) =
        (prior.bind fun seed =>
          ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
            (Function.update
              (serviceReferenceTurnPolicy setup mode duration leaks bound turns timing reference)
              who deviation)
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).map fun final => runKey final.application.config).bind
          (fun current => (nextNoise (keyView who current)).map fun extra => (current, extra)) ∧
      ∀ policy, (prior.bind fun seed =>
        ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
          (Function.update
            (serviceReferenceTurnPolicy setup mode duration leaks bound turns timing reference)
            who deviation)
          (fun current => event ∈ current.application.config.cut.completed) horizon
          (execution seed)).bind fun final =>
            keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy) who
              (runKey final.application.config)) =
        prior.bind fun seed =>
          keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy) who
            (runKey (execution seed).application.config) := by
  classical
  let G := serviceGraph setup mode
  let app := serviceApplication setup mode duration leaks
  let timeouts := serviceTimeouts setup mode duration
  let players := Function.update
    (serviceReferenceTurnPolicy setup mode duration leaks bound turns timing reference) who
    deviation
  let phase := fun seed => app.runUntilHorizon scheduler players
    (fun current => event ∈ current.application.config.cut.completed) horizon (execution seed)
  let key := fun seed => runKey (execution seed).application.config
  let traffic := (bindingTraffic timeouts) leaks who
  have ownerlessNode : (G.nodes event).actor = none := ownerless
  let unit := EventCode.actionOfActorNone (G.nodes event) ownerlessNode
  let pick := fun extra : MessageNetwork Player app.Payload ×
      List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
      PlayerView G × PublicView G =>
    extra.2.2.2.2.1.observation.store (.inr event)
  let normal := fun config : G.Config => G.normalizeObservation who (G.playerObserve who config)
  have readyAt (seed : Seed) (supported : seed ∈ prior.support) :
      (execution seed).application.config.cut.Ready event := by
    simpa only [Fin.eta] using (ordered seed supported).ready event.isLt
  have focalEq (seed : Seed) (supported : seed ∈ prior.support) :
      phase seed = app.runUntilHorizon scheduler (focalPlayers setup leaks who deviation)
        (fun current => event ∈ current.application.config.cut.completed) horizon
        (execution seed) :=
    runUntil_reference_focal scheduler bound turns timing reference who deviation event
      (Or.inl ownerless) alone _ (execution seed) (fun _ => readyAt seed supported)
  have seen (config : G.Config) :
      (normal config).store (.inr event) = config.store (.inr event) :=
    G.playerStore_of_visible who config.store (.inr event) visible
  have advanced (seed : Seed) (supported : seed ∈ prior.support)
      (final : app.Execution) (reached : final ∈ (phase seed).support) :
      runKey final.application.config = chanceAdvance event ownerlessNode (key seed)
        (pick (traffic final)) := by
    have ready := readyAt seed supported
    obtain ⟨action, native, primary, drained⟩ := runUntil_completed_primary_drain timeouts leaks
      scheduler players event (horizon - (execution seed).environmentRecall.length)
      (execution seed) final ready
      (fun other otherReady => alone _ other ready otherReady) (quiescent seed supported)
      reached (completes seed supported final reached)
    have chosen : action = unit := (G.nodes event).action_eq_of_actor_none ownerlessNode _ _
    subst chosen
    unfold Config.step at primary
    rw [PMF.support_map] at primary
    obtain ⟨value, _, nativeEq⟩ := primary
    obtain ⟨_, _, stored⟩ := complete_drain (execution seed).application.config event ready unit
      value
    have picked : pick (traffic final) = some value := by
      change G.playerStore who final.application.config.store (.inr event) = some value
      rw [G.playerStore_of_visible who _ (.inr event) visible, drained]
      rw [nativeEq] at stored
      have same := State.drain_runKey_eq native
      have stores : native.drain.config.store = (State.drainConfig native.config).store :=
        congrArg (fun key => key.2.1) same
      rw [stores]
      exact stored
    rw [picked, chanceAdvance_runKey event ownerlessNode _ ready value, drained,
      State.drain_runKey_eq native, nativeEq]
  have keyed (current : RunKey G) (member : current ∈ (prior.map key).support) :
      ∃ seed ∈ prior.support, key seed = current := by
    obtain ⟨seed, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact ⟨seed, supported, same⟩
  have viewKey (seed : Seed) :
      keyView who (key seed) = some (normal (execution seed).application.config) :=
    keyView_runKey who _
  have completedOf (config : G.Config) :
      event ∈ (normal config).completionOrder ↔ event ∈ config.cut.completed :=
    mem_normalize_completionOrder who config event
  have classify (seed : Seed) (supported : seed ∈ prior.support)
      (choice : Option (G.outputLayout event).Value) :
      ∃ next : G.Config,
        keyView who (chanceAdvance event ownerlessNode (key seed) choice) = some (normal next) ∧
        ((∃ value, choice = some value ∧
            Relation.ReflTransGen Config.Step ((execution seed).application.config.complete
              event (readyAt seed supported) unit value) next ∧
            event ∈ next.cut.completed ∧ next.store (.inr event) = some value) ∨
          (next = (execution seed).application.config ∧ choice = none)) := by
    cases choice with
    | none =>
        exact ⟨(execution seed).application.config, viewKey seed, Or.inr ⟨rfl, rfl⟩⟩
    | some value =>
        obtain ⟨path, completed, stored⟩ := complete_drain (execution seed).application.config
          event (readyAt seed supported) unit value
        refine ⟨_, ?_, Or.inl ⟨value, rfl, path, completed, stored⟩⟩
        change keyView who (chanceAdvance event ownerlessNode
          (runKey (execution seed).application.config) (some value)) = _
        rw [chanceAdvance_runKey event ownerlessNode _ (readyAt seed supported) value]
        exact keyView_runKey who _
  have paired (left : Seed) (leftSupport : left ∈ prior.support) (right : Seed)
      (rightSupport : right ∈ prior.support)
      (leftChoice rightChoice : Option (G.outputLayout event).Value)
      (same : keyView who (chanceAdvance event ownerlessNode (key left) leftChoice) =
        keyView who (chanceAdvance event ownerlessNode (key right) rightChoice)) :
      normal (execution left).application.config =
          normal (execution right).application.config ∧ leftChoice = rightChoice := by
    obtain ⟨leftNext, leftView, leftClass⟩ := classify left leftSupport leftChoice
    obtain ⟨rightNext, rightView, rightClass⟩ := classify right rightSupport rightChoice
    rw [leftView, rightView] at same
    have nexts : normal leftNext = normal rightNext := Option.some.inj same
    have order : event ∈ leftNext.cut.completed ↔ event ∈ rightNext.cut.completed := by
      rw [← completedOf, ← completedOf, nexts]
    have stores : leftNext.store (.inr event) = rightNext.store (.inr event) := by
      rw [← seen, ← seen, nexts]
    have leftPending := (readyAt left leftSupport).1
    have rightPending := (readyAt right rightSupport).1
    rcases leftClass with ⟨first, rfl, leftPath, leftDone, leftStored⟩ | ⟨rfl, rfl⟩ <;>
    rcases rightClass with ⟨second, rfl, rightPath, rightDone, rightStored⟩ | ⟨rfl, rfl⟩
    · refine ⟨normalizeObservation_playerObserve_of_complete_paths who
        (ordered left leftSupport) (ordered right rightSupport) event (readyAt left leftSupport)
        (readyAt right rightSupport) le_rfl unit unit first second leftPath rightPath nexts, ?_⟩
      rw [leftStored, rightStored] at stores
      rw [stores]
    · exact (rightPending (order.mp leftDone)).elim
    · exact (leftPending (order.mpr rightDone)).elim
    · exact ⟨nexts, rfl⟩
  obtain ⟨channel, nextNoise, joint, advancedLaw⟩ := exists_owned_phase_joint prior key
    (fun seed => traffic (execution seed)) (keyView who) noise factor
    (fun seed => (phase seed).map traffic)
    (fun left leftSupport right rightSupport same => by
      rw [focalEq left leftSupport, focalEq right rightSupport]
      have recalled : (execution left).environmentRecall = (execution right).environmentRecall :=
        congrArg (fun value => value.2.2.1) same
      unfold ReactiveApplication.runUntilHorizon
      rw [recalled]
      exact focalPhase_traffic_congr scheduler who deviation (Or.inl ownerless) alone _
        (execution left) (execution right) (fun _ => readyAt left leftSupport)
        (fun _ => readyAt right rightSupport) same)
    pick (chanceAdvance event ownerlessNode) (keyView who) (fun _ => True)
    (fun left leftMember right rightMember leftChoice rightChoice same => by
      obtain ⟨leftSeed, leftSupport, rfl⟩ := keyed left leftMember
      obtain ⟨rightSeed, rightSupport, rfl⟩ := keyed right rightMember
      rw [viewKey, viewKey]
      exact congrArg some
        (paired leftSeed leftSupport rightSeed rightSupport leftChoice rightChoice same).1)
    (fun left leftMember right rightMember leftChoice rightChoice _ same => by
      obtain ⟨leftSeed, leftSupport, rfl⟩ := keyed left leftMember
      obtain ⟨rightSeed, rightSupport, rfl⟩ := keyed right rightMember
      exact (paired leftSeed leftSupport rightSeed rightSupport leftChoice rightChoice same).2)
    (fun _ idle => (idle trivial).elim)
  have pairs : (prior.bind fun seed => (phase seed).map fun final =>
      (runKey final.application.config, traffic final)) =
      prior.bind fun seed => ((phase seed).map traffic).map fun extra =>
        (chanceAdvance event ownerlessNode (key seed) (pick extra), extra) := by
    apply bind_congr_on_support _
    intro seed supported
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro final reached
    simp only [Function.comp_apply, advanced seed supported final reached]
  have marginal : (prior.bind fun seed => (phase seed).map fun final =>
      runKey final.application.config) =
      (prior.map key).bind fun current =>
        (channel (keyView who current)).map fun extra =>
          chanceAdvance event ownerlessNode current (pick extra) := by
    have projected := congrArg (PMF.map Prod.fst) (pairs.trans advancedLaw)
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const,
      PMF.bind_pure] at projected
    exact projected
  refine ⟨nextNoise, ?_, ?_⟩
  · change (prior.bind fun seed => (phase seed).map fun final =>
      (runKey final.application.config, traffic final)) =
      (prior.bind fun seed => (phase seed).map fun final =>
        runKey final.application.config).bind _
    rw [pairs, advancedLaw, marginal]
  · intro policy
    let P := G.lastDeviationProfile base who policy
    have independentP : LastIndependent P who := independent policy
    let continuation := fun config : G.Config => keyTarget P who (runKey config)
    have drained (state : EventGraphRuntime.State G) :
        continuation state.drain.config = continuation state.config := by
      simp only [continuation, keyTarget_runKey independentP]
      exact State.drain_lastErasedLaw independentP state
    have headStep (config : G.Config) (ready : config.cut.Ready event)
        (action : G.Action event) :
        (config.step event ready action).bind continuation = continuation config := by
      simp only [continuation, keyTarget_runKey independentP]
      have stepped := lastRun_step P who config (fun terminal => ready.1 (by
          rw [terminal]; exact Finset.mem_univ _)) event ready
        (lastPick_eq_of_alone who config (fun other otherReady => alone _ other ready otherReady)
          _)
      have mapped := congrArg (PMF.map erasedKey) stepped
      rw [PMF.map_bind] at mapped
      change lastErasedLaw P who config = _ at mapped
      rw [mapped]
      unfold eventStep
      rw [actionLaw_of_ownerless _ _ ownerlessNode, PMF.pure_bind,
        (G.nodes event).action_eq_of_actor_none ownerlessNode action
          (EventCode.actionOfActorNone (G.nodes event) ownerlessNode)]
      rfl
    apply bind_congr_on_support _
    intro seed supported
    exact chance_runUntil_bind_continuation timeouts leaks continuation drained scheduler players
      event (fun _ _ otherReady ready => alone _ _ ready otherReady) headStep ownerless _
      (execution seed) (readyAt seed supported)

end Vegas
