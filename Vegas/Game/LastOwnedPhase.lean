module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceDeviationChoice
public import Vegas.Game.OwnedPhaseJoint
public import Vegas.EventGraph.LastKeyTarget
public import Vegas.EventGraph.PrefixRestriction
public import Vegas.EventGraph.OwnedStep
public import Vegas.Pending.LastErasedKeyLaw
public import Vegas.Pending.ReactiveGraphSteps

@[expose] public section

/-! # The deviator's sole event, served last

At a boundary where an event of the deviator is ready alone, the reference
clients of the other players are silent until it completes. The deviator's
choice there is read from its own completion record, and the order-free key of
the drained configuration is a function of the key before the event and that
choice. Conditioning the deviator's final traffic on its normalized view gives
a kernel at that event, and a graph policy that plays this kernel there and a
tail policy afterwards has, from the boundary, the last-served erased-key law
of the tail after the phase, on average over every coupled prior.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Until the sole ready event of the deviator or of chance completes, the
reference clients of the other players remain silent. -/
theorem runUntil_reference_focal
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode)
    (reference : (serviceGraph setup mode).BehavioralProfile) (who : Player)
    (deviation : (serviceApplication setup mode duration leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (focal : (serviceGraph setup mode).actor? event = none ∨ (serviceGraph setup mode).actor?
        event = some who)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event → cut.Ready
        other → other = event) (count : Nat)
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (holds : event ∉ execution.application.config.cut.completed →
      execution.application.config.cut.Ready event) :
    (serviceApplication setup mode duration leaks).runUntil scheduler
    (Function.update
      (serviceReferenceTurnPolicy setup mode duration leaks bound turns timing reference) who
        deviation)
    (fun final => event ∈ final.application.config.cut.completed) count execution =
    (serviceApplication setup mode duration leaks).runUntil scheduler
    (focalPlayers setup leaks who deviation)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := serviceApplication setup mode duration leaks
  apply app.runUntil_congr_of_agree scheduler _ _ _
    (fun current => event ∉ current.application.config.cut.completed →
      current.application.config.cut.Ready event)
  · intro current currentHolds running command _ middle moved player active
    by_cases same : player = who
    · subst same
      simp only [focalPlayers, Function.update_self]
    · simp only [focalPlayers, Function.update_of_ne same]
      have activateIs : command = .activate player := by
        cases command with
        | activate actor => cases active; rfl
        | «include» => cases active
        | application => cases active
        | wait => cases active
      subst activateIs
      have sameApp := activation_application setup leaks current middle player moved
      have idle : (middle.observe app player).application.publicView.ownTurn? player = none := by
        change middle.application.publicView.ownTurn? player = none
        rw [sameApp]
        apply ownTurn?_none_of_alone alone _ (currentHolds running) player
        rcases focal with actorless | owned
        · rw [actorless]
          exact fun impossible => by cases impossible
        · rw [owned]
          exact fun equal => same (Option.some.inj equal).symm
      simp only [serviceReferenceTurnPolicy, idle]
  · intro current currentHolds running next reached
    exact round_ready_of_pending alone (currentHolds running) reached
  · exact holds

section Graph

variable {graph : Vegas.EventGraph Player L}

/-- The action a completion record decided at an event, when it is a record
of that event with a decision. -/
def recordAction (event : graph.EventId) (completion : graph.Completion) :
    Option (graph.Action event) :=
  if same : completion.event = event then same ▸ completion.decision else none

omit [DecidableEq Player] in
@[simp] theorem recordAction_completion (event : graph.EventId)
    (decision : Option (graph.Action event)) (value : (graph.outputLayout event).Value) :
    recordAction event (EventGraph.completion graph event decision value) = decision := by
  simp [recordAction, EventGraph.completion]

/-- The action a player decided at an event, read from its own completions. -/
def observedAction {who : Player} (event : graph.EventId)
    (observation : graph.PlayerObservation who) : Option (graph.Action event) :=
  (observation.ownActions.find? fun completion => completion.event = event).bind
    (recordAction event)

/-- A player's recorded own decision is read from its observation. -/
theorem observedAction_playerObserve (who : Player) (config : graph.Config)
    (event : graph.EventId) (owned : graph.actor? event = some who)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (present : EventGraph.completion graph event (some action) value ∈ config.history) :
    observedAction event (graph.playerObserve who config) = some action := by
  let record := EventGraph.completion graph event (some action) value
  have recalled : record ∈ graph.ownCompletions who config.history :=
    (EventGraph.mem_ownCompletions who config.history record).2 ⟨present, owned, rfl⟩
  have found : (graph.ownCompletions who config.history).find?
      (fun completion => decide (completion.event = event)) = some record := by
    cases selected : (graph.ownCompletions who config.history).find?
        (fun completion => decide (completion.event = event)) with
    | none =>
        have absent := List.find?_eq_none.mp selected record recalled
        exact (absent (by simp only [record, EventGraph.completion, decide_true])).elim
    | some completion =>
        have current := List.mem_of_find?_eq_some selected
        have matching : completion.event = event := by
          simpa only [decide_eq_true_eq] using List.find?_some selected
        have retained := ((EventGraph.mem_ownCompletions who config.history completion).1
          current).1
        have equal : completion = record :=
          List.inj_on_of_nodup_map config.history_nodup retained present matching
        exact congrArg some equal
  change ((graph.ownCompletions who config.history).find?
    (fun completion => decide (completion.event = event))).bind (recordAction event) = _
  rw [found]
  simp [record]

/-- The normalized observation keeps a player's decision at each event. -/
theorem observedAction_normalize (who : Player) (config : graph.Config)
    (event : graph.EventId) :
    observedAction event (graph.normalizeObservation who (graph.playerObserve who config)) =
      ((completionOf config event).filter fun completion =>
        graph.actor? completion.event = some who ∧ completion.decision.isSome).bind
          (recordAction event) := by
  rw [normalizeObservation_playerObserve]
  unfold observedAction
  rw [find?_filterMap_tagged _ (completionOf_filter_tagged config _) event]

/-- An event is in the normalized completion order exactly when it is completed. -/
theorem mem_normalize_completionOrder (who : Player) (config : graph.Config)
    (event : graph.EventId) :
    event ∈ (graph.normalizeObservation who (graph.playerObserve who config)).completionOrder ↔
      event ∈ config.cut.completed := by
  rw [normalizeObservation_playerObserve]
  simp only [List.mem_filter, List.mem_finRange, true_and]
  exact completionOf_isSome_iff config event

/-- The configuration an owned event's step reaches with a given action. -/
def ownedStepped {who : Player} (event : graph.EventId) (owned : graph.actor? event = some who)
    (config : graph.Config) (ready : config.cut.Ready event) (action : graph.Action event) :
    graph.Config :=
  (config.step_eq_pure_of_actor event ready action who owned).choose

theorem step_eq_ownedStepped {who : Player} (event : graph.EventId)
    (owned : graph.actor? event = some who) (config : graph.Config)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    config.step event ready action = PMF.pure (ownedStepped event owned config ready action) :=
  (config.step_eq_pure_of_actor event ready action who owned).choose_spec

/-- The key after an owned event takes an action and automatic completion drains;
the key itself when no configuration of the key has the event ready. -/
def ownedAdvance {who : Player} (event : graph.EventId) (owned : graph.actor? event = some who)
    (key : RunKey graph) : Option (graph.Action event) → RunKey graph
  | none => key
  | some action =>
      open scoped Classical in
      if found : ∃ config : graph.Config, runKey config = key ∧ config.cut.Ready event then
        runKey (State.drainConfig
          (ownedStepped event owned found.choose found.choose_spec.2 action))
      else key

theorem ownedAdvance_runKey {who : Player} (event : graph.EventId)
    (owned : graph.actor? event = some who) (config : graph.Config)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    ownedAdvance event owned (runKey config) (some action) =
      runKey (State.drainConfig (ownedStepped event owned config ready action)) := by
  have found : ∃ other : graph.Config, runKey other = runKey config ∧ other.cut.Ready event :=
    ⟨config, rfl, ready⟩
  dsimp only [ownedAdvance]
  rw [dite_eq_left found]
  have keys : runKey (ownedStepped event owned found.choose found.choose_spec.2 action) =
      runKey (ownedStepped event owned config ready action) := by
    have mapped := step_map_runKey_congr found.choose_spec.1 event found.choose_spec.2 ready
      action
    rw [step_eq_ownedStepped event owned found.choose found.choose_spec.2 action,
      step_eq_ownedStepped event owned config ready action, PMF.pure_map, PMF.pure_map]
      at mapped
    have supports := congrArg PMF.support mapped
    rw [PMF.support_pure, PMF.support_pure] at supports
    exact Set.singleton_eq_singleton_iff.mp supports
  exact State.drain_runKey_congr keys

/-- Without a ready configuration of the key, the key does not advance. -/
theorem ownedAdvance_of_not_ready {who : Player} (event : graph.EventId)
    (owned : graph.actor? event = some who) (key : RunKey graph)
    (blocked : ∀ config : graph.Config, runKey config = key → ¬ config.cut.Ready event)
    (choice : Option (graph.Action event)) :
    ownedAdvance event owned key choice = key := by
  cases choice with
  | none => rfl
  | some action =>
      dsimp only [ownedAdvance]
      rw [dite_eq_right]
      rintro ⟨config, keyEq, ready⟩
      exact blocked config keyEq ready

/-- The drained step of an active owner's event is a path from the configuration,
completes the event, and records the owner's action in its normalized view. -/
theorem ownedStepped_drain {who : Player} (event : graph.EventId)
    (owned : graph.actor? event = some who) (config : graph.Config)
    (ready : config.cut.Ready event) (active : who ∉ config.defaulted)
    (action : graph.Action event) :
    Relation.ReflTransGen Config.Step config
        (State.drainConfig (ownedStepped event owned config ready action)) ∧
      event ∈ (State.drainConfig (ownedStepped event owned config ready action)).cut.completed ∧
      observedAction event (graph.normalizeObservation who (graph.playerObserve who
        (State.drainConfig (ownedStepped event owned config ready action)))) = some action := by
  let stepped := ownedStepped event owned config ready action
  have member : stepped ∈ (config.step event ready action).support := by
    rw [step_eq_ownedStepped event owned config ready action, PMF.support_pure]
    rfl
  have drained := (State.ofConfig stepped).drain_graph_steps
  have path : Relation.ReflTransGen Config.Step config (State.drainConfig stepped) :=
    Relation.ReflTransGen.head ⟨event, ready, action, member⟩ drained
  obtain ⟨value, _, history⟩ := config.step_completion event ready action stepped member
  have ownedNode : (graph.nodes event).actor = some who := owned
  rw [config.actualDecision_of_active event who ownedNode active action] at history
  have recorded : completionOf stepped event =
      some (EventGraph.completion graph event (some action) value) := by
    apply (completionOf_eq_some_iff stepped event _).mpr
    refine ⟨?_, rfl⟩
    rw [history]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have kept : completionOf (State.drainConfig stepped) event =
      some (EventGraph.completion graph event (some action) value) :=
    Config.Step.path_completionOf_of_some drained event _ recorded
  refine ⟨path, ?_, ?_⟩
  · exact (completionOf_isSome_iff _ event).mp (by
      change (completionOf (State.drainConfig stepped) event).isSome = true
      rw [kept]
      rfl)
  · rw [observedAction_normalize]
    change ((completionOf (State.drainConfig stepped) event).filter _).bind _ = _
    have keep : (decide (graph.actor? event = some who) && (some action).isSome) = true := by
      simp only [owned, decide_true, Option.isSome_some, Bool.and_self]
    rw [kept]
    simp only [Option.filter_some, EventGraph.completion, keep, ite_true, Option.bind_some,
      Bool.decide_and, Bool.decide_eq_true]
    exact recordAction_completion event (some action) value

/-- **The deviator's head at one event.** It plays the kernel on its
normalized observation there, and the tail elsewhere and where the kernel
declines. -/
def ownedHead {who : Player} (event : graph.EventId)
    (kernel : Option (graph.PlayerObservation who) → PMF (Option (graph.Action event)))
    (tail : graph.BehavioralPolicy who) : graph.BehavioralPolicy who :=
  fun current actor observation active =>
    if same : event = current then
      (same ▸ kernel (some observation) : PMF (Option (graph.Action current))).bind fun choice =>
        choice.elim (tail current actor observation active) PMF.pure
    else tail current actor observation active

theorem ownedHead_self {who : Player} (event : graph.EventId)
    (kernel : Option (graph.PlayerObservation who) → PMF (Option (graph.Action event)))
    (tail : graph.BehavioralPolicy who) (actor : (graph.nodes event).actor = some who)
    (observation : graph.PlayerObservation who) (active : who ∉ observation.defaulted) :
    ownedHead event kernel tail event actor observation active =
      (kernel (some observation)).bind fun choice =>
        choice.elim (tail event actor observation active) PMF.pure := by
  simp [ownedHead]

end Graph

/-- **The deviator's sole event.** From a coupled prior whose deviator
traffic is noise read from its normalized view of the order-free key, the
phase that completes an event of the deviator ready alone has a successor key
and final traffic of the same factored form, and a graph policy built from the
deviator's conditional choice there has, on average, the last-served
erased-key law of its tail after the phase. -/
theorem lastOwned_phase_patched
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler) (horizon : Nat)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode)
    (reference base : (serviceGraph setup mode).BehavioralProfile) (who : Player)
    (deviation : (serviceApplication setup mode duration leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    {Seed : Type} (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode duration leaks).Execution)
    (quiescent : ∀ seed ∈ prior.support, ∀ query,
      ¬ (execution seed).application.AutomaticReady query)
    (pendingPrefix : ∀ seed ∈ prior.support,
      event ∉ (execution seed).application.config.cut.completed →
        (execution seed).application.config.cut.IsPrefix event.val)
    (automaticPast : ∀ seed ∈ prior.support,
      event ∈ (execution seed).application.config.cut.completed →
        observedAction event ((serviceGraph setup mode).normalizeObservation who
          ((serviceGraph setup mode).playerObserve who
            (execution seed).application.config)) = none)
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
    ∃ (build : (serviceGraph setup mode).BehavioralPolicy who →
        (serviceGraph setup mode).BehavioralPolicy who)
      (nextNoise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _),
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
      (∀ policy, (prior.bind fun seed =>
        ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
          (Function.update
            (serviceReferenceTurnPolicy setup mode duration leaks bound turns timing reference)
            who deviation)
          (fun current => event ∈ current.application.config.cut.completed) horizon
          (execution seed)).bind fun final =>
            keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy) who
              (runKey final.application.config)) =
        prior.bind fun seed =>
          keyTarget ((serviceGraph setup mode).lastDeviationProfile base who (build policy)) who
            (runKey (execution seed).application.config)) ∧
      ∀ policy (config : (serviceGraph setup mode).Config) other, other ≠ event →
        actionLaw ((serviceGraph setup mode).lastDeviationProfile base who (build policy)) config
            other =
          actionLaw ((serviceGraph setup mode).lastDeviationProfile base who policy) config
            other := by
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
  let pick := fun extra : MessageNetwork Player app.Payload ×
      List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
      PlayerView G × PublicView G =>
    observedAction event extra.2.2.2.2.1.observation
  have ownedNode : (G.nodes event).actor = some who := owned
  have readyAt (seed : Seed) (supported : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed) :
      (execution seed).application.config.cut.Ready event := by
    have ordered := pendingPrefix seed supported pending
    simpa only [Fin.eta] using ordered.ready event.isLt
  have activeAt (seed : Seed) (supported : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed) :
      who ∉ (execution seed).application.config.defaulted := by
    intro inactive
    apply quiescent seed supported event
    unfold State.AutomaticReady
    rw [owned]
    exact ⟨readyAt seed supported pending, inactive⟩
  have focalEq (seed : Seed) (supported : seed ∈ prior.support) :
      phase seed = app.runUntilHorizon scheduler (focalPlayers setup leaks who deviation)
        (fun current => event ∈ current.application.config.cut.completed) horizon
        (execution seed) :=
    runUntil_reference_focal scheduler bound turns timing reference who deviation event
      (Or.inr owned) alone _ (execution seed) (readyAt seed supported)
  have advanced (seed : Seed) (supported : seed ∈ prior.support)
      (final : app.Execution) (reached : final ∈ (phase seed).support) :
      runKey final.application.config = ownedAdvance event owned (key seed)
        (pick (traffic final)) ∧
      (event ∉ (execution seed).application.config.cut.completed →
        ∃ action, pick (traffic final) = some action) := by
    by_cases pending : event ∉ (execution seed).application.config.cut.completed
    · have ready := readyAt seed supported pending
      obtain ⟨action, native, primary, drained⟩ := runUntil_completed_primary_drain timeouts leaks
        scheduler players event (horizon - (execution seed).environmentRecall.length)
        (execution seed) final ready
        (fun other otherReady => alone _ other ready otherReady) (quiescent seed supported)
        reached (completes seed supported final reached)
      rw [step_eq_ownedStepped event owned _ ready action, PMF.mem_support_pure_iff] at primary
      have member : ownedStepped event owned _ ready action ∈
          ((execution seed).application.config.step event ready action).support := by
        rw [step_eq_ownedStepped event owned _ ready action, PMF.support_pure]
        rfl
      obtain ⟨value, _, history⟩ := (execution seed).application.config.step_completion event
        ready action _ member
      rw [(execution seed).application.config.actualDecision_of_active event who ownedNode
        (activeAt seed supported pending) action] at history
      obtain ⟨extra, extended⟩ := Config.Step.path_history_prefix native.drain_graph_steps
      have present : EventGraph.completion G event (some action) value ∈
          final.application.config.history := by
        rw [drained, ← extended, primary, history]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
      have picked : pick (traffic final) = some action :=
        observedAction_playerObserve who final.application.config event owned action value
          present
      refine ⟨?_, fun _ => ⟨action, picked⟩⟩
      rw [picked, ownedAdvance_runKey event owned _ ready action, drained,
        State.drain_runKey_eq native, primary]
    · push Not at pending
      have stopped : phase seed = PMF.pure (execution seed) :=
        app.runUntil_of_stop scheduler players _ _ _ pending
      rw [stopped, PMF.mem_support_pure_iff] at reached
      subst final
      refine ⟨?_, fun unfinished => (unfinished pending).elim⟩
      symm
      apply ownedAdvance_of_not_ready
      intro config keyEq ready
      have cuts : config.cut = (execution seed).application.config.cut := congrArg Prod.fst keyEq
      exact ready.1 (cuts ▸ pending)
  let normal := fun config : G.Config => G.normalizeObservation who (G.playerObserve who config)
  have keyed (current : RunKey G) (member : current ∈ (prior.map key).support) :
      ∃ seed ∈ prior.support, key seed = current := by
    obtain ⟨seed, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact ⟨seed, supported, same⟩
  have viewKey (seed : Seed) :
      keyView who (key seed) = some (normal (execution seed).application.config) :=
    keyView_runKey who _
  have stay (seed : Seed) (choice : Option (G.Action event))
      (staying : choice = none ∨ event ∈ (execution seed).application.config.cut.completed) :
      ownedAdvance event owned (key seed) choice = key seed := by
    rcases staying with rfl | completed
    · rfl
    · apply ownedAdvance_of_not_ready
      intro config keyEq ready
      have cuts : config.cut = (execution seed).application.config.cut :=
        congrArg Prod.fst keyEq
      exact ready.1 (cuts ▸ completed)
  have classify (seed : Seed) (supported : seed ∈ prior.support)
      (choice : Option (G.Action event)) :
      ∃ next : G.Config,
        keyView who (ownedAdvance event owned (key seed) choice) = some (normal next) ∧
        ((event ∉ (execution seed).application.config.cut.completed ∧
            ∃ action, choice = some action ∧
              Relation.ReflTransGen Config.Step (execution seed).application.config next ∧
              event ∈ next.cut.completed ∧ observedAction event (normal next) = some action) ∨
          (next = (execution seed).application.config ∧
            (event ∉ (execution seed).application.config.cut.completed → choice = none))) := by
    by_cases pending : event ∉ (execution seed).application.config.cut.completed
    · cases choice with
      | none =>
          refine ⟨(execution seed).application.config, ?_, Or.inr ⟨rfl, fun _ => rfl⟩⟩
          rw [stay seed none (Or.inl rfl)]
          exact viewKey seed
      | some action =>
          have ready := readyAt seed supported pending
          obtain ⟨path, completed, observed⟩ := ownedStepped_drain event owned _ ready
            (activeAt seed supported pending) action
          refine ⟨_, ?_, Or.inl ⟨pending, action, rfl, path, completed, observed⟩⟩
          change keyView who (ownedAdvance event owned
            (runKey (execution seed).application.config) (some action)) = _
          rw [ownedAdvance_runKey event owned _ ready action]
          exact keyView_runKey who _
    · push Not at pending
      refine ⟨(execution seed).application.config, ?_,
        Or.inr ⟨rfl, fun unfinished => (unfinished pending).elim⟩⟩
      rw [stay seed choice (Or.inr pending)]
      exact viewKey seed
  have completedOf (config : G.Config) :
      event ∈ (normal config).completionOrder ↔ event ∈ config.cut.completed :=
    mem_normalize_completionOrder who config event
  have paired (left : Seed) (leftSupport : left ∈ prior.support) (right : Seed)
      (rightSupport : right ∈ prior.support) (leftChoice rightChoice : Option (G.Action event))
      (same : keyView who (ownedAdvance event owned (key left) leftChoice) =
        keyView who (ownedAdvance event owned (key right) rightChoice)) :
      normal (execution left).application.config = normal (execution right).application.config ∧
        (event ∉ (execution left).application.config.cut.completed →
          leftChoice = rightChoice) := by
    obtain ⟨leftNext, leftView, leftClass⟩ := classify left leftSupport leftChoice
    obtain ⟨rightNext, rightView, rightClass⟩ := classify right rightSupport rightChoice
    rw [leftView, rightView] at same
    have nexts : normal leftNext = normal rightNext := Option.some.inj same
    have order : event ∈ leftNext.cut.completed ↔ event ∈ rightNext.cut.completed := by
      rw [← completedOf, ← completedOf, nexts]
    have decided : observedAction event (normal leftNext) =
        observedAction event (normal rightNext) := by rw [nexts]
    rcases leftClass with ⟨leftPending, first, rfl, leftPath, leftDone, leftObserved⟩ |
      ⟨rfl, leftNone⟩ <;>
    rcases rightClass with ⟨rightPending, second, rfl, rightPath, rightDone, rightObserved⟩ |
      ⟨rfl, rightNone⟩
    · refine ⟨normalizeObservation_playerObserve_of_paths who
        (pendingPrefix left leftSupport leftPending)
        (pendingPrefix right rightSupport rightPending) leftPath rightPath nexts, fun _ => ?_⟩
      rw [leftObserved, rightObserved] at decided
      exact decided
    · exfalso
      by_cases rightPending : event ∉ (execution right).application.config.cut.completed
      · exact rightPending (order.mp leftDone)
      · push Not at rightPending
        rw [leftObserved, automaticPast right rightSupport rightPending] at decided
        cases decided
    · exfalso
      by_cases leftPending : event ∉ (execution left).application.config.cut.completed
      · exact leftPending (order.mpr rightDone)
      · push Not at leftPending
        rw [rightObserved, automaticPast left leftSupport leftPending] at decided
        cases decided
    · refine ⟨nexts, fun leftPending => ?_⟩
      have rightPending : event ∉ (execution right).application.config.cut.completed :=
        fun done => leftPending (order.mpr done)
      rw [leftNone leftPending, rightNone rightPending]
  obtain ⟨channel, nextNoise, joint, advancedLaw⟩ := exists_owned_phase_joint prior key
    (fun seed => traffic (execution seed)) (keyView who) noise factor
    (fun seed => (phase seed).map traffic)
    (fun left leftSupport right rightSupport same => by
      rw [focalEq left leftSupport, focalEq right rightSupport]
      have recalled : (execution left).environmentRecall = (execution right).environmentRecall :=
        congrArg (fun value => value.2.2.1) same
      unfold ReactiveApplication.runUntilHorizon
      rw [recalled]
      exact focalPhase_traffic_congr scheduler who deviation (Or.inr owned) alone _
        (execution left) (execution right) (readyAt left leftSupport)
        (readyAt right rightSupport) same)
    pick (ownedAdvance event owned) (keyView who)
    (fun view => ∃ observation, view = some observation ∧ event ∉ observation.completionOrder)
    (fun left leftMember right rightMember leftChoice rightChoice same => by
      obtain ⟨leftSeed, leftSupport, rfl⟩ := keyed left leftMember
      obtain ⟨rightSeed, rightSupport, rfl⟩ := keyed right rightMember
      rw [viewKey, viewKey]
      exact congrArg some
        (paired leftSeed leftSupport rightSeed rightSupport leftChoice rightChoice same).1)
    (fun left leftMember right rightMember leftChoice rightChoice live same => by
      obtain ⟨leftSeed, leftSupport, rfl⟩ := keyed left leftMember
      obtain ⟨rightSeed, rightSupport, rfl⟩ := keyed right rightMember
      obtain ⟨observation, observationEq, notDone⟩ := live
      rw [viewKey] at observationEq
      cases observationEq
      exact (paired leftSeed leftSupport rightSeed rightSupport leftChoice rightChoice same).2
        (fun done => notDone ((completedOf _).mpr done)))
    (fun current idle first second => by
      have blocked : ∀ config : G.Config, runKey config = current →
          ¬ config.cut.Ready event := fun config keyEq ready => idle
        ⟨normal config, by rw [← keyEq]; exact keyView_runKey who config,
          fun member => ready.1 ((completedOf config).mp member)⟩
      rw [ownedAdvance_of_not_ready event owned current blocked first,
        ownedAdvance_of_not_ready event owned current blocked second])
  let kernel := fun view => (channel view).map pick
  let build := fun tail : G.BehavioralPolicy who =>
    patchPolicy event (ownedHead event kernel tail) tail
  have pairs : (prior.bind fun seed => (phase seed).map fun final =>
      (runKey final.application.config, traffic final)) =
      prior.bind fun seed => ((phase seed).map traffic).map fun extra =>
        (ownedAdvance event owned (key seed) (pick extra), extra) := by
    apply bind_congr_on_support _
    intro seed supported
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro final reached
    simp only [Function.comp_apply, (advanced seed supported final reached).1]
  have marginal : (prior.bind fun seed => (phase seed).map fun final =>
      runKey final.application.config) =
      (prior.map key).bind fun current =>
        (channel (keyView who current)).map fun extra =>
          ownedAdvance event owned current (pick extra) := by
    have projected := congrArg (PMF.map Prod.fst) (pairs.trans advancedLaw)
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const,
      PMF.bind_pure] at projected
    exact projected
  have supportPick (seed : Seed) (supported : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed)
      (extra : _) (member : extra ∈ (channel (keyView who (key seed))).support) :
      ∃ action, pick extra = some action := by
    have inJoint : (key seed, extra) ∈ ((prior.map key).bind fun current =>
        (channel (keyView who current)).map fun extra => (current, extra)).support := by
      rw [PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨key seed, (PMF.mem_support_map_iff _ _ _).mpr
        ⟨seed, supported, rfl⟩, ?_⟩
      rw [PMF.support_map]
      exact ⟨extra, member, rfl⟩
    rw [← joint, PMF.support_bind] at inJoint
    obtain ⟨other, otherSupport, otherMember⟩ := Set.mem_iUnion₂.mp inJoint
    rw [PMF.support_map] at otherMember
    obtain ⟨found, foundMember, foundEq⟩ := otherMember
    rw [PMF.support_map] at foundMember
    obtain ⟨final, reached, finalEq⟩ := foundMember
    have keys : key other = key seed := congrArg Prod.fst foundEq
    have extras : found = extra := congrArg Prod.snd foundEq
    have otherPending : event ∉ (execution other).application.config.cut.completed := by
      have cuts : (execution other).application.config.cut =
          (execution seed).application.config.cut := congrArg Prod.fst keys
      rw [cuts]
      exact pending
    obtain ⟨action, picked⟩ := (advanced other otherSupport final reached).2 otherPending
    exact ⟨action, by rw [← extras, ← finalEq]; exact picked⟩
  refine ⟨build, nextNoise, ?_, ?_, fun policy config other different =>
    actionLaw_lastDeviationProfile_patch_of_ne base who event _ policy config different⟩
  · change (prior.bind fun seed => (phase seed).map fun final =>
      (runKey final.application.config, traffic final)) =
      (prior.bind fun seed => (phase seed).map fun final =>
        runKey final.application.config).bind _
    rw [pairs, advancedLaw, marginal]
  · intro policy
    let P := fun tail : G.BehavioralPolicy who => G.lastDeviationProfile base who tail
    have agree (config : G.Config) (other : G.EventId) (different : other ≠ event) :
        actionLaw (P (build policy)) config other = actionLaw (P policy) config other :=
      actionLaw_lastDeviationProfile_patch_of_ne base who event _ policy config different
    change (prior.bind fun seed => (phase seed).bind fun final =>
      keyTarget (P policy) who (runKey final.application.config)) =
      prior.bind fun seed => keyTarget (P (build policy)) who (key seed)
    calc
      _ = prior.bind (fun seed => ((phase seed).map traffic).bind fun extra =>
          keyTarget (P policy) who (ownedAdvance event owned (key seed) (pick extra))) := by
        apply bind_congr_on_support _
        intro seed supported
        rw [PMF.bind_map]
        apply bind_congr_on_support _
        intro final reached
        simp only [Function.comp_apply, (advanced seed supported final reached).1]
      _ = (prior.map key).bind (fun current => (channel (keyView who current)).bind
          fun extra =>
            keyTarget (P policy) who (ownedAdvance event owned current (pick extra))) := by
        have regrouped := congrArg (fun law => law.bind fun pair =>
          keyTarget (P policy) who (ownedAdvance event owned pair.1 (pick pair.2))) joint
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at regrouped
        simpa only [PMF.bind_bind, PMF.bind_map, Function.comp_def] using regrouped
      _ = (prior.map key).bind (keyTarget (P (build policy)) who) := by
        apply bind_congr_on_support _
        intro current member
        obtain ⟨seed, supported, rfl⟩ := keyed current member
        change _ = keyTarget (P (build policy)) who (runKey (execution seed).application.config)
        rw [keyTarget_runKey (independent _), viewKey]
        by_cases pending : event ∉ (execution seed).application.config.cut.completed
        · have ready := readyAt seed supported pending
          have active := activeAt seed supported pending
          rw [lastErasedLaw_patch_step event agree _ ready
            (lastPick_eq_of_alone who _ (fun other otherReady => alone _ other ready otherReady)
              _)]
          unfold eventStep
          rw [actionLaw_lastDeviationProfile_owned base who _ _ ownedNode active]
          simp only [build, patchPolicy, ↓reduceIte]
          rw [ownedHead_self, PMF.bind_bind, PMF.bind_map, PMF.bind_bind]
          apply bind_congr_on_support _
          intro extra member
          obtain ⟨action, picked⟩ := supportPick seed supported pending extra
            (by rw [viewKey]; exact member)
          simp only [Function.comp_apply, picked, Option.elim_some, PMF.pure_bind]
          rw [step_eq_ownedStepped event owned _ ready action, PMF.pure_bind,
            ownedAdvance_runKey event owned _ ready action, keyTarget_runKey (independent _),
            State.drainConfig_lastErasedLaw (independent _)]
        · push Not at pending
          rw [lastErasedLaw_patch_completed event agree _ pending]
          simp only [stay seed _ (Or.inr pending), PMF.bind_const]
          exact keyTarget_runKey (independent _) _
      _ = _ := PMF.bind_map _ _ _

/-- **The deviator's sole event.** From a coupled prior whose deviator
traffic is noise read from its normalized view of the order-free key, the
phase that completes an event of the deviator ready alone has a successor key
and final traffic of the same factored form, and a graph policy built from the
deviator's conditional choice there has, on average, the last-served
erased-key law of its tail after the phase. -/
theorem lastOwned_phase
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler) (horizon : Nat)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode)
    (reference base : (serviceGraph setup mode).BehavioralProfile) (who : Player)
    (deviation : (serviceApplication setup mode duration leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    {Seed : Type} (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode duration leaks).Execution)
    (quiescent : ∀ seed ∈ prior.support, ∀ query,
      ¬ (execution seed).application.AutomaticReady query)
    (pendingPrefix : ∀ seed ∈ prior.support,
      event ∉ (execution seed).application.config.cut.completed →
        (execution seed).application.config.cut.IsPrefix event.val)
    (automaticPast : ∀ seed ∈ prior.support,
      event ∈ (execution seed).application.config.cut.completed →
        observedAction event ((serviceGraph setup mode).normalizeObservation who
          ((serviceGraph setup mode).playerObserve who
            (execution seed).application.config)) = none)
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
    ∃ (build : (serviceGraph setup mode).BehavioralPolicy who →
        (serviceGraph setup mode).BehavioralPolicy who)
      (nextNoise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _),
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
          keyTarget ((serviceGraph setup mode).lastDeviationProfile base who (build policy)) who
            (runKey (execution seed).application.config) := by
  obtain ⟨build, nextNoise, joint, averaged, _⟩ := lastOwned_phase_patched scheduler horizon
    bound turns timing reference base who deviation independent event owned alone prior execution
    quiescent pendingPrefix automaticPast completes noise factor
  exact ⟨build, nextNoise, joint, averaged⟩

end Vegas
