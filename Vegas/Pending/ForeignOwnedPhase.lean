module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ForeignBindingTraffic
public import Vegas.Pending.FirstTurnAction
public import Vegas.Pending.CompletionTraffic
public import Vegas.EventGraph.PrefixConfiguration
public import GameTheory.Math.Probability.ConditionalObservation

@[expose] public section

/-! # The joint traffic law at a solitary foreign strategic event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {inputs : PMF graph.Inputs}

local notation "app" => reactiveApplication timeouts leaks

/-- Couple the fixed-action physical branches of a solitary foreign event, then
reuse them in the first-turn mixture. The active branch uses its selected
action; an already-defaulted head takes no further physical rounds. -/
theorem foreign_owned_checkpoint_successor_traffic_factor
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (delay bound : graph.EventId → Nat) (reference : graph.BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal owner : Player) (deviation : (app).Policy) (foreign : owner ≠ focal)
    (event : graph.EventId) (owned : graph.actor? event = some owner)
    (solitary : graph.Solitary event)
    {Seed : Type*} (prior : PMF Seed) (execution : Seed → (app).Execution)
    (config : Seed → graph.Config) :
    let traffic := bindingTraffic timeouts leaks focal
    let observe := graph.playerObserve focal
    let honest := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) reference
    let players := Function.update honest focal deviation
    let stop := fun final : (app).Execution => event ∈ final.application.config.cut.completed
    let phase := fun seed => (app).runUntilHorizon scheduler players stop horizon (execution seed)
    let fixed := fun action => Function.update (focalPlayers timeouts leaks focal deviation) owner
      (decidedTurnPolicy timeouts leaks bound owner event action)
    let fixedPhase := fun seed action =>
      (app).runUntilHorizon scheduler (fixed action) stop horizon (execution seed)
    ∀ (noise : graph.PlayerObservation focal → PMF _),
      prior.map (fun seed => (config seed, traffic (execution seed))) =
        (prior.map config).bind (fun before =>
          (noise (observe before)).map fun extra => (before, extra)) →
      (∀ seed ∈ prior.support, (config seed).cut.IsPrefix event.val) →
      (∀ seed ∈ prior.support, (execution seed).application.config = State.drainConfig
        (config seed)) →
      (∀ seed ∈ prior.support, owner ∉ (config seed).defaulted →
        PrefixBoundary (inputs.map State.initial) scheduler players event.val (execution seed)) →
      (∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) →
      (∀ seed ∈ prior.support, owner ∉ (config seed).defaulted →
        ∀ action ∈ (actionDistribution reference (config seed) event).support,
          EffectiveAction (config seed) event action) →
      (∀ left ∈ prior.support, ∀ right ∈ prior.support,
        ∀ leftAction ∈ (actionDistribution reference (config left) event).support,
        ∀ rightAction ∈ (actionDistribution reference (config right) event).support,
        ∀ (leftReady : (config left).cut.Ready event)
          (rightReady : (config right).cut.Ready event),
        owner ∉ (config left).defaulted → owner ∉ (config right).defaulted →
        (execution left).application.config = config left →
        (execution right).application.config = config right →
        ∀ leftPrimary ∈ ((config left).step event leftReady leftAction).support,
        ∀ rightPrimary ∈ ((config right).step event rightReady rightAction).support,
          observe leftPrimary = observe rightPrimary →
          traffic (execution left) = traffic (execution right) →
          (fixedPhase left leftAction).map traffic = (fixedPhase right rightAction).map traffic) →
      ∃ nextNoise : graph.PlayerObservation focal → PMF _,
        (prior.bind fun seed => (phase seed).map fun final =>
          (final.application.config, traffic final)) =
        (prior.bind fun seed =>
          if ready : (config seed).cut.Ready event then
            (eventStep reference (config seed) event ready).bind fun primary =>
              (nextNoise (observe primary)).map fun extra => (State.drainConfig primary, extra)
          else PMF.pure (config seed, traffic (execution seed))) := by
  classical
  intro traffic observe honest players stop phase fixed fixedPhase noise factor ordered native
    boundary bounded realizable coupled
  have follows : players owner = honest owner := Function.update_of_ne foreign _ _
  have ready (seed : Seed) (member : seed ∈ prior.support) : (config seed).cut.Ready event :=
    (ordered seed member).ready event.isLt
  have activeConfig (seed : Seed) (member : seed ∈ prior.support)
      (active : owner ∉ (config seed).defaulted) :
      (execution seed).application.config = config seed := by
    rw [native seed member]
    apply State.drainConfig_of_quiescent (State.ofConfig (config seed))
    intro other eligible
    have same := solitary _ eligible.1 (ready seed member)
    subst other
    have inactive := eligible.2
    rw [owned] at inactive
    exact active inactive
  have stutter (seed : Seed) (member : seed ∈ prior.support)
      (inactive : owner ∈ (config seed).defaulted) :
      phase seed = PMF.pure (execution seed) := by
    have eligible : (State.ofConfig (config seed)).AutomaticReady event := by
      refine ⟨ready seed member, ?_⟩
      rw [owned]
      exact inactive
    exact (automatic_checkpoint_native_stutter timeouts leaks scheduler players horizon
      (execution seed) (config seed) (native seed member) event eligible
      (fun _ other => solitary _ other (ready seed member))).1
  have trace (seed : Seed) (member : seed ∈ prior.support)
      (active : owner ∉ (config seed).defaulted) :=
    (app).raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler players
      (execution seed).environmentRecall.length (bounded seed member) (execution seed)
      (boundary seed member active).supported
  let choice := fun before => actionDistribution reference before event
  let advance := fun (before : graph.Config) (action : graph.Action event) =>
    if available : before.cut.Ready event then
      (before.step_eq_pure_of_actor event available action owner owned).choose
    else before
  have stepLaw (before : graph.Config) (available : before.cut.Ready event)
      (action : graph.Action event) :
      before.step event available action = PMF.pure (advance before action) := by
    simp only [advance, dite_eq_left available]
    exact (before.step_eq_pure_of_actor event available action owner owned).choose_spec
  have taken (seed : Seed) (support : seed ∈ prior.support) (action : graph.Action event) :
      advance (config seed) action ∈
        ((config seed).step event (ready seed support) action).support := by
    rw [stepLaw, PMF.mem_support_pure_iff]
  let branch := fun seed action =>
    if owner ∈ (config seed).defaulted then PMF.pure (execution seed)
    else fixedPhase seed action
  have mixed (seed : Seed) (member : seed ∈ prior.support) :
      phase seed = (choice (config seed)).bind (branch seed) := by
    by_cases inactive : owner ∈ (config seed).defaulted
    · rw [stutter seed member inactive]
      simp only [branch, ite_eq_left inactive, PMF.bind_const]
    · simpa only [branch, ite_eq_right inactive, choice, activeConfig seed member inactive]
        using foreign_firstTurn_mixture scheduler bound reference focal deviation owner event
          owned foreign solitary (execution seed) (boundary seed member inactive)
          (bounded seed member)
  have aligned (seed : Seed) (member : seed ∈ prior.support) (action : graph.Action event)
      (selected : action ∈ (choice (config seed)).support) :
      ∀ final ∈ (branch seed action).support,
        final.application.config = State.drainConfig (advance (config seed) action) := by
    intro final reached
    by_cases inactive : owner ∈ (config seed).defaulted
    · simp only [branch, ite_eq_left inactive, PMF.mem_support_pure_iff] at reached
      subst final
      have drained := State.step_drainConfig_of_defaulted (config seed) event (ready seed member)
        (fun _ other => solitary _ other (ready seed member)) owner owned inactive action
      rw [stepLaw, PMF.pure_map] at drained
      have equal : State.drainConfig (advance (config seed) action) =
          State.drainConfig (config seed) := by
        apply (PMF.mem_support_pure_iff _ _).mp
        rw [← drained, PMF.mem_support_pure_iff]
      exact (native seed member).trans equal.symm
    · have sameConfig := activeConfig seed member inactive
      have available : (execution seed).application.config.cut.Ready event :=
        sameConfig.symm ▸ ready seed member
      have law := firstTurn_fixedAction_continuation timeouts leaks scheduler delay bound
        reference (fun current => PMF.pure (State.drainConfig current))
        (fun state => congrArg PMF.pure (State.drainConfig_drain_eq state))
        contract timely owner event owned solitary players follows action (execution seed)
        available (boundary seed member inactive).supported
        (fun who => (boundary seed member inactive).untouched event le_rfl who)
        (bounded seed member) (by
          rw [sameConfig]
          exact realizable seed member inactive action selected)
      have sameStep {before after : graph.Config} (same : before = after)
          (left : before.cut.Ready event) (right : after.cut.Ready event) :
          before.step event left action = after.step event right action := by
        subst after
        rfl
      dsimp only [players, honest] at law
      rw [foreign_firstTurn_fixedRun (horizon := horizon) scheduler bound turns reference focal
        deviation owner event owned solitary action (execution seed) available,
        sameStep sameConfig available (ready seed member), stepLaw, PMF.pure_bind] at law
      have fixedAt : branch seed action =
          (app).runUntilHorizon scheduler (fixed action) stop horizon (execution seed) := by
        simp only [branch, ite_eq_right inactive, fixedPhase]
      have exactLaw : (branch seed action).map (fun final =>
          State.drainConfig final.application.config) =
            PMF.pure (State.drainConfig (advance (config seed) action)) := by
        rw [fixedAt]
        exact law
      have drained : State.drainConfig final.application.config =
          State.drainConfig (advance (config seed) action) := by
        have present : State.drainConfig final.application.config ∈ ((branch seed action).map
            (fun current => State.drainConfig current.application.config)).support :=
          (PMF.mem_support_map_iff _ _ _).mpr ⟨final, reached, rfl⟩
        rwa [exactLaw, PMF.mem_support_pure_iff] at present
      rw [fixedAt] at reached
      obtain ⟨used, within, rounds, _⟩ := (app).runUntil_runRounds scheduler (fixed action) stop
        (horizon - (execution seed).environmentRecall.length) (execution seed) final reached
      obtain ⟨startTrace⟩ := trace seed member inactive
      obtain ⟨endTrace⟩ := (app).raw_trace_runRounds (inputs.map State.initial) horizon scheduler
        (fixed action) (horizon - (execution seed).environmentRecall.length - used) used
        (execution seed) final (by simpa only [Nat.sub_add_cancel within] using startTrace) rounds
      have quiet := (legalFacts timeouts leaks inputs horizon scheduler _ endTrace).quiescent
      exact (State.drainConfig_of_quiescent final.application quiet).symm.trans drained
  let step := fun seed action => (branch seed action).map traffic
  obtain ⟨nextNoise, joint⟩ := exists_updated_observation_kernel_of_readout prior config
    (fun seed => traffic (execution seed)) observe noise factor choice advance observe step
    (fun left leftSupport leftAction _ right rightSupport rightAction _ same => by
      obtain ⟨leftSeed, leftMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp leftSupport
      obtain ⟨rightSeed, rightMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rightSupport
      have leftPrevious := beforeCompletion_playerObserve_of_step focal (config leftSeed)
        event (ready leftSeed leftMember) leftAction _ (taken leftSeed leftMember leftAction)
      have rightPrevious := beforeCompletion_playerObserve_of_step focal (config rightSeed)
        event (ready rightSeed rightMember) rightAction _ (taken rightSeed rightMember rightAction)
      exact leftPrevious.symm.trans ((congrArg (beforeCompletion event) same).trans rightPrevious))
    (fun left leftSupport leftAction leftChosen right rightSupport rightAction rightChosen
        same observed => by
      have leftPrevious := beforeCompletion_playerObserve_of_step focal (config left)
        event (ready left leftSupport) leftAction _ (taken left leftSupport leftAction)
      have rightPrevious := beforeCompletion_playerObserve_of_step focal (config right)
        event (ready right rightSupport) rightAction _ (taken right rightSupport rightAction)
      have old := leftPrevious.symm.trans ((congrArg (beforeCompletion event) same).trans
        rightPrevious)
      have status : (config left).defaulted = (config right).defaulted :=
        congrArg EventPlayerObservation.defaulted old
      by_cases inactive : owner ∈ (config left).defaulted
      · have rightInactive : owner ∈ (config right).defaulted := status ▸ inactive
        simp only [step, branch, ite_eq_left inactive, ite_eq_left rightInactive,
          PMF.pure_map, observed]
      · have rightActive : owner ∉ (config right).defaulted := status ▸ inactive
        have transport := coupled left leftSupport right rightSupport leftAction leftChosen
          rightAction rightChosen (ready left leftSupport) (ready right rightSupport)
          inactive rightActive (activeConfig left leftSupport inactive)
          (activeConfig right rightSupport rightActive) _ (taken left leftSupport leftAction) _
          (taken right rightSupport rightAction) same observed
        simpa only [step, branch, ite_eq_right inactive, ite_eq_right rightActive]
          using transport)
  refine ⟨nextNoise, ?_⟩
  calc
    _ = (prior.bind fun seed => (choice (config seed)).bind fun action =>
          (step seed action).map fun extra => (advance (config seed) action, extra)).map
          (fun pair => (State.drainConfig pair.1, pair.2)) := by
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, step]
      apply bind_congr_on_support _
      intro seed supported
      rw [mixed seed supported, PMF.map_bind]
      apply bind_congr_on_support _
      intro action selected
      apply map_congr_on_support _
      intro final reached
      rw [aligned seed supported action selected final reached]
    _ = _ := by
      rw [joint]
      simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, PMF.bind_bind, Function.comp_def]
      apply bind_congr_on_support _
      intro seed supported
      simp only [dite_eq_left (ready seed supported), eventStep, choice, PMF.bind_bind]
      apply bind_congr_on_support _
      intro action _
      rw [stepLaw, PMF.pure_bind]

/-- Read the primary rank from a drained successor without changing its
joint traffic law. -/
theorem primary_rank_traffic_of_checkpoint_distribution
    {Seed Native Traffic View : Type*} (prior : PMF Seed) (phase : Seed → PMF Native)
    (config : Seed → graph.Config) (readConfig : Native → graph.Config)
    (arbitraryNative : Seed → Native) (traffic : Native → Traffic) (observe : graph.Config → View)
    (event : graph.EventId) (reference : graph.BehavioralProfile) (nextNoise : View → PMF Traffic)
    (ordered : ∀ seed ∈ prior.support, (config seed).cut.IsPrefix event.val)
    (joint :
      (prior.bind fun seed => (phase seed).map fun final => (readConfig final, traffic final)) =
      prior.bind fun seed =>
        if ready : (config seed).cut.Ready event then
          (eventStep reference (config seed) event ready).bind fun primary =>
            (nextNoise (observe primary)).map fun extra => (State.drainConfig primary, extra)
        else PMF.pure (config seed, traffic (arbitraryNative seed))) :
    (prior.bind phase).map (fun final =>
      (Config.rankPrefix (event.val + 1) (readConfig final), traffic final)) =
    (prior.bind fun seed =>
      if ready : (config seed).cut.Ready event then
        eventStep reference (config seed) event ready
      else PMF.pure (config seed)).bind fun primary =>
        (nextNoise (observe primary)).map fun extra => (primary, extra) := by
  have lifted := congrArg
    (PMF.map (fun pair => (Config.rankPrefix (event.val + 1) pair.1, pair.2))) joint
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at lifted
  rw [PMF.map_bind, PMF.bind_bind]
  refine lifted.trans ?_
  apply bind_congr_on_support _
  intro seed supported
  have ready := (ordered seed supported).ready event.isLt
  simp only [dite_eq_left ready, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp only [eventStep, PMF.bind_bind]
  apply bind_congr_on_support _
  intro action _
  apply bind_congr_on_support _
  intro primary moved
  have atRank : primary.cut.IsPrefix (event.val + 1) := by
    rw [(config seed).step_cut event ready action primary moved]
    exact (ordered seed supported).complete_at event ready rfl
  have restored := Config.rankPrefix_of_path atRank (State.ofConfig primary).drain_graph_steps
  change Config.rankPrefix (event.val + 1) (State.drainConfig primary) = primary at restored
  simp only [restored]

/-- Project the stopped ledger to the primary successor rank while retaining
its traffic. The prior may mix defaulted and active checkpoints. -/
theorem foreign_owned_checkpoint_primary_traffic_factor
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (delay bound : graph.EventId → Nat) (reference : graph.BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal owner : Player) (deviation : (app).Policy) (foreign : owner ≠ focal)
    (event : graph.EventId) (owned : graph.actor? event = some owner)
    (solitary : graph.Solitary event)
    {Seed : Type*} (prior : PMF Seed) (execution : Seed → (app).Execution)
    (config : Seed → graph.Config) :
    let traffic := bindingTraffic timeouts leaks focal
    let observe := graph.playerObserve focal
    let honest := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) reference
    let players := Function.update honest focal deviation
    let stop := fun final : (app).Execution => event ∈ final.application.config.cut.completed
    let phase := fun seed => (app).runUntilHorizon scheduler players stop horizon (execution seed)
    let fixed := fun action => Function.update (focalPlayers timeouts leaks focal deviation) owner
      (decidedTurnPolicy timeouts leaks bound owner event action)
    let fixedPhase := fun seed action =>
      (app).runUntilHorizon scheduler (fixed action) stop horizon (execution seed)
    ∀ (noise : graph.PlayerObservation focal → PMF _),
      prior.map (fun seed => (config seed, traffic (execution seed))) =
        (prior.map config).bind (fun before =>
          (noise (observe before)).map fun extra => (before, extra)) →
      (∀ seed ∈ prior.support, (config seed).cut.IsPrefix event.val) →
      (∀ seed ∈ prior.support, (execution seed).application.config = State.drainConfig
        (config seed)) →
      (∀ seed ∈ prior.support, owner ∉ (config seed).defaulted →
        PrefixBoundary (inputs.map State.initial) scheduler players event.val (execution seed)) →
      (∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) →
      (∀ seed ∈ prior.support, owner ∉ (config seed).defaulted →
        ∀ action ∈ (actionDistribution reference (config seed) event).support,
          EffectiveAction (config seed) event action) →
      (∀ left ∈ prior.support, ∀ right ∈ prior.support,
        ∀ leftAction ∈ (actionDistribution reference (config left) event).support,
        ∀ rightAction ∈ (actionDistribution reference (config right) event).support,
        ∀ (leftReady : (config left).cut.Ready event)
          (rightReady : (config right).cut.Ready event),
        owner ∉ (config left).defaulted → owner ∉ (config right).defaulted →
        (execution left).application.config = config left →
        (execution right).application.config = config right →
        ∀ leftPrimary ∈ ((config left).step event leftReady leftAction).support,
        ∀ rightPrimary ∈ ((config right).step event rightReady rightAction).support,
          observe leftPrimary = observe rightPrimary →
          traffic (execution left) = traffic (execution right) →
          (fixedPhase left leftAction).map traffic = (fixedPhase right rightAction).map traffic) →
      ∃ nextNoise : graph.PlayerObservation focal → PMF _,
        (prior.bind phase).map (fun final =>
          (Config.rankPrefix (event.val + 1) final.application.config, traffic final)) =
        (prior.bind fun seed =>
          if ready : (config seed).cut.Ready event then
            eventStep reference (config seed) event ready
          else PMF.pure (config seed)).bind fun primary =>
            (nextNoise (observe primary)).map fun extra => (primary, extra) := by
  intro traffic observe honest players stop phase fixed fixedPhase noise factor ordered native
    boundary bounded realizable coupled
  obtain ⟨nextNoise, joint⟩ := foreign_owned_checkpoint_successor_traffic_factor
    scheduler delay bound reference contract timely focal owner deviation foreign event owned
    solitary prior execution config noise factor ordered native boundary bounded realizable coupled
  exact ⟨nextNoise, primary_rank_traffic_of_checkpoint_distribution prior phase config (fun final =>
    final.application.config) execution traffic observe event reference nextNoise ordered joint⟩

end Vegas.EventGraphRuntime
