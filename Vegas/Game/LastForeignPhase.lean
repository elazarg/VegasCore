/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ReferenceForeignTraffic
import Vegas.Game.RevealServiceSoleSegment

/-! # An honest binding, served last

At a boundary where an honest owner's binding is ready alone, its client draws
the reference's action and the deviator's traffic law depends only on its
starting traffic and on whether the binding was admitted, which its next view
shows. The order-free key after the phase is a function of the key before it
and the owner's action, so the deviator's final traffic is again noise read
from its normalized view. The last-served erased-key law of every normalized
deviation of a base whose normalization is the reference is invariant under
the phase seed by seed.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Graph

variable {graph : Vegas.EventGraph Player L}

/-- The step of an owned event reaches the completion with some output. -/
theorem ownedStepped_eq_complete {owner : Player} (event : graph.EventId)
    (owned : graph.actor? event = some owner) (config : graph.Config)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    ∃ value, ownedStepped event owned config ready action =
      config.complete event ready action value := by
  have member : ownedStepped event owned config ready action ∈
      (config.step event ready action).support := by
    rw [step_eq_ownedStepped event owned config ready action, PMF.support_pure]
    rfl
  unfold Config.step at member
  rw [PMF.support_map] at member
  obtain ⟨value, _, same⟩ := member
  exact ⟨value, same.symm⟩

/-- The drained step of an owned event records the event's completion and the
defaults of that completion. -/
theorem ownedStepped_drain_record {owner : Player} (event : graph.EventId)
    (owned : graph.actor? event = some owner) (config : graph.Config)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    ∃ value,
      completionOf (State.drainConfig (ownedStepped event owned config ready action)) event =
        some (EventGraph.completion graph event (config.actualDecision event action) value) ∧
      (State.drainConfig (ownedStepped event owned config ready action)).defaulted =
        (config.complete event ready action value).defaulted := by
  obtain ⟨value, stepped⟩ := ownedStepped_eq_complete event owned config ready action
  refine ⟨value, ?_, ?_⟩
  · have recorded : completionOf (config.complete event ready action value) event =
        some (EventGraph.completion graph event (config.actualDecision event action) value) := by
      rw [completionOf_complete, Function.update_self]
    rw [stepped]
    exact Config.Step.path_completionOf_of_some
      (State.ofConfig (config.complete event ready action value)).drain_graph_steps event _
      recorded
  · rw [stepped]
    exact State.drain_defaulted (State.ofConfig (config.complete event ready action value))

/-- A binding's completion defaults its active owner exactly when the binding
is not admitted. -/
theorem bind_completion_defaultEvent (config : graph.Config) (event : graph.EventId)
    {owner : Player} {payload : L.Ty} (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (active : owner ∉ config.defaulted) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (EventGraph.completion graph event (config.actualDecision event action) value).defaultEvent =
      if (cast (congrArg EventField.Action outputEq) action).isSome then none
      else some owner := by
  have actionEq : action = cast (congrArg EventField.Action outputEq.symm)
      (cast (congrArg EventField.Action outputEq) action) := by simp only [cast_cast, cast_eq]
  have valueEq : value = cast (congrArg EventField.Value outputEq.symm)
      (cast (congrArg EventField.Value outputEq) value) := by simp only [cast_cast, cast_eq]
  generalize chosen : cast (congrArg EventField.Action outputEq) action = choice at actionEq
  rw [actionEq, valueEq]
  cases choice with
  | none =>
      rw [config.completion_bind_none_defaultEvent event owner payload outputEq codeEq,
        ite_eq_right active]
      rfl
  | some result =>
      rw [config.completion_bind_some_defaultEvent event owner payload outputEq codeEq]
      rfl

end Graph

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **An honest binding.** From a coupled prior whose deviator traffic is noise
read from its normalized view of the order-free key, the phase that completes
an honest owner's binding ready alone has a successor key and final traffic of
the same factored form, and leaves the last-served erased-key law of every
normalized deviation of the base unchanged, when the honest clients follow the
normalized base. -/
theorem lastForeign_phase
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (horizon : Nat)
    (delay bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (base : (serviceGraph setup mode).BehavioralProfile)
    (referenceIndependent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (event : (serviceGraph setup mode).EventId) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner) (foreign : owner ≠ who)
    {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    {Seed : Type} (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (supported : ∀ seed ∈ prior.support, execution seed ∈
      ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
          turns (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile
            base)) who deviation)
        (execution seed).environmentRecall.length).support)
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (pendingPrefix : ∀ seed ∈ prior.support,
      event ∉ (execution seed).application.config.cut.completed →
        (execution seed).application.config.cut.IsPrefix event.val)
    (untouched : ∀ seed ∈ prior.support,
      event ∉ (execution seed).application.config.cut.completed →
        Untouched setup leaks event (execution seed))
    (automaticPast : ∀ seed ∈ prior.support,
      event ∈ (execution seed).application.config.cut.completed →
        owner ∈ (execution seed).application.config.defaulted ∧
          (completionOf (execution seed).application.config event).bind
            EventCompletion.defaultEvent = none)
    (noise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _)
    (factor : prior.map (fun seed => (runKey (execution seed).application.config,
        (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map fun seed => runKey (execution seed).application.config).bind fun current =>
        (noise (keyView who current)).map fun extra => (current, extra)) :
    ∃ nextNoise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _,
      (prior.bind fun seed =>
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
            (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
            who deviation)
          (fun current => event ∈ current.application.config.cut.completed) horizon
          (execution seed)).map fun final => (runKey final.application.config,
            (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
        (prior.bind fun seed =>
          ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
            (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
              (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile
                base)) who deviation)
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).map fun final => runKey final.application.config).bind
          (fun current => (nextNoise (keyView who current)).map fun extra => (current, extra)) ∧
      ∀ policy, (prior.bind fun seed =>
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
            (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
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
  let app := serviceApplication setup mode deadline leaks
  let runtime := serviceRuntime setup mode deadline
  let R := G.normalizeProfile base
  let honest := serviceReferenceTurnPolicy setup mode deadline leaks bound turns
    (firstTurnTiming setup turns mode) R
  let players := Function.update honest who deviation
  let stop := fun current : app.Execution => event ∈ current.application.config.cut.completed
  let phase := fun seed => app.runUntilHorizon scheduler players stop horizon (execution seed)
  let key := fun seed => runKey (execution seed).application.config
  let traffic := runtime.bindingTraffic leaks who
  let normal := fun config : G.Config => G.normalizeObservation who (G.playerObserve who config)
  let member := fun (action : G.Action event) past view =>
    if serviceTurn setup mode deadline leaks owner event past view = some 0 then
      decidedOpportunity setup leaks bound owner event action past view
    else honest owner past view
  let decided := fun seed (action : G.Action event) => app.runUntilHorizon scheduler
    (Function.update players owner (member action)) stop horizon (execution seed)
  have ownedNode : (G.nodes event).actor = some owner := owned
  have follows : players owner = honest owner := Function.update_of_ne foreign _ _
  have solitary : G.Solitary event := fun _ _ otherReady ready => alone _ _ ready otherReady
  have notPublication : ¬ (G.outputLayout event).IsPublication := by
    rw [outputEq]
    exact fun impossible => impossible
  have traceAt (seed : Seed) (present : seed ∈ prior.support) :
      Nonempty ((app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨horizon - (execution seed).environmentRecall.length, none, execution seed⟩)) :=
    app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler players _
      (bounded seed present) _ (supported seed present)
  have quiescentAt (seed : Seed) (present : seed ∈ prior.support) :
      ∀ query, ¬ (execution seed).application.AutomaticReady query := by
    obtain ⟨trace⟩ := traceAt seed present
    exact (legalFacts setup leaks horizon scheduler _ trace).quiescent
  have readyAt (seed : Seed) (present : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed) :
      (execution seed).application.config.cut.Ready event := by
    simpa only [Fin.eta] using (pendingPrefix seed present pending).ready event.isLt
  have activeAt (seed : Seed) (present : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed) :
      owner ∉ (execution seed).application.config.defaulted :=
    (execution seed).application.active_of_ready_owned (quiescentAt seed present)
      (readyAt seed present pending) owned
  have stoppedAt (seed : Seed)
      (completed : event ∈ (execution seed).application.config.cut.completed)
      (others : Player → app.Policy) :
      app.runUntilHorizon scheduler others stop horizon (execution seed) =
        PMF.pure (execution seed) :=
    app.runUntil_of_stop scheduler others _ _ _ completed
  have mixture (seed : Seed) (present : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed) :
      phase seed = (actionLaw R (execution seed).application.config event).bind
        (decided seed) := by
    have ready := readyAt seed present pending
    have active := activeAt seed present pending
    let law := R owner event ownedNode (G.playerObserve owner (execution seed).application.config)
      active
    have callback (current : app.Execution)
        (same : current.application.config = (execution seed).application.config) :
        serviceReferencePolicy setup mode deadline leaks R owner (current.logs owner)
            (current.observe app owner) =
          law.map (fun action => runtime.canonicalServiceDecision leaks owner
            (current.logs owner) (current.observe app owner) event action) := by
      have currentReady : current.application.config.cut.Ready event := same.symm ▸ ready
      have turn := serviceOwnTurn?_of_ready setup current.application currentReady owned
      have currentActive : owner ∉ current.application.config.defaulted := same.symm ▸ active
      have kernel (left right : G.Config) (sameConfig : left = right)
          (leftActive : owner ∉ left.defaulted) (rightActive : owner ∉ right.defaulted) :
          R owner event ownedNode (G.playerObserve owner left) leftActive =
            R owner event ownedNode (G.playerObserve owner right) rightActive := by
        subst sameConfig
        rfl
      rw [sourceServiceCanonicalPolicy_at_event_reference setup leaks R owner current event
        turn owned, dite_eq_right currentActive]
      exact congrArg (PMF.map _) (kernel _ _ same currentActive active)
    have mixed := serviceReference_firstTurn_mixture runtime leaks scheduler bound R owner event
      owned solitary players follows (execution seed) ready (supported seed present)
      (untouched seed present pending) (bounded seed present) law callback
    rw [actionLaw_of_actor _ _ ownedNode, dite_eq_right active]
    exact mixed
  have continued (seed : Seed) (present : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed)
      {Result : Type} (continuation : G.Config → PMF Result)
      (drained : ∀ state : EventGraphRuntime.State G,
        continuation state.drain.config = continuation state.config)
      (action : G.Action event) :
      (decided seed action).bind (fun final => continuation final.application.config) =
        ((execution seed).application.config.step event (readyAt seed present pending)
          action).bind continuation :=
    serviceReference_fixedAction_continuation runtime leaks scheduler delay bound R continuation
      drained contract timely owner event owned solitary players follows action (execution seed)
      (readyAt seed present pending) (supported seed present) (untouched seed present pending)
      (bounded seed present)
      (effectiveAction_of_not_publication _ event notPublication action)
  have endpoint (seed : Seed) (present : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed)
      (action : G.Action event) (final : app.Execution)
      (reached : final ∈ (decided seed action).support) :
      runKey final.application.config = ownedAdvance event owned (key seed) (some action) := by
    have ready := readyAt seed present pending
    let readout := fun config : G.Config => PMF.pure (runKey (State.drainConfig config))
    have drained (state : EventGraphRuntime.State G) :
        readout state.drain.config = readout state.config := by
      simp only [readout]
      rw [State.drainConfig_drain]
    have law := continued seed present pending readout drained action
    rw [step_eq_ownedStepped event owned _ ready action, PMF.pure_bind] at law
    have keyed : runKey (State.drainConfig final.application.config) =
        runKey (State.drainConfig (ownedStepped event owned _ ready action)) := by
      have member : runKey (State.drainConfig final.application.config) ∈
          ((decided seed action).bind fun final => readout final.application.config).support := by
        rw [PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨final, reached, by simp [readout]⟩
      rw [law] at member
      simpa only [readout, PMF.support_pure, Set.mem_singleton_iff] using member
    obtain ⟨trace⟩ := traceAt seed present
    let remaining := horizon - (execution seed).environmentRecall.length
    change final ∈ (app.runUntil scheduler (Function.update players owner (member action)) stop
      remaining (execution seed)).support at reached
    obtain ⟨used, enough, rounds, _⟩ := app.runUntil_runRounds scheduler
      (Function.update players owner (member action)) stop remaining (execution seed) final reached
    obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (serviceInitialLaw setup mode) horizon scheduler
      (Function.update players owner (member action)) (remaining - used) used (execution seed)
      final (by simpa only [Nat.sub_add_cancel enough] using trace) rounds
    have quiet := (legalFacts setup leaks horizon scheduler _ finalTrace).quiescent
    rw [← State.runKey_drainConfig_of_quiescent final.application quiet, keyed,
      ownedAdvance_runKey event owned _ ready action]
  let choiceAt : RunKey G → PMF (G.Action event) := fun current =>
    if found : ∃ config : G.Config, runKey config = current then
      actionLaw R found.choose event
    else PMF.pure ((G.nodes event).failureAction owner ownedNode)
  have choiceKey (config : G.Config) : choiceAt (runKey config) = actionLaw R config event := by
    have found : ∃ other : G.Config, runKey other = runKey config := ⟨config, rfl⟩
    change (if found : ∃ other : G.Config, runKey other = runKey config then
      actionLaw R found.choose event else _) = _
    rw [dite_eq_left found]
    exact referenceIndependent.congr found.choose_spec event
  let advance := fun current (action : G.Action event) =>
    ownedAdvance event owned current (some action)
  let step := fun seed (action : G.Action event) =>
    if event ∈ (execution seed).application.config.cut.completed then
      PMF.pure (traffic (execution seed))
    else (decided seed action).map traffic
  have stay (seed : Seed) (completed : event ∈ (execution seed).application.config.cut.completed)
      (action : G.Action event) : advance (key seed) action = key seed := by
    apply ownedAdvance_of_not_ready
    intro config keyEq ready
    have cuts : config.cut = (execution seed).application.config.cut := congrArg Prod.fst keyEq
    exact ready.1 (cuts ▸ completed)
  have keyed (current : RunKey G) (member : current ∈ (prior.map key).support) :
      ∃ seed ∈ prior.support, key seed = current := by
    obtain ⟨seed, present, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact ⟨seed, present, same⟩
  have viewKey (seed : Seed) :
      keyView who (key seed) = some (normal (execution seed).application.config) :=
    keyView_runKey who _
  have pendingNext (seed : Seed) (present : seed ∈ prior.support)
      (pending : event ∉ (execution seed).application.config.cut.completed)
      (action : G.Action event) :
      ∃ next : G.Config,
        keyView who (advance (key seed) action) = some (normal next) ∧
        Relation.ReflTransGen Config.Step (execution seed).application.config next ∧
        (completionOf next event).bind EventCompletion.defaultEvent =
          (if (cast (congrArg EventField.Action outputEq) action).isSome then none
            else some owner) ∧
        (completionOf next event).isSome ∧
        (owner ∈ next.defaulted ↔
          (cast (congrArg EventField.Action outputEq) action).isSome = false) := by
    have ready := readyAt seed present pending
    have active := activeAt seed present pending
    obtain ⟨path, _, _⟩ := ownedStepped_drain event owned _ ready active action
    obtain ⟨value, recorded, defaultedEq⟩ := ownedStepped_drain_record event owned _ ready action
    have defaults := bind_completion_defaultEvent _ event outputEq codeEq active action value
    refine ⟨_, ?_, path, ?_, ?_, ?_⟩
    · change keyView who (ownedAdvance event owned
        (runKey (execution seed).application.config) (some action)) = _
      rw [ownedAdvance_runKey event owned _ ready action]
      exact keyView_runKey who _
    · rw [recorded, Option.bind_some]
      exact defaults
    · rw [recorded]
      rfl
    · rw [defaultedEq]
      unfold EventGraph.Config.defaulted
      rw [Config.complete_defaults, defaults]
      by_cases admitted : (cast (congrArg EventField.Action outputEq) action).isSome
      · rw [ite_eq_left admitted, DefaultHistory.defaulted_record_none]
        simp only [admitted, Bool.true_eq_false, iff_false]
        exact active
      · rw [ite_eq_right admitted, DefaultHistory.defaulted_record_some]
        simp only [Finset.mem_insert, true_or, true_iff]
        simpa using admitted
  have paired (left : Seed) (leftSupport : left ∈ prior.support) (right : Seed)
      (rightSupport : right ∈ prior.support) (leftAction rightAction : G.Action event)
      (same : keyView who (advance (key left) leftAction) =
        keyView who (advance (key right) rightAction)) :
      normal (execution left).application.config =
          normal (execution right).application.config ∧
        (event ∉ (execution left).application.config.cut.completed →
          event ∉ (execution right).application.config.cut.completed ∧
          (cast (congrArg EventField.Action outputEq) leftAction).isSome =
            (cast (congrArg EventField.Action outputEq) rightAction).isSome) ∧
        (event ∈ (execution left).application.config.cut.completed →
          event ∈ (execution right).application.config.cut.completed) := by
    by_cases leftPending : event ∉ (execution left).application.config.cut.completed <;>
    by_cases rightPending : event ∉ (execution right).application.config.cut.completed
    · obtain ⟨leftNext, leftView, leftPath, leftDefault, leftPresent, _⟩ :=
        pendingNext left leftSupport leftPending leftAction
      obtain ⟨rightNext, rightView, rightPath, rightDefault, _, _⟩ :=
        pendingNext right rightSupport rightPending rightAction
      rw [leftView, rightView] at same
      have nexts : normal leftNext = normal rightNext := Option.some.inj same
      refine ⟨normalizeObservation_playerObserve_of_paths who
        (pendingPrefix left leftSupport leftPending)
        (pendingPrefix right rightSupport rightPending) leftPath rightPath nexts,
        fun _ => ⟨rightPending, ?_⟩, fun done => (leftPending done).elim⟩
      have defaults := normalize_defaultEvent_congr who nexts event leftPresent
      rw [leftDefault, rightDefault] at defaults
      revert defaults
      cases (cast (congrArg EventField.Action outputEq) leftAction).isSome <;>
        cases (cast (congrArg EventField.Action outputEq) rightAction).isSome <;> simp
    · exfalso
      push Not at rightPending
      obtain ⟨leftNext, leftView, _, leftDefault, leftPresent, leftOwner⟩ :=
        pendingNext left leftSupport leftPending leftAction
      rw [leftView, stay right rightPending, viewKey] at same
      have nexts := Option.some.inj same
      obtain ⟨rightDefaulted, rightNone⟩ := automaticPast right rightSupport rightPending
      have defaultedEq := normalize_defaulted_congr who nexts
      have ownerIn : owner ∈ leftNext.defaulted := defaultedEq ▸ rightDefaulted
      have notAdmitted := leftOwner.mp ownerIn
      have defaults := normalize_defaultEvent_congr who nexts event leftPresent
      rw [leftDefault, rightNone, notAdmitted] at defaults
      cases defaults
    · exfalso
      push Not at leftPending
      obtain ⟨rightNext, rightView, _, rightDefault, rightPresent, rightOwner⟩ :=
        pendingNext right rightSupport rightPending rightAction
      rw [rightView, stay left leftPending, viewKey] at same
      have nexts := (Option.some.inj same).symm
      obtain ⟨leftDefaulted, leftNone⟩ := automaticPast left leftSupport leftPending
      have defaultedEq := normalize_defaulted_congr who nexts
      have ownerIn : owner ∈ rightNext.defaulted := defaultedEq ▸ leftDefaulted
      have notAdmitted := rightOwner.mp ownerIn
      have defaults := normalize_defaultEvent_congr who nexts event rightPresent
      rw [rightDefault, leftNone, notAdmitted] at defaults
      cases defaults
    · push Not at leftPending rightPending
      rw [stay left leftPending, stay right rightPending, viewKey, viewKey] at same
      exact ⟨Option.some.inj same, fun pending => (pending leftPending).elim,
        fun _ => rightPending⟩
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior key
    (fun seed => traffic (execution seed)) (keyView who) noise factor choiceAt advance
    (keyView who) step
    (fun left leftMember _ _ right rightMember _ _ same => by
      obtain ⟨leftSeed, leftSupport, rfl⟩ := keyed left leftMember
      obtain ⟨rightSeed, rightSupport, rfl⟩ := keyed right rightMember
      rw [viewKey, viewKey]
      exact congrArg some (paired leftSeed leftSupport rightSeed rightSupport _ _ same).1)
    (fun left leftSupport leftAction _ right rightSupport rightAction _ same trafficEq => by
      obtain ⟨_, pendingFacts, completedFacts⟩ :=
        paired left leftSupport right rightSupport leftAction rightAction same
      by_cases leftPending : event ∉ (execution left).application.config.cut.completed
      · obtain ⟨rightPending, admitted⟩ := pendingFacts leftPending
        simp only [step, ite_eq_right leftPending, ite_eq_right rightPending]
        have fixedLeft := reference_foreign_fixedRun (horizon := horizon) scheduler bound turns R
          who deviation owner event owned alone leftAction (execution left)
          (readyAt left leftSupport leftPending)
        have fixedRight := reference_foreign_fixedRun (horizon := horizon) scheduler bound turns R
          who deviation owner event owned alone rightAction (execution right)
          (readyAt right rightSupport rightPending)
        change (app.runUntilHorizon scheduler
          (Function.update players owner (member leftAction)) stop horizon
            (execution left)).map traffic =
          (app.runUntilHorizon scheduler
          (Function.update players owner (member rightAction)) stop horizon
            (execution right)).map traffic
        rw [fixedLeft, fixedRight]
        have congruence := reference_binding_traffic_congr (horizon := horizon) scheduler bound
          turns R who owner deviation foreign event outputEq codeEq node alone
          (cast (congrArg EventField.Action outputEq) leftAction)
          (cast (congrArg EventField.Action outputEq) rightAction) admitted
          (execution left) (execution right) (readyAt left leftSupport leftPending)
          (readyAt right rightSupport rightPending) (supported left leftSupport)
          (supported right rightSupport) (untouched left leftSupport leftPending)
          (untouched right rightSupport rightPending) (bounded left leftSupport)
          (bounded right rightSupport) trafficEq
        simpa only [cast_cast, cast_eq] using congruence
      · push Not at leftPending
        have rightCompleted := completedFacts leftPending
        simp only [step, ite_eq_left leftPending, ite_eq_left rightCompleted]
        exact congrArg PMF.pure trafficEq)
  have pairs : (prior.bind fun seed => (phase seed).map fun final =>
      (runKey final.application.config, traffic final)) =
      prior.bind fun seed => (choiceAt (key seed)).bind fun action =>
        (step seed action).map fun extra => (advance (key seed) action, extra) := by
    apply bind_congr_on_support _
    intro seed present
    by_cases pending : event ∉ (execution seed).application.config.cut.completed
    · rw [mixture seed present pending, PMF.map_bind, choiceKey]
      apply bind_congr_on_support _
      intro action _
      simp only [step, ite_eq_right pending]
      rw [PMF.map_comp]
      apply map_congr_on_support _
      intro final reached
      simp only [Function.comp_apply, endpoint seed present pending action final reached]
      rfl
    · push Not at pending
      have stopped : phase seed = PMF.pure (execution seed) := stoppedAt seed pending players
      rw [stopped, PMF.pure_map]
      simp only [step, ite_eq_left pending, PMF.pure_map, stay seed pending]
      rw [PMF.bind_const]
  have marginal : (prior.bind fun seed => (phase seed).map fun final =>
      runKey final.application.config) =
      (prior.map key).bind fun current => (choiceAt current).map (advance current) := by
    have projected := congrArg (PMF.map Prod.fst) (pairs.trans law)
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const,
      PMF.bind_pure] at projected
    rw [← projected]
  refine ⟨nextNoise, ?_, ?_⟩
  · change (prior.bind fun seed => (phase seed).map fun final =>
      (runKey final.application.config, traffic final)) =
      (prior.bind fun seed => (phase seed).map fun final =>
        runKey final.application.config).bind _
    rw [pairs, law, marginal]
  · intro policy
    let P := G.lastDeviationProfile base who policy
    have independentP : LastIndependent P who := independent policy
    let continuation := fun config : G.Config => keyTarget P who (runKey config)
    have drained (state : EventGraphRuntime.State G) :
        continuation state.drain.config = continuation state.config := by
      simp only [continuation, keyTarget_runKey independentP]
      exact State.drain_lastErasedLaw independentP state
    have foreignNode : (G.nodes event).actor ≠ some who := by
      rw [ownedNode]
      exact fun same => foreign (Option.some.inj same)
    apply bind_congr_on_support _
    intro seed present
    by_cases pending : event ∉ (execution seed).application.config.cut.completed
    · have ready := readyAt seed present pending
      change (phase seed).bind (fun final => continuation final.application.config) =
        continuation (execution seed).application.config
      rw [mixture seed present pending, PMF.bind_bind]
      rw [bind_congr_on_support _ (fun action _ =>
        continued seed present pending continuation drained action)]
      simp only [continuation, keyTarget_runKey independentP]
      have stepped := lastRun_step P who (execution seed).application.config
        (fun terminal => ready.1 (by rw [terminal]; exact Finset.mem_univ _)) event ready
        (lastPick_eq_of_alone who _ (fun other otherReady => alone _ other ready otherReady) _)
      have mapped := congrArg (PMF.map erasedKey) stepped
      rw [PMF.map_bind] at mapped
      change lastErasedLaw P who (execution seed).application.config = _ at mapped
      rw [mapped]
      unfold eventStep
      rw [actionLaw_lastDeviationProfile_other base who policy _ foreignNode, PMF.bind_bind]
      rfl
    · push Not at pending
      change (phase seed).bind (fun final => continuation final.application.config) =
        continuation (execution seed).application.config
      have stopped : phase seed = PMF.pure (execution seed) := stoppedAt seed pending players
      rw [stopped, PMF.pure_bind]

end Vegas
