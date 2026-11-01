/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ObservationRecall
import Vegas.Compile.EventGraphStep
import Vegas.Game.SourceServiceCheckpoint
import GameTheoryExtensions.Math.Probability.ObservedChoice
import Interaction.ReactiveRawRoundTrace
import Vegas.Game.ServiceDeviationTraffic
import Vegas.Game.SourceServiceTurnPolicy
import Vegas.Game.SourceServiceCompletion
import Interaction.ReactiveMixtureRounds

/-! # Actual disclosure choices and a deviating player at a ready event

A successor view retains the preceding full view and the owner's actual
optional disclosure decision. An already defaulted owner records no new choice.
At a sole ready event owned by the deviator or by chance, all other first-turn
clients remain silent until the event completes. At the deviator's revelation, the joint
source-successor and native-traffic law has a behavioral source kernel. The actual ledger
endpoint is the typed source completion followed by deterministic automatic completion.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- The owner's successor view determines its prior view and the actual
optional choice. Boolean choices are recovered only for active callbacks. -/
theorem reveal_owner_view_reflects {Γ : SourceCtx Player L} {name : VarId}
    {who : Player} {payload : L.Ty} (published : VarId)
    (selected : HasVar Γ name (.commitment who payload))
    (left right : Config Player L Γ) (first second : Bool)
    (same : (revealSuccessor published selected left first).view who =
      (revealSuccessor published selected right second).view who) :
    left.view who = right.view who ∧
      (if who ∈ left.defaulted then none else some first) =
        (if who ∈ right.defaulted then none else some second) := by
  have prior := reveal_view_reflects who published selected left right first second same
  refine ⟨prior, ?_⟩
  have defaultsEq := congrArg DecisionView.defaulted prior
  change left.defaulted = right.defaulted at defaultsEq
  by_cases inactive : who ∈ left.defaulted
  · simp only [← defaultsEq, ite_eq_left inactive]
  · have rightActive : who ∉ right.defaulted := by rwa [← defaultsEq]
    have last := congrArg
      (fun view : DecisionView who ((published, .publication payload) :: Γ) =>
        view.history.getLast?) same
    simp only [Config.view, revealSuccessor, inactive, rightActive, ite_false,
      Function.update_self, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq, OwnAction.reveal.injEq, true_and] at last
    simp only [ite_eq_right inactive, ite_eq_right rightActive, last]

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- While an event is ready alone, no player but its actor has a turn. -/
theorem ownTurn?_none_of_alone {event : (serviceGraph setup mode).EventId}
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    (ready : state.config.cut.Ready event) (player : Player)
    (other : (serviceGraph setup mode).actor? event ≠ some player) :
    state.publicView.ownTurn? player = none := by
  cases turn : state.publicView.ownTurn? player with
  | none => rfl
  | some current =>
      obtain ⟨seen, owned⟩ := PublicView.ownTurn?_spec _ player current turn
      have same := alone _ current ready ((state.publicView_eventReady current).mp seen)
      subst same
      exact (other owned).elim

/-- Readiness at a pending event is preserved until that event completes. -/
theorem round_ready_of_pending
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {event : (serviceGraph setup mode).EventId}
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    {before after : (serviceApplication setup mode deadline leaks).Execution}
    (ready : before.application.config.cut.Ready event)
    (reached : after ∈ ((serviceApplication setup mode deadline leaks).round scheduler
      players before).support) (pending : event ∉ after.application.config.cut.completed) :
    after.application.config.cut.Ready event := by
  rw [reactive_round_config_eq_of_pending (serviceRuntime setup mode deadline) leaks scheduler
    players event before after (fun other otherReady => alone _ other ready otherReady)
    pending reached]
  exact ready

/-- Until the sole ready event of the deviator or of chance completes,
first-turn clients of the other players remain silent. -/
theorem runUntil_deviation_focal
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (focal : (serviceGraph setup mode).actor? event = none ∨ (serviceGraph setup mode).actor?
        event = some who)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event → cut.Ready
        other → other = event) (count : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (holds : event ∉ execution.application.config.cut.completed →
      execution.application.config.cut.Ready event) :
    (serviceApplication setup mode deadline leaks).runUntil scheduler
    (Function.update
      (serviceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) profile) who deviation)
    (fun final => event ∈ final.application.config.cut.completed) count execution =
    (serviceApplication setup mode deadline leaks).runUntil scheduler
    (focalPlayers setup leaks who deviation)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := serviceApplication setup mode deadline leaks
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
      simp only [serviceTurnPolicy, idle]
  · intro current currentHolds running next reached
    exact round_ready_of_pending alone (currentHolds running) reached
  · exact holds

private def disclosedAt (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (event : (serviceGraph setup mode).EventId)
    {observer : Player} (observed : (serviceGraph setup mode).PlayerObservation observer) : Bool :=
  OwnAction.disclosure ((observed.ownActions.find?
    (fun record => decide (record.event = event))).bind
    fun record => record.decision.bind (decodeEventAction setup.program record.event))

private theorem disclosedAt_record (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (who : Player)
    (native : EventGraphRuntime.State (serviceGraph setup mode))
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (action : (serviceGraph setup mode).Action event)
    (value : ((serviceGraph setup mode).outputLayout event).Value)
    (present : EventGraph.completion (serviceGraph setup mode) event (some action) value
      ∈ native.config.history) :
    disclosedAt setup mode event (native.playerView who).observation =
      OwnAction.disclosure (decodeEventAction setup.program event action) := by
  let record := EventGraph.completion (serviceGraph setup mode) event (some action) value
  have recalled : record ∈ (serviceGraph setup mode).ownCompletions who native.config.history :=
    (EventGraph.mem_ownCompletions who native.config.history record).2 ⟨present, owned, rfl⟩
  have found : ((serviceGraph setup mode).ownCompletions who native.config.history).find?
      (fun completion => decide (completion.event = event)) = some record := by
    cases selected : ((serviceGraph setup mode).ownCompletions who native.config.history).find?
        (fun completion => decide (completion.event = event)) with
    | none =>
        have absent := List.find?_eq_none.mp selected record recalled
        exact (absent (by simp only [record, EventGraph.completion, decide_true])).elim
    | some completion =>
        have current := List.mem_of_find?_eq_some selected
        have matching : completion.event = event := by
          simpa only [decide_eq_true_eq] using List.find?_some selected
        have retained := ((EventGraph.mem_ownCompletions who native.config.history completion).1
          current).1
        have equal : completion = record :=
          List.inj_on_of_nodup_map native.config.history_nodup retained present matching
        exact congrArg some equal
  simp only [disclosedAt, EventGraphRuntime.State.playerView, EventGraph.playerObserve, found,
    Option.bind_some, record, EventGraph.completion]
private theorem primary_reveal_joint {Seed : Type} {Γ : SourceCtx Player L} {name : VarId}
    {who : Player} {payload : L.Ty} (published : VarId)
    (binding : HasVar Γ name (.commitment who payload))
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (horizon : Nat) (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
      (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun traffic => (config, traffic))
    (active : ∀ seed ∈ prior.support, who ∉ (source seed).defaulted)
    (ready : ∀ seed ∈ prior.support, event ∉ (execution seed).application.config.cut.completed →
      (execution seed).application.config.cut.Ready event) :
    ∃ choice : DecisionView who Γ → PMF Bool,
      ∃ nextNoise : DecisionView who ((published, .publication payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (focalPlayers setup leaks who deviation)
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (revealSuccessor published binding (source seed)
              (disclosedAt setup mode event
                (final.application.playerView who).observation),
              (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
      ((prior.map source).bind fun config =>
        (choice (config.view who)).map (revealSuccessor published binding config)).bind
          fun config =>
          (nextNoise (config.view who)).map fun traffic => (config, traffic) := by
  let app := serviceApplication setup mode deadline leaks
  let read := fun seed => (serviceRuntime setup mode deadline).bindingTraffic leaks who
    (execution seed)
  let phase := fun seed => (app.runUntilHorizon scheduler (focalPlayers setup leaks who deviation)
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)).map
      ((serviceRuntime setup mode deadline).bindingTraffic leaks who)
  obtain ⟨channel, channelLaw⟩ := exists_updated_observation_kernel_of_readout prior source read
    (fun config => config.view who) noise factor
    (fun _ => PMF.pure ()) (fun config _ => config) (fun config => config.view who)
    (fun seed _ => phase seed)
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right rightSupport _ _ _ same => by
      have recalled := congrArg (fun traffic => traffic.2.2.1) same
      change (execution left).environmentRecall = (execution right).environmentRecall at recalled
      simp only [phase, ReactiveApplication.runUntilHorizon, recalled]
      exact focalPhase_traffic_congr scheduler who deviation (Or.inr owned) alone
        (horizon - (execution right).environmentRecall.length)
        (execution left) (execution right) (ready left leftSupport) (ready right rightSupport) same)
  have joint : (prior.bind fun seed => (phase seed).map fun traffic => (source seed, traffic)) =
      (prior.map source).bind fun config =>
        (channel (config.view who)).map fun traffic => (config, traffic) := by
    simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure] using channelLaw
  let pick := fun traffic : MessageNetwork Player app.Payload ×
      List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
      PlayerView (serviceGraph setup mode) × PublicView (serviceGraph setup mode) =>
      disclosedAt setup mode event traffic.2.2.2.2.1.observation
  let choice := fun view => (channel view).map pick
  let nextNoise := fun view : DecisionView who ((published, .publication payload) :: Γ) =>
    fiberPosterior (channel (view.back true)) pick (OwnAction.disclosure view.history.getLast?)
  refine ⟨choice, nextNoise, ?_⟩
  have remembered (config : Config Player L Γ) (isActive : who ∉ config.defaulted)
      (disclose : Bool) :
      OwnAction.disclosure
        ((revealSuccessor published binding config disclose).view who).history.getLast?
        = disclose := by
    simp only [Config.view, revealSuccessor, isActive, ite_false, Function.update_self,
      List.getLast?_append, List.getLast?_singleton, Option.some_or, OwnAction.disclosure]
  calc
    _ = (prior.bind fun seed => (phase seed).map fun traffic => (source seed, traffic)).map
        (fun pair => (revealSuccessor published binding pair.1 (pick pair.2), pair.2)) := by
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, phase, pick,
        EventGraphRuntime.bindingTraffic, app]
    _ = ((prior.map source).bind fun config =>
        (channel (config.view who)).map fun traffic => (config, traffic)).map
          (fun pair => (revealSuccessor published binding pair.1 (pick pair.2), pair.2)) := by
      rw [joint]
    _ = _ := by
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_bind, PMF.bind_map]
      apply bind_congr_on_support _
      intro seed supported
      rw [map_readout_choice (channel ((source seed).view who)) pick
        (fun disclose traffic =>
          (revealSuccessor published binding (source seed) disclose, traffic))]
      apply bind_congr_on_support _
      intro disclose _
      have backed : ((revealSuccessor published binding (source seed) disclose).view who).back
          true = (source seed).view who := by
        simpa using back_reveal_view who published binding (source seed) disclose
      simp only [nextNoise, backed, remembered _ (active seed supported)]


/-- A deviator's genuine disclosure has an observation-local source kernel.
The actual stopped ledger endpoint follows its typed source successor by automatic completion. -/
theorem sourceService_deviator_reveal_law
    {Seed : Type} {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (complete : CompletesPlay (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment who payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published who name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published who name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other,
      cut.Ready (embedding.event ⟨0, by simp [eventCount]⟩) → cut.Ready other →
        other = embedding.event ⟨0, by simp [eventCount]⟩)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.reveal published who name fresh binding unresolved next) profile refs
      (source seed).revelations (source seed).registry embedding refsBefore rank)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs rank
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) wholeProfile) who deviation) rank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun traffic => (config, traffic)) :
    let index : Fin (eventCount (.reveal published who name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (serviceGraph setup mode).EventId := embedding.event index
    let publicationRef : EventGraph.FieldRef (graphLayout setup.program) (.publication payload) :=
      by simpa [index, outputLayout, eventCount] using embedding.ref index
    let players := Function.update (serviceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) wholeProfile) who deviation
    let readChoice := fun final : (serviceApplication setup mode deadline leaks).Execution =>
      OwnAction.disclosure
        (((final.application.playerView who).observation.ownActions.find?
          (fun record => decide (record.event = event))).bind fun record =>
            record.decision.bind (decodeEventAction setup.program record.event))
    ∃ kernel : DecisionView who Γ → PMF Bool,
      ∃ nextNoise : DecisionView who ((published, .publication payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (revealSuccessor published binding (source seed) (readChoice final),
              (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
        (((prior.map source).bind fun config =>
          (kernel (config.view who)).map (revealSuccessor published binding config)).bind
            fun config => (nextNoise (config.view who)).map fun traffic => (config, traffic)) ∧
      ∀ seed ∈ prior.support, ∀ final ∈
          ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).support,
        ∃ (disclose : Bool) (native : EventGraphRuntime.State (serviceGraph setup mode)),
          SourceCheckpoint setup (revealSuccessor published binding (source seed) disclose)
            (refs.cons (name := published) publicationRef) (rank + 1) native.config ∧
          final.application.config = native.drain.config ∧ readChoice final = disclose := by
  intro index event publicationRef players readChoice
  let app := serviceApplication setup mode deadline leaks
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (serviceGraph setup mode).actor? event = some who := by
    change (toEventGraph setup.program).actor? event = some who
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have outputEq : (serviceGraph setup mode).outputLayout event = .publication payload :=
    publicationRef.layout_eq
  have codeEq (seed : Seed) :
      cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve who payload (refs.get binding)
          (compileChecks (published := published) refs (source seed).registry
            (source seed).revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using (aligned seed).graphSuffix.nodeEq index
  have decodedAction (disclose : Bool) : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal who name disclose) := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    simpa [event, index, outputEq, decodeEventAction] using lookup
  have readyAt (seed : Seed) (supported : seed ∈ prior.support) :
      (execution seed).application.config.cut.Ready event := by
    have ordered := (boundary seed supported).ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  have traceAt (seed : Seed) (supported : seed ∈ prior.support) :
      Nonempty ((app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨horizon - (execution seed).environmentRecall.length, none, execution seed⟩)) :=
    app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler players _
      (bounded seed supported) _ (boundary seed supported).supported
  have nativeActive (seed : Seed) (supported : seed ∈ prior.support) :
      who ∉ (execution seed).application.config.defaulted := by
    obtain ⟨trace⟩ := traceAt seed supported
    exact (execution seed).application.active_of_ready_owned
      (legalFacts setup leaks horizon scheduler _ trace).quiescent (readyAt seed supported) owned
  have sourceActive (seed : Seed) (supported : seed ∈ prior.support) :
      who ∉ (source seed).defaulted := by
    have defaults : (execution seed).application.config.defaulted = (source seed).defaulted :=
      congrArg DefaultHistory.defaulted (checkpoint seed).defaults
    rw [← defaults]
    exact nativeActive seed supported
  have phaseEq (seed : Seed) (supported : seed ∈ prior.support) :
      app.runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed) =
      app.runUntilHorizon scheduler (focalPlayers setup leaks who deviation)
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed) := by
    exact runUntil_deviation_focal scheduler bound turns wholeProfile who deviation event
      (Or.inr owned) alone _ (execution seed) (fun _ => readyAt seed supported)
  obtain ⟨kernel, nextNoise, law⟩ := primary_reveal_joint published binding setup leaks scheduler
    deviation event owned alone horizon prior source execution noise factor sourceActive
      (fun seed supported _ => readyAt seed supported)
  refine ⟨kernel, nextNoise, ?_, ?_⟩
  · calc
      _ = prior.bind (fun seed =>
          (app.runUntilHorizon scheduler (focalPlayers setup leaks who deviation)
            (fun final => event ∈ final.application.config.cut.completed) horizon
            (execution seed)).map fun final =>
              (revealSuccessor published binding (source seed) (readChoice final),
                (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) := by
        apply bind_congr_on_support _
        intro seed supported
        rw [phaseEq seed supported]
      _ = _ := law
  · intro seed supported final reached
    have ready := readyAt seed supported
    have completed : event ∈ final.application.config.cut.completed := by
      obtain ⟨trace⟩ := traceAt seed supported
      let remaining := horizon - (execution seed).environmentRecall.length
      change final ∈ (app.runUntil scheduler players
        (fun current => event ∈ current.application.config.cut.completed) remaining
        (execution seed)).support at reached
      rcases app.runUntil_stopped scheduler players _ remaining (execution seed) final reached
          with done | spent
      · exact done
      · obtain ⟨used, enough, rounds, lengthEq⟩ := app.runUntil_runRounds scheduler players _
          remaining (execution seed) final reached
        obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (serviceInitialLaw setup mode) horizon
          scheduler players (remaining - used) used (execution seed) final
          (by simpa only [Nat.sub_add_cancel enough] using trace) rounds
        have terminal := complete _ finalTrace (by
          change remaining - used = 0 ∧ _
          exact ⟨by dsimp only [remaining] at *; omega, rfl⟩)
        change final.application.config.cut.completed = Finset.univ at terminal
        rw [terminal]
        exact Finset.mem_univ _
    obtain ⟨action, native, primary, drained⟩ := runUntil_completed_primary_drain
      (serviceRuntime setup mode deadline) leaks scheduler players event
      (horizon - (execution seed).environmentRecall.length) (execution seed) final ready
      (fun other otherReady => alone _ other ready otherReady) who owned
      (nativeActive seed supported) reached completed
    let disclose : Bool := cast (congrArg EventGraph.EventField.Action outputEq) action
    have actionEq : action =
        cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose := by
      simp only [disclose, cast_cast, cast_eq]
    have status : (execution seed).application.config.defaulted = (source seed).defaulted :=
      congrArg DefaultHistory.defaulted (checkpoint seed).defaults
    have stepLaw := reveal_step (execution seed).application.config event ready outputEq
      refs (source seed).revelations (source seed).registry binding (codeEq seed)
        (source seed).state (checkpoint seed).agrees disclose
    have stepLaw' : (execution seed).application.config.step event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        PMF.pure ((execution seed).application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding (source seed) disclose))) := by
      simpa only [status, disclosureResult, revealSuccessor, Env.get, Env.cons] using stepLaw
    have configEq : native.config = (execution seed).application.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (disclosureResult published binding (source seed) disclose)) := by
      rw [actionEq, stepLaw', PMF.mem_support_pure_iff] at primary
      exact primary
    have nextCheckpoint := (checkpoint seed).reveal published binding event eventRank ready
      outputEq (fun ref => refsBefore ref index) disclose (decodedAction disclose)
    change SourceCheckpoint setup _ _ (rank + 1)
      ((execution seed).application.config.complete event ready _ _) at nextCheckpoint
    have refEq : publicationRef = ⟨.inr event, outputEq⟩ := by
      rfl
    have typed : SourceCheckpoint setup (revealSuccessor published binding (source seed) disclose)
        (refs.cons (name := published) publicationRef) (rank + 1) native.config := by
      rw [configEq, refEq]
      exact nextCheckpoint
    refine ⟨disclose, native, typed, drained, ?_⟩
    obtain ⟨value, _, recorded⟩ := (execution seed).application.config.step_completion event ready
      action native.config primary
    rw [(execution seed).application.config.actualDecision_of_active event who owned
      (nativeActive seed supported) action] at recorded
    obtain ⟨extra, retained⟩ := EventGraph.Config.Step.path_history_prefix native.drain_graph_steps
    have present : EventGraph.completion (serviceGraph setup mode) event (some action) value ∈
        final.application.config.history := by
      rw [drained, ← retained, recorded]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    have chosen := disclosedAt_record setup mode who final.application event owned action value
      present
    simpa only [disclosedAt, readChoice, actionEq, decodedAction, OwnAction.disclosure] using chosen

end Vegas
