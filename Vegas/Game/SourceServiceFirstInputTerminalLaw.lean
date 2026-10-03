/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstInputReadoutPosterior
import Vegas.Game.SourceServicePastPrefix
import Vegas.Game.AsyncServiceFirstInputPassage

/-! # The actual terminal source ancestor and first input jointly

The retrospective prefix reads only completed lower ranks. Its common original
memory restoration and persistent initial parameter therefore remain the same
after the real first-response stop. The terminal chronological input retains
that same stopped input through all later traffic and actions.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Restore the original source position before a fixed rank from a later
physical configuration, using one all-owner lottery and its persistent initial
draw. Completions at and after the rank do not enter this source history. -/
def sourceServicePastRestoredPrefixReadout {Parameter : Type}
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter) (rank : Nat)
    (config : (graph setup).Config) : PMF (Option (Parameter × ProtocolState setup.program)) :=
  match sourceInitialReadout setup config, sourceServicePastPrefix? setup rank config with
  | some initial, some before =>
      (profile.restoreDisclosureMemory setup.program [] (Revelations.initial setup.context)
        before).map fun original => some (parameter initial, original)
  | _, _ => PMF.pure none

omit [Fintype Player] in
private theorem initialReadout_congr
    (left right : (graph setup).Config) (inputs : left.inputs = right.inputs) :
    sourceInitialReadout setup left = sourceInitialReadout setup right := by
  have reads {Γ : SourceCtx Player L}
      (refs : ContextRefs (EventGraph.fieldLayout (graph setup).inputLayout
        (graph setup).outputLayout) Γ)
      (same : ∀ {name cell} (source : HasVar Γ name cell),
        (refs.get source).get? left.store = (refs.get source).get? right.store) :
      decodeState? refs left.store = decodeState? refs right.store := by
    induction Γ with
    | nil => rfl
    | cons entry Γ ih =>
        obtain ⟨name, cell⟩ := entry
        have head := same (HasVar.here : HasVar ((name, cell) :: Γ) name cell)
        have tail := ih refs.tail (fun source => same (.there source))
        cases cell <;> simp only [decodeState?, head, tail]
  apply reads
  intro name cell source
  apply ((ContextRefs.initial setup.context (outputLayout setup.program)).get source).get?_congr
  change some (left.inputs (inputId source)) = some (right.inputs (inputId source))
  rw [inputs]

omit [Fintype Player] in
private theorem inputsInvariant (seed : (graph setup).Inputs) :
    (application setup leaks).Invariant (fun state => state.config.inputs = seed) := by
  have step (config next : (graph setup).Config) (same : config.inputs = seed)
      (event : (graph setup).EventId) (ready : config.cut.Ready event)
      (action : (graph setup).Action event)
      (supported : next ∈ (config.step event ready action).support) : next.inputs = seed := by
    rw [EventGraph.Config.step, PMF.support_map] at supported
    obtain ⟨value, _selected, rfl⟩ := supported
    exact same
  refine ⟨?_, ?_, ?_⟩
  · intro state who material same
    change (submitStep (material.call.register state who)
      who material.call.packet).config.inputs = _
    rw [submitStep_config, (material.call.register_facts who state).1]
    exact same
  · intro state message next same accepted
    obtain ⟨event, _, ready, action, supported⟩ := handle_config_mem_step (runtime setup) state next
      ⟨message.id, message.payload.call⟩ (reactiveHandle_call accepted)
    exact step state.config next.config same event ready action supported
  · intro state command next same supported
    cases command with
    | advanceClock =>
        change next ∈ (environmentStep (runtime setup) state .advanceClock).support at supported
        simp only [environmentStep, PMF.mem_support_pure_iff _ _] at supported
        subst next
        exact same
    | executeSample event =>
        obtain ⟨_, unchanged | moved⟩ := environmentStep_executeSample_config_activated
          (runtime setup) state next event supported
        · rw [unchanged.1]
          exact same
        · obtain ⟨ready, action, reached, _⟩ := moved
          exact step state.config next.config same event ready action reached
    | expire event =>
        obtain ⟨_, unchanged | moved⟩ := environmentStep_expire_config_activated
          (runtime setup) state next event supported
        · rw [unchanged.1]
          exact same
        · obtain ⟨ready, action, reached, _⟩ := moved
          exact step state.config next.config same event ready action reached

omit [Fintype Player] in
private theorem initialReadout_runRounds
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (count : Nat)
    (before after : (application setup leaks).Execution)
    (supported : after ∈ ((application setup leaks).runRounds scheduler players count
      before).support) :
    sourceInitialReadout setup after.application.config =
      sourceInitialReadout setup before.application.config := by
  have same := (ReactiveApplication.Invariant.policyInvariant (application setup leaks)
    (inputsInvariant before.application.config.inputs) players).runRounds
      scheduler count before after rfl supported
  exact initialReadout_congr _ _ same

/-- Every continuation after a prefix cut reads the same earlier source
position and initialization, with the same common original-memory kernel. -/
theorem sourceServicePastRestoredPrefixReadout_runRounds {Parameter : Type}
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter) (rank : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (count : Nat)
    (before after : (application setup leaks).Execution)
    (ordered : before.application.config.cut.IsPrefix rank)
    (supported : after ∈ ((application setup leaks).runRounds scheduler players count
      before).support) :
    sourceServicePastRestoredPrefixReadout profile parameter rank after.application.config =
      sourceServiceRestoredPrefixReadout profile parameter rank before.application.config := by
  unfold sourceServicePastRestoredPrefixReadout sourceServiceRestoredPrefixReadout
  rw [initialReadout_runRounds scheduler players count before after supported,
    sourceServicePastPrefix?_runRounds setup leaks rank before after ordered scheduler players
      count supported]
  rfl

/-- The actual physical terminal retrospective readout and earliest owned
input have exactly the joint law of the real first-input stopped readout. -/
theorem sourceServiceFirstTurn_terminal_joint_readout {Parameter : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter)
    (who : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some who) :
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) profile
    let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
      normalized
    let rank := fun initial => (application setup leaks).runUntilHorizon scheduler players
      (sourceServiceRankCompleted event.val) horizon
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))
    let first := fun execution => (application setup leaks).runUntilHorizon scheduler players
      (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none)
      horizon execution
    (((application setup leaks).roundsFrom (initialLaw setup) scheduler players horizon).bind
      fun final => (sourceServicePastRestoredPrefixReadout profile parameter event.val
        final.application.config).map fun restored =>
          (restored, sourceServiceFirstInput? setup leaks who event (final.recall who))) =
    setup.initialLaw.bind fun initial => (rank initial).bind fun execution =>
      (first execution).bind fun stopped =>
        (sourceServiceRestoredPrefixReadout profile parameter event.val
          stopped.application.config).map fun restored =>
            (restored, sourceServiceTurnInput? setup leaks who event (stopped.recall who)) := by
  classical
  intro normalized players rank first
  let app := application setup leaks
  let start := fun initial : State L setup.context =>
    ReactiveApplication.Execution.initial app
      (EventGraphRuntime.State.initial (setup.eventInputs initial))
  have effective (owner : Player) : (normalized owner).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
    (profile owner).normalizeDisclosureFrom_effective setup.program []
      (Revelations.initial setup.context) (fun view => PMF.pure view.2)
  change _ = _
  have initialized : app.roundsFrom (initialLaw setup) scheduler players horizon =
      setup.initialLaw.bind (fun initial => app.runToHorizon scheduler players horizon
        (start initial)) := by
    simp only [ReactiveApplication.roundsFrom, initialLaw, PMF.bind_map,
      ReactiveApplication.runToHorizon, start, ReactiveApplication.Execution.initial,
      List.length_nil, Nat.sub_zero, Function.comp_def]
  rw [initialized, PMF.bind_bind]
  apply bind_congr_on_support setup.initialLaw
  intro initial initialSupport
  rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players
    (sourceServiceRankCompleted event.val), PMF.bind_bind]
  apply bind_congr_on_support (rank initial)
  intro execution actual
  obtain ⟨bounded, boundary⟩ :=
    (sourceServiceFirstTurn_rank_law (turns := turns) contract timely normalized effective initial
      initialSupport event.val (Nat.le_of_lt event.isLt)).1 execution actual
  rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players
    (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none),
    PMF.bind_bind]
  apply bind_congr_on_support (first execution)
  intro stopped reached
  have configEq := sourceServiceFirstActivation_config contract timely players who normalized rfl
    event owned execution boundary bounded stopped reached
  have ordered : stopped.application.config.cut.IsPrefix event.val := by
    rw [configEq]
    exact boundary.ordered
  obtain ⟨middle, response, _actual, _configEq, firstTurn, _fits, _chosen, after, inputEq⟩ :=
    sourceServiceFirstActivation_input contract timely players who turns normalized rfl event
      owned execution boundary bounded stopped reached
  have absent : sourceServiceTurnInput? setup leaks who event (middle.recall who) = none := by
    apply (sourceServiceTurnInput?_eq_none_iff who event _).mpr
    unfold sourceServiceTurn at firstTurn
    split at firstTurn
    · have zero := Option.some.inj firstTurn
      intro entry member named
      have excluded := List.countP_eq_zero.mp zero entry member
      exact excluded (decide_eq_true named)
    · cases firstTurn
  have turn : middle.application.publicView.ownTurn? who = some event := by
    unfold sourceServiceTurn at firstTurn
    split at firstTurn
    · assumption
    · cases firstTurn
  have present : sourceServiceFirstInput? setup leaks who event (stopped.recall who) =
      sourceServiceTurnInput? setup leaks who event (stopped.recall who) := by
    rw [inputEq, after]
    exact sourceServiceFirstInput?_first_response who event middle absent turn response
  have inputLaw := sourceServiceFirstInput?_runToHorizon who event scheduler players horizon
    stopped _ present (by rw [inputEq]; exact Option.some_ne_none _)
  calc
    _ = (app.runToHorizon scheduler players horizon stopped).bind (fun final =>
        (sourceServiceRestoredPrefixReadout profile parameter event.val
          stopped.application.config).map fun restored =>
            (restored, sourceServiceFirstInput? setup leaks who event (final.recall who))) := by
      apply bind_congr_on_support _
      intro final supported
      rw [sourceServicePastRestoredPrefixReadout_runRounds profile parameter event.val scheduler
        players _ stopped final ordered supported]
    _ = _ := by
      change (app.runToHorizon scheduler players horizon stopped).bind (fun final =>
        (sourceServiceRestoredPrefixReadout profile parameter event.val
          stopped.application.config).bind fun restored => PMF.pure
            (restored, sourceServiceFirstInput? setup leaks who event (final.recall who))) = _
      rw [PMF.bind_comm]
      apply bind_congr_on_support _
      intro restored _possible
      calc
        _ = ((app.runToHorizon scheduler players horizon stopped).map
            fun final => sourceServiceFirstInput? setup leaks who event (final.recall who)).map
              (fun input => (restored, input)) := (PMF.map_comp ..).symm
        _ = _ := by rw [inputLaw, PMF.pure_map]; rfl

omit [Fintype Player] in
private theorem initialReadout_reaches
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    {first last : ((application setup leaks).protocol initial horizon scheduler).History}
    {fuel : Nat}
    (path : ((application setup leaks).protocol initial horizon scheduler).ReachesWithin fuel
      first last)
    (before after : (application setup leaks).Control)
    (firstEq : first.state = some before) (lastEq : last.state = some after) :
    sourceInitialReadout setup after.execution.application.config =
      sourceInitialReadout setup before.execution.application.config := by
  have inputs : after.execution.application.config.inputs =
      before.execution.application.config.inputs := by
    let app := application setup leaks
    induction path generalizing before with
    | refl _ history =>
        cases Option.some.inj (firstEq.symm.trans lastEq)
        rfl
    | @step steps history target joint legal reached supported suffix ih =>
        have moved := supported
        change reached ∈ (app.transition initial horizon scheduler history.state joint).support
          at moved
        rw [firstEq] at moved
        obtain ⟨middle, middleEq, _⟩ := app.transition_recall_prefix initial horizon scheduler
          before reached joint moved
        have invariant := inputsInvariant (leaks := leaks)
          before.execution.application.config.inputs
        have good := invariant.transition (PMF.pure before.execution.application) horizon scheduler
          (by
            intro state member
            cases (PMF.mem_support_pure_iff _ _).mp member
            rfl)
          (some before) reached joint rfl moved
        rw [middleEq] at good
        exact (ih middle middleEq lastEq).trans good
  exact initialReadout_congr _ _ inputs

/-- Every actual descendant of an owned prefix uses the same earlier source
restoration kernel and the same initial draw as the before-response ancestor. -/
theorem sourceServicePastRestoredPrefixReadout_reaches {Parameter : Type}
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter) (rank : Nat)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    {first last : ((application setup leaks).protocol initial horizon scheduler).History}
    {fuel : Nat}
    (path : ((application setup leaks).protocol initial horizon scheduler).ReachesWithin fuel
      first last)
    (before after : (application setup leaks).Control)
    (firstEq : first.state = some before) (lastEq : last.state = some after)
    (ordered : before.execution.application.config.cut.IsPrefix rank) :
    sourceServicePastRestoredPrefixReadout profile parameter rank
        after.execution.application.config =
      sourceServiceRestoredPrefixReadout profile parameter rank
        before.execution.application.config := by
  have same := sourceServicePastPrefix_reaches setup leaks initial horizon scheduler rank path
    before after firstEq lastEq (fun event preceding => (ordered.2 event).mpr preceding)
  unfold sourceServicePastRestoredPrefixReadout sourceServiceRestoredPrefixReadout
  rw [initialReadout_reaches initial horizon scheduler path before after firstEq lastEq, same.2,
    sourceServicePastPrefix?_eq_at_prefix setup rank _ ordered]
  rfl

end Vegas

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

/-- The represented normalized first-turn native terminal law retains the
same restored before-event source position and initial parameter jointly with
its actual first input. The source restoration is an auxiliary readout. -/
theorem normalizedFirstTurnProfile_first_input_joint_readout {Parameter : Type} (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (parameter : State L service.setup.context → Parameter)
    (who : Player) (event : (graph service.setup).EventId)
    (owned : (graph service.setup).actor? event = some who) :
    let normalized := normalizeDisclosureProfile service.setup.program []
      (Revelations.initial service.setup.context) profile
    let players := sourceServiceTurnPolicy service.setup service.leaks service.bound turns
      (firstTurnTiming service.setup turns) normalized
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let model := menu.information (initialLaw service.setup) service.horizon service.scheduler
    let certificate := (menu.bounded (initialLaw service.setup) service.horizon
      service.scheduler).wellFoundedHistories
    let readout := fun state : (application service.setup service.leaks).ProtocolState =>
      match state with
      | none => PMF.pure (none, none)
      | some control => (sourceServicePastRestoredPrefixReadout profile parameter event.val
          control.execution.application.config).map fun restored =>
            (restored, sourceServiceFirstInput? service.setup service.leaks who event
              (control.execution.recall who))
    ((model.runBehavioralTerminalFrom certificate (service.firstTurnProfile turns normalized)
      (menu.protocol (initialLaw service.setup) service.horizon service.scheduler).initHistory).bind
        fun final => readout final.state) =
      service.setup.initialLaw.bind fun initial =>
        ((application service.setup service.leaks).runUntilHorizon service.scheduler players
          (sourceServiceRankCompleted event.val) service.horizon
          (.initial (application service.setup service.leaks)
            (EventGraphRuntime.State.initial (service.setup.eventInputs initial)))).bind
              fun execution =>
                ((application service.setup service.leaks).runUntilHorizon service.scheduler
                  players (fun final => sourceServiceTurnInput? service.setup service.leaks
                    who event (final.recall who) ≠ none) service.horizon execution).bind
                      fun stopped =>
                        (sourceServiceRestoredPrefixReadout profile parameter event.val
                          stopped.application.config).map fun restored =>
                            (restored, sourceServiceTurnInput? service.setup service.leaks who
                              event (stopped.recall who)) := by
  classical
  intro normalized players menu model certificate readout
  have admitted (owner : Player) : (normalized owner).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program) :=
    (profile owner).normalizeDisclosureFrom_admitted service.setup.program
      (CommitmentInterface.values service.setup.program) (permitted owner) []
      (Revelations.initial service.setup.context) (fun view => PMF.pure view.2)
  have represented := congrArg (fun law => law.bind readout)
    (service.firstTurnProfile_initialized_control_law turns normalized admitted)
  simp only [PMF.bind_map, readout] at represented
  exact represented.trans (sourceServiceFirstTurn_terminal_joint_readout service.contract
    service.timely profile parameter who event owned)

end Vegas.AsyncServiceSpec
