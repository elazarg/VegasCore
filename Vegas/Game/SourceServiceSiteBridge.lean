/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnCompletes

/-! # The completion bridge for every scheduler

A decision on the sequentialized graph is located by its ready site: the event
whose phase it lies in, that event's readiness, and that it is the only ready
event (`Vegas.ReadySite`). No plan position, roster or calendar is involved.

After a response at a ready site, the run is stopped when the site's event
completes (`Vegas.ReadySite.completionLaw`). For every scheduler that completes
play, every player profile, and every response whose execution the players
reach from initialization, each stopping point is a completion boundary of the
next rank within the horizon (`Vegas.ReadySite.completion_boundary_of_supported`).
At a legal decision of a response menu under a fully mixed restricted
assessment every legal response is such a response
(`Vegas.ReadySite.completion_boundary`).

The readout after the response is then the configuration law at completion,
bound with the continuation from the next boundary: exactly, given exact
boundary continuations (`Vegas.ReadySite.response_completion_law`), and within
the next boundary's error, given approximate ones
(`Vegas.ReadySite.response_completion_within`). Both are the Markov property of
the round evaluator at the completion time
(`Interaction.ReactiveApplication.runToHorizon_eq_runUntilHorizon_bind`).

Every initial execution is a completion boundary of rank zero
(`Vegas.initial_completionBoundary`), so approximate boundary continuations
bound the distance of the whole initialized native readout from the source law
(`Vegas.initializedReadout_within`). For the turn-counted policy this is the
total deferral weight (`Vegas.sourceServiceTurnPolicy_initialized_lawError`),
in the per-outcome form of the initialized-law premise of the library's
sequential-equilibrium limit lemma with a vanishing law error.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The position-free datum of a decision: the event whose phase the execution
is in, that event's readiness, and that it is the only ready event. -/
structure ReadySite (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup leaks).Execution) where
  event : (graph setup).EventId
  ready : execution.application.config.cut.Ready event
  sole : execution.application.publicView.SoleReady event

/-- The complete typed source terminal law after one current response: the
players and the scheduler run to the horizon. -/
def sourceResponseReadout {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (players : Player → (application setup leaks).Policy)
    (execution : (application setup leaks).Execution) (who : Player)
    (response : (application setup leaks).Action) :
    PMF (Option (State L setup.program.terminalCtx)) :=
  ((application setup leaks).runToHorizon scheduler players horizon
    (execution.respond (application setup leaks) who response)).map
      (fun final => sourceReadout setup leaks ((application setup leaks).finished final))

namespace ReadySite

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {execution : (application setup leaks).Execution}

/-- Every ready event is the execution's ready site. -/
def ofReady {event : (graph setup).EventId}
    (ready : execution.application.config.cut.Ready event) : ReadySite setup leaks execution :=
  ⟨event, ready, soleReady_of_ready setup execution.application ready⟩

variable (site : ReadySite setup leaks execution)

/-- The execution after one current response, stopped when the site's event
completes or at the horizon. -/
def completionLaw (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (response : (application setup leaks).Action) :
    PMF (application setup leaks).Execution :=
  (application setup leaks).runUntilHorizon scheduler players
    (fun final => site.event ∈ final.application.config.cut.completed) horizon
    (execution.respond (application setup leaks) who response)

/-- The configuration law when the site's event completes. -/
def completionConfigLaw (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (response : (application setup leaks).Action) : PMF (graph setup).Config :=
  (site.completionLaw scheduler horizon players who response).map
    (fun final => final.application.config)

/-- **The completion boundary, for every scheduler.** If the players reach the
execution after a response from initialization, within the horizon, then every
point where its completion run stops lies within the horizon, has completed
exactly the events up to the site's event, and no recorded response has seen
the next event ready. -/
theorem completion_boundary_of_supported {scheduler : (application setup leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup leaks).Policy}
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (who : Player) (response : (application setup leaks).Action)
    (supported : execution.respond (application setup leaks) who response ∈
      ((application setup leaks).roundsFrom (initialLaw setup) scheduler players
        execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ (site.completionLaw scheduler horizon players who response).support) :
    stopped.environmentRecall.length ≤ horizon ∧
      CompletionBoundary setup leaks scheduler players (site.event.val + 1) stopped := by
  have ordered : (execution.respond (application setup leaks) who
      response).application.config.cut.IsPrefix site.event.val := by
    rw [((runtime setup).reactive_respond_application leaks execution who response).1]
    exact ⟨Nat.le_of_lt site.event.isLt, fun prior =>
      setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready
        execution.application.config.cut site.ready⟩
  have respondedLength : (execution.respond (application setup leaks) who
      response).environmentRecall.length = execution.environmentRecall.length :=
    congrArg List.length ((application setup leaks).respond_environmentRecall execution who
      response)
  unfold completionLaw ReactiveApplication.runUntilHorizon at reached
  generalize execution.respond (application setup leaks) who response = responded at *
  let app := application setup leaks
  have respondedSupported : responded ∈ (app.roundsFrom (initialLaw setup) scheduler players
      responded.environmentRecall.length).support := by
    rw [respondedLength]
    exact supported
  obtain ⟨rank, rankOrdered, seen⟩ := roundsFrom_ranked setup leaks scheduler players _
    responded supported
  have rankEq := isPrefix_unique rankOrdered ordered
  subst rankEq
  obtain ⟨stoppedSeen, stoppedConfig⟩ := runUntil_completion_prefix setup leaks scheduler players
    site.event _ responded stopped ordered seen reached
  have stoppedSupported := app.roundsFrom_runUntil scheduler players (initialLaw setup) _ _
    responded stopped respondedSupported reached
  obtain ⟨used, within, _, length⟩ := app.runUntil_runRounds scheduler players _ _
    responded stopped reached
  have stoppedBounded : stopped.environmentRecall.length ≤ horizon := by omega
  have finished : stopped.application.config.cut.IsPrefix (site.event.val + 1) := by
    rcases stoppedConfig with current | advanced
    · exfalso
      have unfinished : site.event ∉ stopped.application.config.cut.completed := fun member =>
        Nat.lt_irrefl _ ((current.2 site.event).mp member)
      rcases app.runUntil_stopped scheduler players _ _ responded stopped reached with
        halted | spent
      · exact unfinished halted
      · obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players _
          stoppedBounded stopped stoppedSupported
        have terminal := completes _ trace (by
          change horizon - stopped.environmentRecall.length = 0 ∧ _
          exact ⟨by omega, rfl⟩)
        change stopped.application.config.cut.completed = Finset.univ at terminal
        exact unfinished (terminal ▸ Finset.mem_univ _)
    · exact advanced
  refine ⟨stoppedBounded, stoppedSupported, finished, ?_⟩
  intro next rankNext observer entry member readyView
  have := stoppedSeen observer entry member next readyView
  omega

/-- **The completion boundary at a legal decision.** For any response menu,
scheduler, horizon and players admissible for the menu whose restriction is
a fully mixed assessment, every legal response at a legal decision stops at a
completion boundary of the next rank, within the horizon. -/
theorem completion_boundary {scheduler : (application setup leaks).Scheduler} {horizon : Nat}
    {players : Player → (application setup leaks).Policy}
    (menu : (application setup leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (initialLaw setup) horizon scheduler who (players who))
    (assessment : (menu.information (initialLaw setup) horizon scheduler).BehavioralAssessment)
    (strategy : assessment.strategy = fun who =>
      menu.restrictPolicy (initialLaw setup) horizon scheduler who (players who))
    (mixed : assessment.IsFullyMixed)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {who : Player} {remaining : Nat}
    (trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (allowed : response ∈ menu.actions who (execution.recall who)
      (execution.observe (application setup leaks) who))
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ (site.completionLaw scheduler horizon players who response).support) :
    stopped.environmentRecall.length ≤ horizon ∧
      CompletionBoundary setup leaks scheduler players (site.event.val + 1) stopped := by
  let app := application setup leaks
  have accounted := (menu.roundSupported_uniform (initialLaw setup) horizon scheduler trace).1
  change execution.environmentRecall.length + remaining = horizon at accounted
  have supported := menu.fullyMixed_response_rounds_support (initialLaw setup) horizon scheduler
    players covered assessment strategy mixed who remaining execution trace response allowed 0
    (execution.respond app who response) ((PMF.mem_support_pure_iff _ _).mpr rfl)
  rw [show (execution.respond app who response).environmentRecall.length =
      execution.environmentRecall.length from
    congrArg List.length (app.respond_environmentRecall execution who response)] at supported
  exact site.completion_boundary_of_supported completes who response supported (by omega)
    stopped reached

/-- **Completion-stopped continuation bridge, for every scheduler.** After a
response whose execution the players reach within the horizon, the complete
typed source terminal law is the source continuation from the next event
boundary, averaged over the configuration law when the site's event completes,
given source continuations from completion boundaries. -/
theorem response_completion_law {scheduler : (application setup leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup leaks).Policy}
    {profile : BehavioralProfile setup.program}
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (continuation : BoundaryContinuationLaw setup leaks scheduler horizon players profile)
    (who : Player) (response : (application setup leaks).Action)
    (supported : execution.respond (application setup leaks) who response ∈
      ((application setup leaks).roundsFrom (initialLaw setup) scheduler players
        execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    sourceResponseReadout scheduler horizon players execution who response =
      (site.completionConfigLaw scheduler horizon players who response).bind
        (sourceContinuation setup profile (site.event.val + 1)) := by
  unfold sourceResponseReadout completionConfigLaw completionLaw
  rw [(application setup leaks).runToHorizon_eq_runUntilHorizon_bind scheduler players
    (fun final => site.event ∈ final.application.config.cut.completed) horizon _,
    PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro stopped reached
  obtain ⟨stoppedBounded, boundary⟩ :=
    site.completion_boundary_of_supported completes who response supported bounded stopped
      reached
  exact continuation _ stopped boundary stoppedBounded

/-- **Approximate completion-stopped bridge, for every scheduler.** After a
response whose execution the players reach within the horizon, the complete
typed source terminal law is within the next boundary's error of the source
continuation from the next event boundary, averaged over the configuration law
when the site's event completes. -/
theorem response_completion_within {scheduler : (application setup leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup leaks).Policy}
    {profile : BehavioralProfile setup.program} {error : Nat → ℝ}
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (continuation : BoundaryContinuationWithin setup leaks scheduler horizon players profile error)
    (who : Player) (response : (application setup leaks).Action)
    (supported : execution.respond (application setup leaks) who response ∈
      ((application setup leaks).roundsFrom (initialLaw setup) scheduler players
        execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    PMF.WithinTV (error (site.event.val + 1))
      (sourceResponseReadout scheduler horizon players execution who response)
      ((site.completionConfigLaw scheduler horizon players who response).bind
        (sourceContinuation setup profile (site.event.val + 1))) := by
  unfold sourceResponseReadout completionConfigLaw completionLaw
  rw [(application setup leaks).runToHorizon_eq_runUntilHorizon_bind scheduler players
    (fun final => site.event ∈ final.application.config.cut.completed) horizon _,
    PMF.map_bind, PMF.bind_map]
  apply PMF.WithinTV.bind_right
  intro stopped reached
  obtain ⟨stoppedBounded, boundary⟩ :=
    site.completion_boundary_of_supported completes who response supported bounded stopped
      reached
  exact continuation _ stopped boundary stoppedBounded

/-- The exact bridge at a legal decision of a response menu. -/
theorem response_completion_law_of_menu {scheduler : (application setup leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup leaks).Policy}
    {profile : BehavioralProfile setup.program}
    (menu : (application setup leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (initialLaw setup) horizon scheduler who (players who))
    (assessment : (menu.information (initialLaw setup) horizon scheduler).BehavioralAssessment)
    (strategy : assessment.strategy = fun who =>
      menu.restrictPolicy (initialLaw setup) horizon scheduler who (players who))
    (mixed : assessment.IsFullyMixed)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (continuation : BoundaryContinuationLaw setup leaks scheduler horizon players profile)
    {who : Player} {remaining : Nat}
    (trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (allowed : response ∈ menu.actions who (execution.recall who)
      (execution.observe (application setup leaks) who)) :
    sourceResponseReadout scheduler horizon players execution who response =
      (site.completionConfigLaw scheduler horizon players who response).bind
        (sourceContinuation setup profile (site.event.val + 1)) := by
  unfold sourceResponseReadout completionConfigLaw
  rw [(application setup leaks).runToHorizon_eq_runUntilHorizon_bind scheduler players
    (fun final => site.event ∈ final.application.config.cut.completed) horizon _,
    PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro stopped reached
  obtain ⟨stoppedBounded, boundary⟩ := site.completion_boundary menu covered assessment strategy
    mixed completes trace response allowed stopped reached
  exact continuation _ stopped boundary stoppedBounded

/-- The approximate bridge at a legal decision of a response menu. -/
theorem response_completion_within_of_menu {scheduler : (application setup leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup leaks).Policy}
    {profile : BehavioralProfile setup.program} {error : Nat → ℝ}
    (menu : (application setup leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (initialLaw setup) horizon scheduler who (players who))
    (assessment : (menu.information (initialLaw setup) horizon scheduler).BehavioralAssessment)
    (strategy : assessment.strategy = fun who =>
      menu.restrictPolicy (initialLaw setup) horizon scheduler who (players who))
    (mixed : assessment.IsFullyMixed)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (continuation : BoundaryContinuationWithin setup leaks scheduler horizon players profile error)
    {who : Player} {remaining : Nat}
    (trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (allowed : response ∈ menu.actions who (execution.recall who)
      (execution.observe (application setup leaks) who)) :
    PMF.WithinTV (error (site.event.val + 1))
      (sourceResponseReadout scheduler horizon players execution who response)
      ((site.completionConfigLaw scheduler horizon players who response).bind
        (sourceContinuation setup profile (site.event.val + 1))) := by
  unfold sourceResponseReadout completionConfigLaw
  rw [(application setup leaks).runToHorizon_eq_runUntilHorizon_bind scheduler players
    (fun final => site.event ∈ final.application.config.cut.completed) horizon _,
    PMF.map_bind, PMF.bind_map]
  apply PMF.WithinTV.bind_right
  intro stopped reached
  obtain ⟨stoppedBounded, boundary⟩ := site.completion_boundary menu covered assessment strategy
    mixed completes trace response allowed stopped reached
  exact continuation _ stopped boundary stoppedBounded

end ReadySite

/-! ## The initialized law -/

section Initialized

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- **Rank zero.** Every initial execution is a completion boundary of rank
zero, for every scheduler and players. -/
theorem initial_completionBoundary (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (state : EventGraphRuntime.State (graph setup))
    (supported : state ∈ (initialLaw setup).support) :
    CompletionBoundary setup leaks scheduler players 0
      (ReactiveApplication.Execution.initial (application setup leaks) state) := by
  refine ⟨?_, ?_, ?_⟩
  · change _ ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler players 0).support
    simp only [ReactiveApplication.roundsFrom, ReactiveApplication.runRounds,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
    exact ⟨state, supported, rfl⟩
  · obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact EventOrder.Cut.empty_isPrefix _
  · intro event _ who entry member
    simp [ReactiveApplication.Execution.initial] at member

/-- The source continuation from the initial boundary, averaged over the
native prior, is the source law. -/
theorem initialLaw_bind_sourceContinuation (profile : BehavioralProfile setup.program) :
    (initialLaw setup).bind (fun state => sourceContinuation setup profile 0 state.config) =
      (setup.run profile).map some := by
  rw [initialLaw, serviceInitialLaw, PMF.bind_map, Setup.run, PMF.map_bind]
  congr 1
  funext initial
  simp only [Function.comp_apply, sourceContinuation, sourceServicePrefix?_initial,
    Setup.continuationLaw, ProtocolState.continuationLaw_entry]
  rfl

variable {setup leaks} [Fintype Player]

/-- **The initialized law within the initial error.** For any response menu,
scheduler and horizon, players admissible for the menu whose boundary
continuations are within `error` of the source, the native initialized typed
readout of their restriction is within `error 0` of the source law. -/
theorem initializedReadout_within {scheduler : (application setup leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup leaks).Policy}
    {profile : BehavioralProfile setup.program} {error : Nat → ℝ}
    (menu : (application setup leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (initialLaw setup) horizon scheduler who (players who))
    (within : BoundaryContinuationWithin setup leaks scheduler horizon players profile error) :
    PMF.WithinTV (error 0)
      (((menu.information (initialLaw setup) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (initialLaw setup) horizon scheduler who (players who))
        (2 * horizon + 1)).map (fun final => sourceReadout setup leaks final.state))
      ((setup.run profile).map some) := by
  let app := application setup leaks
  have physical := congrArg (PMF.map (sourceReadout setup leaks))
    (menu.run_restrict_eq_finish (initialLaw setup) horizon scheduler players covered
      (2 * horizon + 1) (menu.protocol (initialLaw setup) horizon scheduler).initHistory le_rfl)
  rw [PMF.map_comp] at physical
  rw [InformationModel.runBehavioral]
  refine (Eq.subst (motive := fun law => PMF.WithinTV (error 0) law _)
    (show _ = _ from physical.symm) ?_)
  rw [← initialLaw_bind_sourceContinuation setup profile]
  change PMF.WithinTV (error 0)
    (((initialLaw setup).bind fun state =>
      (app.runRounds scheduler players horizon
        (ReactiveApplication.Execution.initial app state)).map app.finished).map
      (sourceReadout setup leaks)) _
  rw [PMF.map_bind]
  apply PMF.WithinTV.bind_right
  intro state supported
  have close := within 0 (ReactiveApplication.Execution.initial app state)
    (initial_completionBoundary setup leaks scheduler players state supported) (Nat.zero_le _)
  rw [PMF.map_comp]
  exact close

/-- **The initialized law in the limit lemma's form.** Under the hypotheses of
`Vegas.initializedReadout_within`, every typed outcome's native probability is
within `error 0` of its probability in the source information model, for any
source profile with the same source law. -/
theorem initializedReadout_lawError {scheduler : (application setup leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup leaks).Policy}
    {profile : BehavioralProfile setup.program} {error : Nat → ℝ}
    (menu : (application setup leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (initialLaw setup) horizon scheduler who (players who))
    (within : BoundaryContinuationWithin setup leaks scheduler horizon players profile error)
    (admission : CommitmentInterface setup.program)
    (source : Profile (setup.informationModel admission).behavioralSignature)
    (sameRun : setup.run profile = setup.run (setup.decodeBehavioralProfile admission source))
    (outcome : Option (State L setup.program.terminalCtx)) :
    |((((menu.information (initialLaw setup) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (initialLaw setup) horizon scheduler who (players who))
        (2 * horizon + 1)).map (fun final => sourceReadout setup leaks final.state))
          outcome).toReal -
      ((((setup.informationModel admission).runBehavioral source
        (instructionCount setup.program + 1)).map
          (fun final => setup.protocolReadout final.state)) outcome).toReal| ≤ error 0 := by
  have sourceLaw : ((setup.informationModel admission).runBehavioral source
      (instructionCount setup.program + 1)).map (fun final => setup.protocolReadout final.state) =
        (setup.run profile).map some := by
    rw [sameRun]
    exact setup.runBehavioralFrom_readout admission source (instructionCount setup.program + 1)
      (setup.executionProtocol admission).initHistory (Nat.le_refl _)
  rw [sourceLaw]
  exact (initializedReadout_within menu covered within).apply outcome

/-- **The turn-counted policy's initialized law error.** Under the asynchronous
contract with `delay + bound < deadline`, for players admissible for a
response menu that follow the turn-counted policy of a source profile with
effective disclosures, every typed outcome's native probability is within the
total deferral weight of its source probability. -/
theorem sourceServiceTurnPolicy_initialized_lawError
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (menu : (application setup leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (initialLaw setup) horizon scheduler who
      (sourceServiceTurnPolicy setup leaks bound turns timing profile who))
    (admission : CommitmentInterface setup.program)
    (source : Profile (setup.informationModel admission).behavioralSignature)
    (sameRun : setup.run profile = setup.run (setup.decodeBehavioralProfile admission source))
    (outcome : Option (State L setup.program.terminalCtx)) :
    |((((menu.information (initialLaw setup) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (initialLaw setup) horizon scheduler who
          (sourceServiceTurnPolicy setup leaks bound turns timing profile who))
        (2 * horizon + 1)).map (fun final => sourceReadout setup leaks final.state))
          outcome).toReal -
      ((((setup.informationModel admission).runBehavioral source
        (instructionCount setup.program + 1)).map
          (fun final => setup.protocolReadout final.state)) outcome).toReal| ≤
      ∑ event, timing.deferral event := by
  have bound := initializedReadout_lawError menu covered
    (sourceServiceTurnPolicy_boundaryContinuationWithin
      (sourceServiceTurnPolicy_firstTurnCompletes contract timely timing profile effective))
    admission source sameRun outcome
  have all : Finset.univ.filter (fun event : (graph setup).EventId => 0 ≤ event.val) =
      Finset.univ :=
    Finset.filter_true_of_mem fun event _ => Nat.zero_le event.val
  simpa only [all] using bound

end Initialized

end Vegas
