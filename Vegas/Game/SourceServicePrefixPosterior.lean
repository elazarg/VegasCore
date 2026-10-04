/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefixFactorization
import Vegas.Game.SourceServicePosterior
import Vegas.Pending.ReactiveOwnerWindow
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # Actual full-source owner posteriors

The initialized timed compiler's joint prefix law is propagated through the
real turn, an arbitrary unsettled roster and passive owner activation. The
complete native input then conditions the same normalized source-state prior.
The normalized prior retains the existing private-intention reconstruction;
it is not identified with an original source assessment.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem owner_window_factorization
    {Seed Source View : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (prior : PMF Seed) (source : Seed → Source)
    (observe : Source → View) (execution : Seed → (application setup leaks).Execution)
    (recalled : ∀ seed ∈ prior.support, (execution seed).InputRecall (application setup leaks))
    (noise : View → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks owner (execution seed))) =
      (prior.map source).bind fun state =>
        (noise (observe state)).map fun extra => (state, extra))
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (policy : (application setup leaks).Policy) :
    ∃ nextNoise : View → PMF _,
      (prior.bind fun seed =>
        ((runtime setup).runInteractionPlan leaks
          (Function.update (fun _ => (application setup leaks).replayPolicy) owner policy)
          network (visits.map ServiceInstruction.player) (execution seed)).map fun final =>
            (source seed, (runtime setup).bindingTraffic leaks owner final)) =
      (prior.map source).bind fun state =>
        (nextNoise (observe state)).map fun extra => (state, extra) := by
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks owner (execution seed))
    observe noise factor (fun _ => PMF.pure Unit.unit) (fun state _ => state) observe
    (fun seed _ => ((runtime setup).runInteractionPlan leaks
      (Function.update (fun _ => (application setup leaks).replayPolicy) owner policy)
      network (visits.map ServiceInstruction.player) (execution seed)).map
        ((runtime setup).bindingTraffic leaks owner))
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right rightSupport _ _ _ same =>
      (runtime setup).owner_window_focal_law leaks network visits owner policy
        (execution left) (execution right) (recalled left leftSupport)
        (recalled right rightSupport) same)
  exact ⟨nextNoise, by simpa only [PMF.pure_bind, PMF.pure_map,
    PMF.bind_pure, PMF.map_id, PMF.map_comp, Function.comp_def] using law⟩

/-- Every supported timed prefix is an actual semantic source checkpoint.
Legality at all native histories transfers support to the retained finite game. -/
theorem sourceService_timed_prefix_checkpoint [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who))
    (count : Nat)
    (within : count ≤ eventCount setup.program)
    (execution : (application setup leaks).Execution)
    (supported : execution ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support) :
    ∃ state, SourcePrefixCheckpoint setup setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) []
      (Revelations.initial setup.context) (outputRef setup.program) 0 count state
        execution.application.config := by
  let menu := sourceServiceMenu setup leaks bounds rosters
  have retained := roster_restrict_prefix_support setup leaks rosters network menu players
    covered count execution supported
  obtain ⟨_, _, state, checkpoint, _⟩ := initialized_sourceService_prefix_support setup leaks
    bounds values capacity rosters opportunities menu.uniformResponses
    (fun who past view response member =>
      (menu.uniformResponses_support who past view response).mp member)
    network (failureProfile setup.program) count within execution retained
  exact ⟨state, checkpoint⟩

/-- At every owner visit before protected inclusion, the actual complete
native input is an auxiliary channel of the normalized source observation.
The channel is derived from the initialized compiler, not assumed. -/
theorem sourceService_owner_information_law [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (full : ∀ event who owned, FullSupport (timing event who owned))
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) (visits : List Player) :
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) original
    let admission := CommitmentInterface.values setup.program
    let encoded := fun who => setup.toProtocolBehavioralPolicy admission who
      (normalized who) (normalized_sourceService_admitted setup original permitted who)
    let players := sourceServiceTimedPolicy setup leaks rosters timing normalized
    let executions := ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters event.val ++
          visits.map ServiceInstruction.player)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
      fun before => before.environmentStep (application setup leaks) (.activate owner)
    ∃ channel : setup.ProtocolView owner → PMF
        (List (application setup leaks).PlayerEntry × (application setup leaks).PlayerView),
      executions.map (fun final =>
        (sourceServicePrefix? setup event.val final.application.config,
          (final.recall owner, final.observe (application setup leaks) owner))) =
      (((setup.informationModel admission).runBehavioral encoded (event.val + 1)).map
        GameTheory.Protocol.ExecutionProtocol.History.state).bind fun state =>
          (channel (setup.protocolObserve owner state)).map fun input => (state, input) := by
  intro normalized admission encoded players executions
  let app := application setup leaks
  let prefixLaw := (initialLaw setup).bind fun state =>
    (runtime setup).runInteractionPlan leaks players network
      (rosterPlanPrefix setup rosters event.val) (ReactiveApplication.Execution.initial app state)
  let read := fun execution : app.Execution =>
    sourceServicePrefix? setup event.val execution.application.config
  let prior := ((setup.informationModel admission).runBehavioral encoded (event.val + 1)).map
    GameTheory.Protocol.ExecutionProtocol.History.state
  obtain ⟨noise, factor⟩ := sourceServiceTimedProfile_prefix_factorization setup leaks bounds values
    initialValues capacity rosters opportunities timing full network original permitted owner
      event.val event.isLt.le
  change prefixLaw.map (fun execution =>
    (read execution, (runtime setup).bindingTraffic leaks owner execution)) =
      prior.bind (fun state => (noise (setup.protocolObserve owner state)).map
        fun extra => (state, extra)) at factor
  have marginal : prefixLaw.map read = prior := by
    have result := congrArg (PMF.map Prod.fst) factor
    simpa only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
      PMF.bind_const, PMF.bind_pure] using result
  have recalls (execution : app.Execution) (supported : execution ∈ prefixLaw.support) :
      execution.InputRecall app := by
    obtain ⟨initial, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    exact (runtime setup).runInteractionPlan_inputRecall leaks players network
      (rosterPlanPrefix setup rosters event.val) (ReactiveApplication.Execution.initial app initial)
        execution (app.initial_inputRecall initial) reached
  have prefixFactor : prefixLaw.map (fun execution =>
      (read execution, (runtime setup).bindingTraffic leaks owner execution)) =
        (prefixLaw.map read).bind (fun state =>
          (noise (setup.protocolObserve owner state)).map fun extra => (state, extra)) := by
    rw [marginal]
    exact factor
  let policy := (app.policyMixture (timing event owner owned)
    (sourceServiceTimedFamily setup leaks rosters normalized owner event)).policy
  obtain ⟨windowNoise, windowFactor⟩ := owner_window_factorization setup leaks owner prefixLaw
    read (setup.protocolObserve owner) (fun execution => execution) recalls noise
      prefixFactor network visits policy
  let window := prefixLaw.bind fun execution =>
    (runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) execution
  have windowLaw (execution : app.Execution) (supported : execution ∈ prefixLaw.support) :
      (runtime setup).runInteractionPlan leaks players network
          (visits.map ServiceInstruction.player) execution =
        (runtime setup).runInteractionPlan leaks
          (Function.update (fun _ => app.replayPolicy) owner policy) network
          (visits.map ServiceInstruction.player) execution := by
    exact sourceServiceTimedPolicy_window_eq setup leaks rosters timing normalized event owner
      owned network visits execution
      (soleReady_of_ready setup execution.application
        (sourceService_prefix_ready setup leaks bounds values capacity rosters opportunities
          network players (sourceServiceTimedPolicy_admissible setup leaks bounds values
            initialValues capacity rosters opportunities network timing full normalized
            (normalized_sourceService_admitted setup original permitted))
          event execution supported))
  have kept (execution final : app.Execution)
      (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) execution).support) : read final = read execution :=
    congrArg (sourceServicePrefix? setup event.val)
      ((runtime setup).player_window_application leaks players network visits
        execution final reached).1
  have windowFactor' : window.map (fun execution =>
      (read execution, (runtime setup).bindingTraffic leaks owner execution)) =
        prior.bind (fun state =>
          (windowNoise (setup.protocolObserve owner state)).map fun extra => (state, extra)) := by
    rw [marginal] at windowFactor
    refine Eq.trans ?_ windowFactor
    simp only [window, PMF.map_bind]
    apply bind_congr_on_support _
    intro execution supported
    rw [← windowLaw execution supported]
    apply map_congr_on_support _
    intro final reached
    exact Prod.ext (kept execution final reached) rfl
  have windowMarginal : window.map read = prior := by
    have result := congrArg (PMF.map Prod.fst) windowFactor'
    simpa only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
      PMF.bind_const, PMF.bind_pure] using result
  obtain ⟨channel, inputFactor⟩ := source_activation_input_factorization setup leaks owner
    window read (setup.protocolObserve owner) (fun execution => execution) windowNoise
      (by rw [windowMarginal]; exact windowFactor')
  refine ⟨channel, ?_⟩
  have executionsEq : executions = window.bind fun before =>
      before.environmentStep app (.activate owner) := by
    simp only [executions, window, prefixLaw, runInteractionPlan_append, PMF.bind_bind]
    rfl
  rw [executionsEq, PMF.map_bind]
  rw [windowMarginal] at inputFactor
  refine Eq.trans ?_ inputFactor
  apply bind_congr_on_support _
  intro execution _
  simp only [ReactiveApplication.Execution.activation_samples, PMF.map_comp]
  rfl

private theorem window_config
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (visits : List Player) (owner : Player)
    (execution final : (application setup leaks).Execution)
    (reached : final ∈ (((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) execution).bind
        fun before => before.environmentStep (application setup leaks) (.activate owner)).support) :
    final.application.config = execution.application.config := by
  rw [PMF.support_bind] at reached
  obtain ⟨before, beforeSupport, active⟩ := Set.mem_iUnion₂.mp reached
  rw [ReactiveApplication.Execution.activation_samples, PMF.support_map] at active
  obtain ⟨sample, _, rfl⟩ := active
  exact ((runtime setup).player_window_application leaks players network visits
    execution before beforeSupport).1

/-- A supported pending decision retains the source checkpoint at phase
entry, even after arbitrary private registrations and replay responses. -/
theorem sourceService_owner_checkpoint [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who))
    (event : (graph setup).EventId) (owner : Player) (visits : List Player)
    (final : (application setup leaks).Execution)
    (reached : final ∈ (((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters event.val ++
          visits.map ServiceInstruction.player)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
      fun before => before.environmentStep (application setup leaks) (.activate owner)).support) :
    ∃ state, SourcePrefixCheckpoint setup setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) []
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state
        final.application.config := by
  let prefixLaw := (initialLaw setup).bind fun state =>
    (runtime setup).runInteractionPlan leaks players network
      (rosterPlanPrefix setup rosters event.val)
      (ReactiveApplication.Execution.initial (application setup leaks) state)
  have combined : final ∈ (prefixLaw.bind fun execution =>
      ((runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) execution).bind
          fun before => before.environmentStep
            (application setup leaks) (.activate owner)).support :=
    by simpa only [prefixLaw, runInteractionPlan_append, PMF.bind_bind] using reached
  rw [PMF.support_bind] at combined
  obtain ⟨before, beforeSupport, tailSupport⟩ := Set.mem_iUnion₂.mp combined
  obtain ⟨state, checkpoint⟩ := sourceService_timed_prefix_checkpoint setup leaks bounds values
    capacity rosters opportunities network players covered event.val event.isLt.le
      before beforeSupport
  have unchanged := window_config setup leaks players network visits owner
    before final tailSupport
  exact ⟨state, unchanged ▸ checkpoint⟩

/-- Conditioning the actual full native owner input recovers the normalized
source-state posterior at the same source instruction. This holds at any visit
in the unsettled phase, including after the owner's earlier private choices. -/
theorem sourceService_owner_posterior [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (full : ∀ event who owned, FullSupport (timing event who owned))
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) (visits : List Player)
    (reference : (application setup leaks).Execution) :
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) original
    let admission := CommitmentInterface.values setup.program
    let encoded := fun who => setup.toProtocolBehavioralPolicy admission who
      (normalized who) (normalized_sourceService_admitted setup original permitted who)
    let players := sourceServiceTimedPolicy setup leaks rosters timing normalized
    let executions := ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters event.val ++
          visits.map ServiceInstruction.player)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
      fun before => before.environmentStep (application setup leaks) (.activate owner)
    reference ∈ executions.support →
      (fiberPosterior executions (fun execution =>
          (execution.recall owner, execution.observe (application setup leaks) owner))
        (reference.recall owner, reference.observe (application setup leaks) owner)).map
          (fun execution => sourceServicePrefix? setup event.val execution.application.config) =
        (fiberPosterior
            (((setup.informationModel admission).runBehavioral encoded (event.val + 1)).map
          GameTheory.Protocol.ExecutionProtocol.History.state)
            (setup.protocolObserve owner) (setup.protocolObserve owner
              (sourceServicePrefix? setup event.val reference.application.config))) := by
  intro normalized admission encoded players executions referenceSupport
  have admitted := normalized_sourceService_admitted setup original permitted
  have covered := sourceServiceTimedPolicy_admissible setup leaks bounds values initialValues
    capacity rosters opportunities network timing full normalized admitted
  obtain ⟨channel, factor⟩ := sourceService_owner_information_law setup leaks bounds values
    initialValues capacity rosters opportunities timing full network original permitted
      event owner owned visits
  apply sourceService_state_posterior setup leaks event.val owner executions ?_
    _ channel factor reference referenceSupport
  intro final reached
  exact sourceService_owner_checkpoint setup leaks bounds values capacity rosters opportunities
    network players covered event owner visits final reached

end Vegas
