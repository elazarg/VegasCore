/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterOwnerNoise
import Vegas.Game.ServiceRosterEvaluation
import GameTheoryExtensions.Math.Probability.ObservationRetraction

/-! # Initialized owner information inside a revelation phase

The conditional channel is derived from the actual initialized program, its
retained finite protocol and passive sampling. Earlier private transcripts,
early own openings and later same-envelope replays remain in native information.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
theorem roster_compiled_prefix_checkpoint [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (count : Nat) (within : count ≤ eventCount setup.program)
    (execution : (application setup leaks).Execution)
    (supported : execution ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing
        (setup.decodeBehavioralProfile admission source.strategy)) network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support) :
    ∃ initial ∈ setup.initialLaw.support, ∃ state,
      PublicPrefixCheckpoint setup leaks initial setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) (outputRef setup.program)
        0 count state execution ∧
      sourcePrefix? setup count execution.application.config = some state := by
  classical
  let := Fintype.ofFinite Player
  let extended := bounds.withInitialValues (initialLaw setup)
  let menu := rosterMenu setup leaks extended rosters
  have legal := roster_restrict_prefix_support setup leaks rosters network menu _
    (rosterPolicy_admissible setup leaks bounds rosters network reveals openable
      admission source mixed timing timingFull) count execution supported
  obtain ⟨initial, initialSupport, state, related, readout, _⟩ :=
    initialized_roster_prefix_support setup leaks extended rosters network reveals openable
      menu.uniformResponses (fun who past view response member =>
        (menu.uniformResponses_support who past view response).mp member)
      count within execution legal
  exact ⟨initial, initialSupport, state, related, readout⟩

theorem roster_owner_information_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) (visits : List Player) :
    ∃ channel : setup.ProtocolView owner → PMF
        (List (application setup leaks).PlayerEntry × (application setup leaks).PlayerView),
      let players := rosterPolicy setup leaks rosters timing
        (setup.decodeBehavioralProfile admission source.strategy)
      let executions := (initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks players network
          (rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
            visits.map ServiceInstruction.player)
          (ReactiveApplication.Execution.initial (application setup leaks) state)
      (executions.bind fun current =>
        current.environmentStep (application setup leaks) (.activate owner)).map (fun final =>
          (sourcePrefix? setup event.val final.application.config,
            (final.recall owner, final.observe (application setup leaks) owner))) =
      (((setup.informationModel admission).runBehavioral source.strategy (event.val + 1)).map
        ExecutionProtocol.History.state).bind fun state =>
          (channel (setup.protocolObserve owner state)).map fun input => (state, input) := by
  let app := application setup leaks
  let decoded := setup.decodeBehavioralProfile admission source.strategy
  let players := rosterPolicy setup leaks rosters timing decoded
  let prior := (initialLaw setup).bind fun state =>
    (runtime setup).runInteractionPlan leaks players network
      (rosterPlanPrefix setup rosters event.val) (ReactiveApplication.Execution.initial app state)
  have checkpoint (execution : app.Execution) (supported : execution ∈ prior.support) :
      ∃ initial ∈ setup.initialLaw.support, ∃ state,
        PublicPrefixCheckpoint setup leaks initial setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program))
          (Revelations.initial setup.context) (outputRef setup.program)
          0 event.val state execution ∧
        sourcePrefix? setup event.val execution.application.config = some state := by
    exact roster_compiled_prefix_checkpoint setup leaks bounds rosters network reveals openable
      admission source mixed timing timingFull event.val event.isLt.le execution supported
  have counts (execution : app.Execution) (supported : execution ∈ prior.support) :
      (execution.recall owner).length = rosterOffset setup rosters owner event := by
    obtain ⟨initial, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    simpa only [ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add] using
      roster_prefix_response_counts setup leaks rosters network players event
        (ReactiveApplication.Execution.initial app initial) execution reached owner
  have recalls (execution : app.Execution) (supported : execution ∈ prior.support) :
      execution.InputRecall app := by
    obtain ⟨initial, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    exact (runtime setup).runInteractionPlan_inputRecall leaks players network
      (rosterPlanPrefix setup rosters event.val) (ReactiveApplication.Execution.initial app initial)
        execution (app.initial_inputRecall initial) reached
  obtain ⟨previousGrant, fixedGrant⟩ := roster_prefix_serviceGrant setup leaks rosters players
    network event.val event.isLt.le
  have previous (execution : app.Execution) (supported : execution ∈ prior.support) :
      execution.application.serviceGrant = previousGrant := by
    obtain ⟨initial, initialSupport, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    apply fixedGrant (ReactiveApplication.Execution.initial app initial) execution _ reached
    obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ initialSupport
    rfl
  obtain ⟨noise, prefixFactor⟩ := roster_compiled_prefix_noise setup leaks rosters timing network
    reveals openable decoded owner event.val event.isLt.le
  obtain ⟨grantedNoise, grantFactor⟩ := roster_prefix_grant_observation_kernel setup leaks prior
    event.val (fun execution supported => by
      obtain ⟨initial, _, state, related, readout⟩ := checkpoint execution supported
      exact ⟨initial, state, related, readout⟩)
    event owner players network previousGrant previous noise prefixFactor
  let granted : app.Execution → app.Execution := fun execution =>
    { execution with
      application := { execution.application with serviceGrant := some event }
      environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .application (.grant event)⟩] }
  have grantLaw (execution : app.Execution) :
      (runtime setup).runInteractionPlan leaks players network [.grant event] execution =
        PMF.pure (granted execution) := by
    simp only [runInteractionPlan, interactionStep, interactionInstruction, PMF.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
      reactiveApplication, environmentStep, PMF.pure_map,
      ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl
  let after := prior.map granted
  have grantedCheckpoint (execution : app.Execution) (supported : execution ∈ after.support) :
      ∃ initial ∈ setup.initialLaw.support, ∃ state,
        PublicPrefixCheckpoint setup leaks initial setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program))
          (Revelations.initial setup.context) (outputRef setup.program)
          0 event.val state execution ∧
        sourcePrefix? setup event.val execution.application.config = some state := by
    obtain ⟨before, beforeSupport, rfl⟩ := PMF.support_map .. ▸ supported
    obtain ⟨initial, initialSupport, state, related, readout⟩ := checkpoint before beforeSupport
    obtain ⟨actual, actualCheckpoint, _, _, _, actualLaw⟩ := related.grant players network event
    have same : granted before = actual := by
      apply (PMF.mem_support_pure_iff _ _).mp
      rw [← actualLaw, grantLaw]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    exact ⟨initial, initialSupport, state, same ▸ actualCheckpoint, readout⟩
  have afterSource : (after.map fun execution =>
      sourcePrefix? setup event.val execution.application.config) =
        prior.map (fun execution => sourcePrefix? setup event.val execution.application.config) :=
    by rw [PMF.map_comp]; rfl
  have factor : after.map (fun execution =>
      (sourcePrefix? setup event.val execution.application.config,
        (app.messageView execution, execution.recall owner))) =
      (after.map fun execution => sourcePrefix? setup event.val execution.application.config).bind
        fun state => (grantedNoise (setup.protocolObserve owner state)).map
          fun extra => (state, extra) := by
    rw [afterSource]
    have grants : (runtime setup).runInteractionPlan leaks players network [.grant event] =
        fun execution => PMF.pure (granted execution) := funext grantLaw
    have afterEq : prior.bind
        ((runtime setup).runInteractionPlan leaks players network [.grant event]) = after := by
      rw [grants]
      exact (FinDist.map_eq_bind granted prior).symm
    simpa only [afterEq] using grantFactor
  obtain ⟨channel, law⟩ := roster_owner_information_kernel setup leaks rosters timing decoded
    event owner owned after (fun execution supported => by
      obtain ⟨initial, _, state, related, readout⟩ := grantedCheckpoint execution supported
      exact ⟨initial, state, related, readout⟩)
    (fun execution supported => by
      obtain ⟨before, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl)
    (fun execution supported => by
      obtain ⟨initial, initialSupport, state, related, _⟩ :=
        grantedCheckpoint execution supported
      have current : execution.application.serviceGrant = some event := by
        obtain ⟨before, _, rfl⟩ := PMF.support_map .. ▸ supported
        rfl
      have data := owner_choices_at_prefix setup leaks bounds decoded owner initial initialSupport
        setup.program reveals decoded
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) (outputEmbedding setup.program)
        (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program decoded)
        event.val event.isLt state execution related event (by omega) owned current
      obtain ⟨candidate, raw, opening, author, valid, _⟩ := data.2.2
      exact ⟨candidate, raw, opening, author, valid⟩)
    (fun execution supported => by
      obtain ⟨before, member, rfl⟩ := PMF.support_map .. ▸ supported
      exact (counts before member).le)
    (fun execution supported => by
      obtain ⟨before, member, rfl⟩ := PMF.support_map .. ▸ supported
      exact app.environment_inputRecall before (granted before) (.application (.grant event))
        (recalls before member) (by
          simp only [ReactiveApplication.Execution.environmentStep, app, application,
            reactiveApplication, environmentStep, PMF.pure_map, PMF.mem_support_pure_iff _ _]
          rfl)) network visits grantedNoise factor
  refine ⟨channel, ?_⟩
  have sourceLaw := roster_compiled_prefix_law setup leaks rosters timing network reveals openable
    admission source.strategy event.val event.isLt.le
  rw [afterSource, sourceLaw] at law
  dsimp only
  refine Eq.trans ?_ law
  have expandedGrant := grantLaw
  dsimp only [players, decoded] at expandedGrant
  simp only [runInteractionPlan_append, expandedGrant, PMF.pure_bind, PMF.bind_bind,
    PMF.map_bind, after, PMF.bind_map, prior]
  apply bind_congr_on_support _
  intro initial _
  apply bind_congr_on_support _
  intro boundary _
  apply bind_congr_on_support _
  intro current reached
  have unchanged := rosterPolicy_run_application setup leaks rosters timing decoded network
    visits (granted boundary) current reached
  apply map_congr_on_support _
  intro final activated
  obtain ⟨_, sampleSupport, rfl⟩ := PMF.support_map .. ▸ activated
  obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ sampleSupport
  rw [unchanged]

omit [Fintype Player] in
/-- A supported actual owner input retains the semantic application of its
granted source checkpoint, even though its traffic and allocator have changed. -/
theorem roster_owner_supported_application [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (event : (graph setup).EventId) (owner : Player) (visits : List Player)
    (final : (application setup leaks).Execution) :
    let players := rosterPolicy setup leaks rosters timing
      (setup.decodeBehavioralProfile admission source.strategy)
    let executions := (initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
          visits.map ServiceInstruction.player)
        (ReactiveApplication.Execution.initial (application setup leaks) state)
    final ∈ (executions.bind fun current =>
      current.environmentStep (application setup leaks) (.activate owner)).support →
    ∃ initial state granted,
      PublicPrefixCheckpoint setup leaks initial setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) (outputRef setup.program)
        0 event.val state granted ∧
      sourcePrefix? setup event.val final.application.config = some state ∧
      final.application = granted.application := by
  intro players executions supported
  simp only [executions, runInteractionPlan_append, PMF.bind_bind] at supported
  obtain ⟨initial, initialSupport, moved⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨boundary, boundarySupport, moved⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have boundaryPresent : boundary ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters event.val)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support := by
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨initial, initialSupport, boundarySupport⟩
  obtain ⟨input, _, state, related, _⟩ := roster_compiled_prefix_checkpoint setup leaks bounds
    rosters network reveals openable admission source mixed timing timingFull
    event.val event.isLt.le boundary boundaryPresent
  obtain ⟨granted, grantedRelated, _, _, _, grantLaw⟩ := related.grant players network event
  rw [grantLaw, PMF.pure_bind] at moved
  obtain ⟨current, currentSupport, observed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have unchanged := rosterPolicy_run_application setup leaks rosters timing
    (setup.decodeBehavioralProfile admission source.strategy) network visits granted current
      currentSupport
  have finalApplication : final.application = granted.application := by
    obtain ⟨_, sampleSupport, rfl⟩ := PMF.support_map .. ▸ observed
    obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ sampleSupport
    exact unchanged
  refine ⟨input, state, granted, grantedRelated, ?_, finalApplication⟩
  rw [finalApplication]
  exact PublicPrefixCheckpoint.decode setup.program _ _ _ 0 event.val state granted grantedRelated

omit [Fintype Player] in
theorem roster_owner_information_projects [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (event : (graph setup).EventId) (owner : Player) (visits : List Player)
    (left right : (application setup leaks).Execution) :
    let players := rosterPolicy setup leaks rosters timing
      (setup.decodeBehavioralProfile admission source.strategy)
    let executions := ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
          visits.map ServiceInstruction.player)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
      fun current => current.environmentStep (application setup leaks) (.activate owner)
    left ∈ executions.support → right ∈ executions.support →
    left.observe (application setup leaks) owner = right.observe (application setup leaks) owner →
    setup.protocolObserve owner (sourcePrefix? setup event.val left.application.config) =
      setup.protocolObserve owner (sourcePrefix? setup event.val right.application.config) := by
  intro players executions leftSupport rightSupport same
  obtain ⟨_, leftState, leftGranted, leftCheckpoint, leftDecoded, leftApplication⟩ :=
    roster_owner_supported_application setup leaks bounds rosters network reveals openable
      admission source mixed timing timingFull event owner visits left leftSupport
  obtain ⟨_, rightState, rightGranted, rightCheckpoint, rightDecoded, rightApplication⟩ :=
    roster_owner_supported_application setup leaks bounds rosters network reveals openable
      admission source mixed timing timingFull event owner visits right rightSupport
  have applicationEq := congrArg ReactiveApplication.PlayerView.application same
  change (application setup leaks).observePlayer left.application owner =
    (application setup leaks).observePlayer right.application owner at applicationEq
  rw [leftApplication, rightApplication] at applicationEq
  have views := PublicPrefixCheckpoint.source_view_eq_of_application_eq owner setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputRef setup.program) 0 event.val leftState rightState
    leftGranted rightGranted leftCheckpoint rightCheckpoint applicationEq
  rw [leftDecoded, rightDecoded]
  exact congrArg some views

/-- Conditioning on a supported actual owner input gives exactly the original
source-state posterior. The observation includes complete private response
recall and the current passive sample, at any position in the phase. -/
theorem roster_owner_state_posterior
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) (visits : List Player)
    (reference : (application setup leaks).Execution) :
    let players := rosterPolicy setup leaks rosters timing
      (setup.decodeBehavioralProfile admission source.strategy)
    let executions := ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
          visits.map ServiceInstruction.player)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
      fun current => current.environmentStep (application setup leaks) (.activate owner)
    let info := fun final : (application setup leaks).Execution =>
      (final.recall owner, final.observe (application setup leaks) owner)
    reference ∈ executions.support →
    (fiberConditional executions info (info reference)).map
        (fun final => sourcePrefix? setup event.val final.application.config) =
      fiberConditional (((setup.informationModel admission).runBehavioral source.strategy (event.val + 1)).map
        ExecutionProtocol.History.state) (setup.protocolObserve owner)
          (setup.protocolObserve owner
            (sourcePrefix? setup event.val reference.application.config)) :=
    by
  intro players executions info referenceSupport
  let read := fun final : (application setup leaks).Execution =>
    sourcePrefix? setup event.val final.application.config
  let prior := ((setup.informationModel admission).runBehavioral source.strategy
    (event.val + 1)).map ExecutionProtocol.History.state
  obtain ⟨channel, factor⟩ := roster_owner_information_law setup leaks bounds rosters network
    reveals openable admission source mixed timing timingFull event owner owned visits
  change executions.map (fun final => (read final, info final)) =
    prior.bind (fun state => (channel (setup.protocolObserve owner state)).map
      fun input => (state, input)) at factor
  have referencePair : (read reference, info reference) ∈
      (prior.bind fun state => (channel (setup.protocolObserve owner state)).map
        fun input => (state, input)).support := by
    rw [← factor, PMF.support_map]
    exact ⟨reference, referenceSupport, rfl⟩
  have present : ∃ state ∈ prior.support,
      setup.protocolObserve owner state = setup.protocolObserve owner (read reference) ∧
      info reference ∈ (channel (setup.protocolObserve owner (read reference))).support := by
    obtain ⟨state, stateSupport, member⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ referencePair)
    obtain ⟨input, inputSupport, equal⟩ := PMF.support_map .. ▸ member
    have stateEq := (Prod.mk.inj equal).1
    have inputEq := (Prod.mk.inj equal).2
    refine ⟨state, stateSupport, congrArg (setup.protocolObserve owner) stateEq, ?_⟩
    simpa only [stateEq, inputEq] using inputSupport
  have recovers (state : setup.ProtocolState) (stateSupport : state ∈ prior.support)
      (possible : info reference ∈ (channel (setup.protocolObserve owner state)).support) :
      setup.protocolObserve owner state = setup.protocolObserve owner (read reference) := by
    have member : (state, info reference) ∈
        (prior.bind fun state => (channel (setup.protocolObserve owner state)).map
          fun input => (state, input)).support := by
      rw [PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨state, stateSupport, ?_⟩
      rw [PMF.support_map]
      exact ⟨info reference, possible, rfl⟩
    rw [← factor, PMF.support_map] at member
    obtain ⟨actual, actualSupport, equal⟩ := member
    have viewEq := congrArg Prod.snd (Prod.mk.inj equal).2
    have projected := roster_owner_information_projects setup leaks bounds rosters network
      reveals openable admission source mixed timing timingFull event owner visits actual reference
      actualSupport referenceSupport viewEq
    change setup.protocolObserve owner (read actual) =
      setup.protocolObserve owner (read reference) at projected
    rwa [(Prod.mk.inj equal).1] at projected
  have posterior := PMF.conditional_observation_kernel_recovered prior
    (setup.protocolObserve owner) channel (setup.protocolObserve owner (read reference))
    (info reference) present recovers
  have observed : info reference ∈
      (executions.map (Prod.snd ∘ fun final => (read final, info final))).support := by
    rw [PMF.support_map]
    exact ⟨reference, referenceSupport, rfl⟩
  have mapped := PMF.map_conditional_readout executions
    (fun final => (read final, info final)) Prod.snd (info reference) observed
  rw [factor] at mapped
  have retained := congrArg (PMF.map Prod.fst) mapped
  simp only [PMF.map_comp, Function.comp_def] at retained
  exact retained.trans posterior

end Vegas
