/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterOwnerPosterior
import Vegas.Game.SourceBayes
import Interaction.ReactiveBayes
import GameTheoryExtensions.Math.Probability.Conditioning

/-! # Actual native Bayes posteriors during an owner's roster phase

The finite retained game executes the same sampled activation as the physical
runtime. Its standard Bayes belief, projected to the existing source state,
is therefore the original source's conditional prefix law. Timing and replay
history remain part of the native information site.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A real retained owner decision determines an original source information
site and its depth, independently of any assessment or perturbation. -/
theorem roster_owner_source_site
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (grant : control.execution.application.serviceGrant = some event) :
    ∃ site : (setup.informationModel admission).InformationSite who,
      site.1 = setup.protocolObserve who
        (sourcePrefix? setup event.val control.execution.application.config) ∧
      setup.decisionDepth who site.1 = event.val + 1 := by
  obtain ⟨actual, _, granted, _, _, initial, state, _, initialSupport, related,
      sourceSupport, grantedAt, _, _, _, _, _, unchanged, _⟩ :=
    roster_decision_phase setup leaks bounds rosters network reveals openable
      who control trace active
  have same : actual = event := by
    rw [unchanged, grantedAt] at grant
    exact Option.some.inj grant
  subst actual
  obtain ⟨site, observed⟩ := roster_source_site setup leaks reveals admission who event owned
    initial initialSupport state granted related sourceSupport
  have decoded := PublicPrefixCheckpoint.decode setup.program
    (Vegas.ContextRefs.initial setup.context (Vegas.outputLayout setup.program))
    (Revelations.initial setup.context) (Vegas.outputRef setup.program) 0 event.val
    state granted related
  change sourcePrefix? setup event.val granted.application.config = some state at decoded
  refine ⟨site, ?_, ?_⟩
  · rw [unchanged, decoded]
    exact observed
  · let profile : BehavioralProfile setup.program :=
      fun owner => RevealOnly.uniformPolicy owner setup.program reveals
    have permitted : ∀ owner, (profile owner).Admitted setup.program admission :=
      fun owner => RevealOnly.uniformPolicy_admitted owner setup.program reveals admission
    obtain ⟨history, supported, stateEq⟩ := setup.exists_history_of_prefix_support admission
      profile permitted initial initialSupport event.val state sourceSupport
    have info : (setup.informationModel admission).infoOf who history.trace = site.1 := by
      rw [show (setup.informationModel admission).infoOf who history.trace =
        setup.protocolObserve who history.state from
          setup.protocol_info admission who history.trace,
        stateEq, observed]
    have acting := PublicPrefixCheckpoint.actor who setup.program
      (Vegas.ContextRefs.initial setup.context (Vegas.outputLayout setup.program))
      (Revelations.initial setup.context) (Vegas.outputRef setup.program) 0 event.val
      state granted related event.isLt
    rw [eventOwner?_eq_actor] at acting
    change ProtocolView.actor who setup.program (ProtocolState.observe who setup.program state) =
      (graph setup).actor? event at acting
    rw [owned] at acting
    have running : ¬ (setup.executionProtocol admission).terminal history.state := by
      rw [stateEq]
      intro stopped
      have absent := ProtocolState.terminal_actor_none who setup.program state stopped
      rw [acting] at absent
      cases absent
    have exactLength :=
      InformationModel.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
        (setup.informationModel admission)
        (fun owner => setup.toProtocolBehavioralPolicy admission owner (profile owner)
          (permitted owner)) (event.val + 1) (setup.executionProtocol admission).initHistory
        history supported
    have length : history.trace.length = event.val + 1 := by
      simpa only [ExecutionProtocol.initHistory, Trace.length, Nat.zero_add] using
        exactLength.resolve_left running
    exact (congrArg (setup.decisionDepth who) info.symm).trans
      ((setup.decisionDepth_trace admission who history.trace).trans length)

theorem roster_owner_bayes_posterior
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
    (count : Nat)
    (selected : (rosterPlan setup rosters)[count]? = some (.player owner))
    (before : (rosterPlan setup rosters).take count =
      rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
        visits.map ServiceInstruction.player)
    (reference : (application setup leaks).Execution) :
    let players := rosterPolicy setup leaks rosters timing
      (setup.decodeBehavioralProfile admission source.strategy)
    let executions := ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        ((rosterPlan setup rosters).take count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
      fun current => current.environmentStep (application setup leaks) (.activate owner)
    let menu := rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
    let scheduler := rosterScheduler setup leaks rosters network
    let horizon := (rosterPlan setup rosters).length
    let model := menu.information (initialLaw setup) horizon scheduler
    let assessment := InformationModel.BehavioralAssessment.ofStrategy
      (rosterPerturbedProfile setup leaks bounds rosters network admission
        source timing)
    let native := InformationModel.bayesAssessment _ assessment.strategy
        (rosterPerturbedProfile_fullyMixed setup leaks bounds rosters network reveals openable
        admission source mixed timing timingFull)
            (menu.decisionInformationAntichain (initialLaw setup) horizon scheduler)
    reference ∈ executions.support →
    ∀ site : model.InformationSite owner,
      site.1 = some (reference.recall owner, reference.observe (application setup leaks) owner) →
      (native.stateBelief owner site).map (fun state => state.bind fun control =>
        sourcePrefix? setup event.val control.execution.application.config) =
        fiberConditional (((setup.informationModel admission).runBehavioral source.strategy
            (event.val + 1)).map
          History.state) (setup.protocolObserve owner)
            (setup.protocolObserve owner
              (sourcePrefix? setup event.val reference.application.config)) := by
  intro players executions menu scheduler horizon model assessment native
    referenceSupport site siteInput
  let depth := count +
    (((rosterPlan setup rosters).take count).filterMap instructionActor).length + 2
  let embed := fun next : (application setup leaks).Execution =>
    (some ⟨horizon - count - 1, some owner, next⟩ : (application setup leaks).ProtocolState)
  let input := fun next : (application setup leaks).Execution =>
    (next.recall owner, next.observe (application setup leaks) owner)
  let read := fun state : (application setup leaks).ProtocolState => state.bind fun control =>
    sourcePrefix? setup event.val control.execution.application.config
  have observeEmbed (next : (application setup leaks).Execution) :
      (application setup leaks).observe owner (embed next) = some (input next) := by
    simp only [ReactiveApplication.observe, embed, input, ↓reduceIte]
  have law : (model.runBehavioral native.strategy depth).map History.state =
      executions.map embed :=
    roster_restrict_activation_state setup leaks rosters network menu players
      (rosterPolicy_admissible setup leaks bounds rosters network reveals openable admission
        source mixed timing timingFull) count owner selected
  have referenceState : embed reference ∈
      ((model.runBehavioral native.strategy depth).map History.state).support := by
    rw [law, PMF.support_map]
    exact ⟨reference, referenceSupport, rfl⟩
  obtain ⟨history, historySupport, stateEq⟩ := PMF.support_map .. ▸ referenceState
  have observed : model.infoOf owner history.trace = site.1 := by
    rw [show model.infoOf owner history.trace =
      (application setup leaks).observe owner history.state from menu.info .., stateEq, siteInput]
    exact observeEmbed reference
  have running : ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal history.state := by
    rw [stateEq]
    change ¬ (horizon - count - 1 = 0 ∧ (some owner : Option Player) = none)
    simp
  have exactDepth := InformationModel.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
    model native.strategy depth (menu.protocol (initialLaw setup) horizon scheduler).initHistory
      history historySupport
  have length : history.trace.length = depth := by
    simpa only [ExecutionProtocol.initHistory, Trace.length, Nat.zero_add] using
      exactDepth.resolve_left running
  obtain ⟨common, clock⟩ := roster_menu_common_depth setup leaks rosters network menu owner site
  have clockAt : ∀ current : model.InformationHistory owner site.1,
      current.1.trace.length = depth := fun current =>
    (clock current).trans ((clock ⟨history, observed⟩).symm.trans length)
  have mixedNative := assessment.bayes_isFullyMixed
    (rosterPerturbedProfile_fullyMixed setup leaks bounds rosters network reveals openable
      admission source mixed timing timingFull)
    (menu.decisionInformationAntichain (initialLaw setup) horizon scheduler)
  have bayesNative := InformationModel.bayesAssessment_isBayesConsistent _ assessment.strategy
      (rosterPerturbedProfile_fullyMixed setup leaks bounds rosters network reveals openable
      admission source mixed timing timingFull)
          (menu.decisionInformationAntichain (initialLaw setup) horizon scheduler)
  have conditioned := menu.stateBelief_eq_conditional_prefix (initialLaw setup) horizon scheduler
    native mixedNative bayesNative owner site depth clockAt
  rw [law, siteInput] at conditioned
  have present : some (input reference) ∈
      (executions.map ((application setup leaks).observe owner ∘ embed)).support := by
    rw [PMF.support_map]
    exact ⟨reference, referenceSupport, observeEmbed reference⟩
  have transported := PMF.map_conditional_readout executions embed
    ((application setup leaks).observe owner) (some (input reference)) present
  have fiber := fiberConditional_eq_of_support_fiber executions
    ((application setup leaks).observe owner ∘ embed) input (some (input reference))
    (input reference) (by
      intro value _
      simp only [Function.comp_apply, observeEmbed, Option.some.injEq])
  rw [fiber] at transported
  have posterior := roster_owner_state_posterior setup leaks bounds rosters network reveals
    openable admission source mixed timing timingFull event owner owned visits reference
  have supported : reference ∈ (((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
          visits.map ServiceInstruction.player)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
      fun current => current.environmentStep (application setup leaks) (.activate owner)).support :=
    by simpa only [executions, before] using referenceSupport
  have result := posterior supported
  change (native.stateBelief owner site).map read = _
  rw [conditioned, ← transported, PMF.map_comp]
  simpa only [executions, before, Function.comp_def, read, embed, Option.bind_some, input]
    using result

/-- Every actual information history can serve as the reference input in the
posterior identity. Full mixing supplies its positive reach; no chosen-run
support hypothesis is supplied by the caller. -/
theorem roster_owner_bayes_at_history
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
    (count : Nat)
    (selected : (rosterPlan setup rosters)[count]? = some (.player owner))
    (before : (rosterPlan setup rosters).take count =
      rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
        visits.map ServiceInstruction.player) :
    let menu := rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
    let scheduler := rosterScheduler setup leaks rosters network
    let horizon := (rosterPlan setup rosters).length
    let model := menu.information (initialLaw setup) horizon scheduler
    let assessment := InformationModel.BehavioralAssessment.ofStrategy
      (rosterPerturbedProfile setup leaks bounds rosters network admission
        source timing)
    let native := InformationModel.bayesAssessment _ assessment.strategy
        (rosterPerturbedProfile_fullyMixed setup leaks bounds rosters network reveals openable
        admission source mixed timing timingFull)
            (menu.decisionInformationAntichain (initialLaw setup) horizon scheduler)
    ∀ (site : model.InformationSite owner) (history : model.InformationHistory owner site.1)
      (control : (application setup leaks).Control),
      history.1.state = some control →
      control.execution.environmentRecall.length = count + 1 →
      (native.stateBelief owner site).map (fun state => state.bind fun current =>
        sourcePrefix? setup event.val current.execution.application.config) =
        fiberConditional (((setup.informationModel admission).runBehavioral source.strategy
            (event.val + 1)).map
          History.state) (setup.protocolObserve owner)
            (setup.protocolObserve owner
              (sourcePrefix? setup event.val control.execution.application.config)) := by
  intro menu scheduler horizon model assessment native site history control current position
  let players := rosterPolicy setup leaks rosters timing
    (setup.decodeBehavioralProfile admission source.strategy)
  let depth := count +
    (((rosterPlan setup rosters).take count).filterMap instructionActor).length + 2
  have mixedNative := assessment.bayes_isFullyMixed
    (rosterPerturbedProfile_fullyMixed setup leaks bounds rosters network reveals openable
      admission source mixed timing timingFull)
    (menu.decisionInformationAntichain (initialLaw setup) horizon scheduler)
  have active := InformationModel.InformationSite.active model site history
  rw [current] at active
  have acting : control.actor = some owner := active
  let traced : (menu.protocol (initialLaw setup) horizon scheduler).Trace (some control) :=
    current ▸ history.1.trace
  have length : history.1.trace.length = depth := by
    have exactLength := roster_decision_depth setup leaks rosters network menu owner control
      traced acting count position
    have castLength {left right : (application setup leaks).ProtocolState}
        (equal : left = right)
        (path : (menu.protocol (initialLaw setup) horizon scheduler).Trace left) :
        (equal ▸ path).length = path.length := by cases equal; rfl
    have traceLength : traced.length = history.1.trace.length := castLength current history.1.trace
    exact traceLength.symm.trans exactLength
  have supported : history.1 ∈ (model.runBehavioral native.strategy depth).support := by
    have reaches := mixedNative.history_supported history.1.trace
    rwa [length] at reaches
  have law := roster_restrict_activation_state setup leaks rosters network menu players
    (rosterPolicy_admissible setup leaks bounds rosters network reveals openable admission
      source mixed timing timingFull) count owner selected
  change (model.runBehavioral native.strategy depth).map History.state = _ at law
  have stateSupport : some control ∈
      ((model.runBehavioral native.strategy depth).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨history.1, supported, current⟩
  rw [law, PMF.support_map] at stateSupport
  obtain ⟨execution, executionSupport, same⟩ := stateSupport
  have executionEq : execution = control.execution :=
    congrArg ReactiveApplication.Control.execution (Option.some.inj same)
  have referenceSupport := executionEq ▸ executionSupport
  have observed : site.1 = some
      (control.execution.recall owner, control.execution.observe (application setup leaks) owner) :=
    by
    have info := (menu.info (initialLaw setup) horizon scheduler owner history.1.trace).symm.trans
      history.2
    rw [current] at info
    simpa only [ReactiveApplication.observe, acting, ↓reduceIte] using info.symm
  exact roster_owner_bayes_posterior setup leaks bounds rosters network reveals openable admission
    source mixed timing timingFull event owner owned visits count selected before control.execution
      referenceSupport site observed

/-- Projected Bayes beliefs agree with the original source assessment at the
structurally recovered site, including native timing histories that disappear
in the limiting strategy. -/
theorem roster_owner_bayes_source_state
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    [∀ who (site : (setup.informationModel admission).InformationSite who),
      Fintype ((setup.informationModel admission).InformationHistory who site.1)]
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission) source (setup.decision_antichain admission))
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) (visits : List Player)
    (count : Nat)
    (selected : (rosterPlan setup rosters)[count]? = some (.player owner))
    (before : (rosterPlan setup rosters).take count =
      rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
        visits.map ServiceInstruction.player) :
    let menu := rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
    let scheduler := rosterScheduler setup leaks rosters network
    let horizon := (rosterPlan setup rosters).length
    let model := menu.information (initialLaw setup) horizon scheduler
    let assessment := InformationModel.BehavioralAssessment.ofStrategy
      (rosterPerturbedProfile setup leaks bounds rosters network admission
        source timing)
    let native := InformationModel.bayesAssessment _ assessment.strategy
        (rosterPerturbedProfile_fullyMixed setup leaks bounds rosters network reveals openable
        admission source mixed timing timingFull)
            (menu.decisionInformationAntichain (initialLaw setup) horizon scheduler)
    ∀ (site : model.InformationSite owner) (history : model.InformationHistory owner site.1)
      (control : (application setup leaks).Control),
      history.1.state = some control →
      control.execution.environmentRecall.length = count + 1 →
      ∀ sourceSite : (setup.informationModel admission).InformationSite owner,
        sourceSite.1 = setup.protocolObserve owner
          (sourcePrefix? setup event.val control.execution.application.config) →
        setup.decisionDepth owner sourceSite.1 = event.val + 1 →
        (native.stateBelief owner site).map (fun state => state.bind fun current =>
          sourcePrefix? setup event.val current.execution.application.config) =
            source.stateBelief owner sourceSite := by
  intro menu scheduler horizon model assessment native site history control current position
    sourceSite sourceView sourceDepth
  have projected := roster_owner_bayes_at_history setup leaks bounds rosters network reveals
    openable admission source mixed timing timingFull event owner owned visits count selected
    before site history control current position
  have original := setup.stateBelief_eq_conditional_prefix admission source mixed bayes
    owner sourceSite
  rw [sourceDepth, sourceView] at original
  exact projected.trans original.symm

end Vegas
