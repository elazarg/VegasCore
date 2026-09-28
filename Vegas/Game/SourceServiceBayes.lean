/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefixPosterior
import Interaction.ReactiveBayes

/-! # Full-source native Bayes beliefs

The actual retained finite protocol has the same pending activation law as the
physical timed compiler. At every owner history its standard Bayes belief,
projected through the source-prefix decoder, is the conditional normalized
source-state law. Original source comparisons use the existing disclosure
memory comparison theorem on this law.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem sourceService_owner_bayes_posterior
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (full : ∀ event who owned, (timing event who owned).FullSupport)
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (native : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (strategy : native.strategy =
      sourceServiceTimedProfile setup leaks bounds rosters network timing original)
    (mixed : native.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network))
      native ((sourceServiceMenu setup leaks bounds rosters).decisionInformationAntichain
        (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) (visits : List Player)
    (count : Nat)
    (selected : (rosterPlan setup rosters)[count]? = some (.player owner))
    (before : (rosterPlan setup rosters).take count =
      rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
        visits.map ServiceInstruction.player)
    (reference : (application setup leaks).Execution) :
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) original
    let admission := CommitmentInterface.values setup.program
    let encoded := fun who => setup.toProtocolBehavioralPolicy admission who
      (normalized who) (normalized_sourceService_admitted setup original permitted who)
    let players := sourceServiceTimedPolicy setup leaks rosters timing normalized
    let executions := ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        ((rosterPlan setup rosters).take count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
      fun current => current.environmentStep (application setup leaks) (.activate owner)
    reference ∈ executions.support →
    ∀ site : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).InformationSite owner,
      site.1 = some (reference.recall owner, reference.observe (application setup leaks) owner) →
      (native.stateBelief owner site).map (fun state => state.bind fun control =>
        sourceServicePrefix? setup event.val control.execution.application.config) =
        (((setup.informationModel admission).runBehavioral encoded (event.val + 1)).map
          History.state).condOnFibre (setup.protocolObserve owner)
            (setup.protocolObserve owner
              (sourceServicePrefix? setup event.val reference.application.config)) := by
  intro normalized admission encoded players executions referenceSupport site siteInput
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  let horizon := (rosterPlan setup rosters).length
  let model := menu.information (initialLaw setup) horizon scheduler
  let depth := count +
    (((rosterPlan setup rosters).take count).filterMap instructionActor).length + 2
  let embed := fun next : (application setup leaks).Execution =>
    (some ⟨horizon - count - 1, some owner, next⟩ : (application setup leaks).ProtocolState)
  let input := fun next : (application setup leaks).Execution =>
    (next.recall owner, next.observe (application setup leaks) owner)
  let read := fun state : (application setup leaks).ProtocolState => state.bind fun control =>
    sourceServicePrefix? setup event.val control.execution.application.config
  have observeEmbed (next : (application setup leaks).Execution) :
      (application setup leaks).observe owner (embed next) = some (input next) := by
    simp only [ReactiveApplication.observe, embed, input, ↓reduceIte]
  have law : (model.runBehavioral native.strategy depth).map History.state =
      executions.map embed := by
    rw [strategy]
    exact roster_restrict_activation_state setup leaks rosters network menu players
      (sourceServiceTimedPolicy_admissible setup leaks bounds values initialValues capacity
        rosters opportunities network timing full normalized
          (normalized_sourceService_admitted setup original permitted)) count owner selected
  have referenceState : embed reference ∈
      ((model.runBehavioral native.strategy depth).map History.state).support := by
    rw [law, FinDist.support_map]
    exact ⟨reference, referenceSupport, rfl⟩
  obtain ⟨history, historySupport, stateEq⟩ := FinDist.support_map .. ▸ referenceState
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
  obtain ⟨_, clock⟩ := roster_menu_common_depth setup leaks rosters network menu owner site
  have clockAt : ∀ current : model.InformationHistory owner site.1,
      current.1.trace.length = depth := fun current =>
    (clock current).trans ((clock ⟨history, observed⟩).symm.trans length)
  have conditioned := menu.stateBelief_eq_conditional_prefix (initialLaw setup) horizon scheduler
    native mixed bayes owner site depth clockAt
  rw [law, siteInput] at conditioned
  have present : some (input reference) ∈
      (executions.map ((application setup leaks).observe owner ∘ embed)).support := by
    rw [FinDist.support_map]
    exact ⟨reference, referenceSupport, observeEmbed reference⟩
  have transported := FinDist.map_conditional_readout executions embed
    ((application setup leaks).observe owner) (some (input reference)) present
  have fiber := FinDist.condOnFibre_eq_of_support_fiber executions
    ((application setup leaks).observe owner ∘ embed) input (some (input reference))
    (input reference) (by
      intro value _
      simp only [Function.comp_apply, observeEmbed, Option.some.injEq])
  rw [fiber] at transported
  have posterior := sourceService_owner_posterior setup leaks bounds values initialValues
    capacity rosters opportunities timing full network original permitted event owner owned visits
      reference
  have supported : reference ∈ (((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
          visits.map ServiceInstruction.player)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
      fun current => current.environmentStep (application setup leaks) (.activate owner)).support :=
    by simpa only [executions, before] using referenceSupport
  have result := posterior supported
  change (native.stateBelief owner site).map read = _
  rw [conditioned, ← transported, FinDist.map_comp]
  simpa only [executions, before, Function.comp_def, read, embed, Option.bind_some, input]
    using result

/-- An arbitrary legal information history supplies its own positive prefix
support under the fully mixed native assessment. No physical support or
conditional-state correspondence is required from the caller. -/
theorem sourceService_owner_bayes_at_history
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (full : ∀ event who owned, (timing event who owned).FullSupport)
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (native : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (strategy : native.strategy =
      sourceServiceTimedProfile setup leaks bounds rosters network timing original)
    (mixed : native.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network))
      native ((sourceServiceMenu setup leaks bounds rosters).decisionInformationAntichain
        (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) (visits : List Player)
    (count : Nat)
    (selected : (rosterPlan setup rosters)[count]? = some (.player owner))
    (before : (rosterPlan setup rosters).take count =
      rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
        visits.map ServiceInstruction.player) :
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) original
    let admission := CommitmentInterface.values setup.program
    let encoded := fun who => setup.toProtocolBehavioralPolicy admission who
      (normalized who) (normalized_sourceService_admitted setup original permitted who)
    let model := (sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    let executions := ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing normalized) network
        ((rosterPlan setup rosters).take count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
      fun before => before.environmentStep (application setup leaks) (.activate owner)
    ∀ (site : model.InformationSite owner) (history : model.InformationHistory owner site.1)
      (control : (application setup leaks).Control),
      history.1.state = some control →
      control.execution.environmentRecall.length = count + 1 →
      control.execution ∈ executions.support ∧
      (native.stateBelief owner site).map (fun state => state.bind fun current =>
        sourceServicePrefix? setup event.val current.execution.application.config) =
        (((setup.informationModel admission).runBehavioral encoded (event.val + 1)).map
          History.state).condOnFibre (setup.protocolObserve owner)
            (setup.protocolObserve owner
              (sourceServicePrefix? setup event.val control.execution.application.config)) := by
  intro normalized admission encoded model executions site history control current position
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduler := rosterScheduler setup leaks rosters network
  let horizon := (rosterPlan setup rosters).length
  let players := sourceServiceTimedPolicy setup leaks rosters timing normalized
  let depth := count +
    (((rosterPlan setup rosters).take count).filterMap instructionActor).length + 2
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
    have reaches := mixed.history_supported history.1.trace
    rwa [length] at reaches
  have law := roster_restrict_activation_state setup leaks rosters network menu players
    (sourceServiceTimedPolicy_admissible setup leaks bounds values initialValues capacity
      rosters opportunities network timing full normalized
        (normalized_sourceService_admitted setup original permitted)) count owner selected
  change (model.runBehavioral
    (sourceServiceTimedProfile setup leaks bounds rosters network timing original) depth).map
      History.state = _ at law
  rw [← strategy] at law
  have stateSupport : some control ∈
      ((model.runBehavioral native.strategy depth).map History.state).support := by
    rw [FinDist.support_map]
    exact ⟨history.1, supported, current⟩
  rw [law, FinDist.support_map] at stateSupport
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
  refine ⟨referenceSupport, ?_⟩
  exact sourceService_owner_bayes_posterior setup leaks bounds values initialValues capacity
    rosters opportunities timing full network original permitted native strategy mixed bayes
      event owner owned visits count selected before control.execution referenceSupport site
        observed

end Vegas
