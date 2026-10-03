/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstInputTerminalLaw
import Vegas.Game.SourceServiceFirstInputAncestor

/-! # Actual native first-site Bayes beliefs with original source restoration

The native belief samples the actual before-response information history. One
common original-memory lottery read there agrees with the persistent earlier
source readout at its terminal descendants. Conditioning on actual passage
therefore gives the original source posterior on the recovered compressed view.
This statement concerns the pure represented normalized first-turn strategy;
perturbed assessment consistency and sequential rationality are separate.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

open Classical in
private theorem conditional_gate {Source Info : Type*} (joint : PMF (Source × Info))
    (input : Info) (present : input ∈ (joint.map Prod.snd).support) :
    fiberPosterior (joint.bind fun pair =>
      if pair.2 = input then PMF.pure (some pair.1) else PMF.pure none) Option.isSome true =
        ((fiberPosterior joint Prod.snd input).map Prod.fst).map some := by
  classical
  let observed := fun pair : Source × Info => decide (pair.2 = input)
  let kernel := fun pair : Source × Info =>
    if pair.2 = input then PMF.pure (some pair.1) else PMF.pure none
  have meets : true ∈ (joint.map observed).support := by
    obtain ⟨pair, supported, equal⟩ := PMF.support_map .. ▸ present
    exact PMF.support_map .. ▸ ⟨pair, supported, by simp only [observed, equal, decide_true]⟩
  have retains : ∀ pair ∈ joint.support, ∀ result ∈ (kernel pair).support,
      result.isSome = observed pair := by
    intro pair _supported result selected
    by_cases equal : pair.2 = input
    · simp only [kernel, equal, ↓reduceIte, PMF.mem_support_pure_iff] at selected
      subst result
      simp only [observed, equal, decide_true, Option.isSome_some]
    · simp only [kernel, equal, ↓reduceIte, PMF.mem_support_pure_iff] at selected
      subst result
      simp only [observed, equal, decide_false, Option.isSome_none]
  change fiberPosterior (joint.bind kernel) Option.isSome true = _
  rw [fiberPosterior_bind_of_observation joint kernel observed Option.isSome retains true meets]
  have fiber : fiberPosterior joint observed true = fiberPosterior joint Prod.snd input :=
    fiberPosterior_eq_of_support_fiber joint observed Prod.snd true input
      (fun pair _supported => by simp only [observed, decide_eq_true_eq])
  rw [fiber, PMF.map_comp]
  apply bind_congr_on_support _
  intro pair supported
  have equal := (mem_support_fiberPosterior present supported).1
  simp only [kernel, equal, ↓reduceIte]
  rfl

open Classical in
/-- The genuine information ancestor's restoration kernel equals the
terminal retrospective kernel on actual passage through this first owned site.
The outer option records passage; the inner decoder option remains distinct. -/
theorem sourceServiceRestoredPrefix_passage_law {Parameter : Type}
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter)
    (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (strategy : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) (event : (graph setup).EventId)
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (observed : site.1 = some (past, view))
    (turn : view.application.publicView.ownTurn? who = some event)
    (absent : sourceServiceTurnInput? setup leaks who event past = none) :
    let app := application setup leaks
    let model := menu.information initial horizon scheduler
    let certificate := (menu.bounded initial horizon scheduler).wellFoundedHistories
    let terminal := model.runBehavioralTerminalFrom certificate strategy
      (menu.protocol initial horizon scheduler).initHistory
    let readBefore := fun before : model.InformationHistory who site.1 =>
      match before.1.state with
      | none => PMF.pure none
      | some control => sourceServiceRestoredPrefixReadout profile parameter event.val
          control.execution.application.config
    let readFinal := fun state : app.ProtocolState =>
      match state with
      | none => PMF.pure (none, none)
      | some control => (sourceServicePastRestoredPrefixReadout profile parameter event.val
          control.execution.application.config).map fun restored =>
            (restored, sourceServiceFirstInput? setup leaks who event
              (control.execution.recall who))
    (terminal.bind fun final =>
      match site.ancestor? model final with
      | none => PMF.pure none
      | some before => (readBefore before).map some) =
    (terminal.bind fun final => readFinal final.state).bind fun pair =>
      if pair.2 = site.1 then PMF.pure (some pair.1) else PMF.pure none := by
  classical
  intro app model certificate terminal readBefore readFinal
  rw [PMF.bind_bind]
  apply bind_congr_on_support terminal
  intro final supported
  have complete := model.runBehavioralTerminalFrom_support_terminal certificate strategy
    (menu.protocol initial horizon scheduler).initHistory final supported
  obtain ⟨control, current⟩ : ∃ control : app.Control, final.state = some control := by
    cases stateEq : final.state with
    | none => change app.terminal final.state at complete
              rw [stateEq] at complete
              exact complete.elim
    | some control => exact ⟨control, rfl⟩
  have passage := sourceServiceFirstInput?_eq_iff_passage menu initial horizon scheduler who
    event site past view observed turn absent final complete
  cases ancestor : site.ancestor? model final with
  | none =>
      have missing : sourceServiceFirstInput? setup leaks who event
          (control.execution.recall who) ≠ site.1 := by
        intro equal
        obtain ⟨before, reached⟩ := passage.mp
          (by simpa only [current, ReactiveApplication.recallAt] using equal)
        have actual := (site.ancestor?_eq_some_iff model
          (menu.decisionInformationAntichain initial horizon scheduler who site) final before).mpr
            reached
        rw [ancestor] at actual
        cases actual
      simp only [readFinal, current, PMF.bind_map, Function.comp_def, missing, ↓reduceIte,
        PMF.bind_const]
  | some before =>
      have reached := (site.ancestor?_eq_some_iff model
        (menu.decisionInformationAntichain initial horizon scheduler who site) final before).mp
          ancestor
      have equal : sourceServiceFirstInput? setup leaks who event
          (control.execution.recall who) = site.1 := by
        simpa only [current, ReactiveApplication.recallAt] using passage.mpr ⟨before, reached⟩
      let actual : model.InformationHistory who (some (past, view)) :=
        ⟨before.1, before.2.trans observed⟩
      obtain ⟨remaining, execution, beforeEq, _recallEq, _viewEq, ordered, _decoded⟩ :=
        sourceServiceInformation_owned_prefix setup leaks menu initial horizon scheduler who
          event past view turn actual
      change before.1.state = some ⟨remaining, some who, execution⟩ at beforeEq
      obtain ⟨fuel, path⟩ := reached
      have kernels := sourceServicePastRestoredPrefixReadout_reaches profile parameter event.val
        initial horizon scheduler (menu.reaches_raw initial horizon scheduler path)
          ⟨remaining, some who, execution⟩ control beforeEq current ordered
      simp only [readBefore, beforeEq, readFinal, current, PMF.bind_map, Function.comp_def,
        equal, ↓reduceIte, kernels]
      rfl

/-- Positive passage gives both genuine input support and the restored
native Bayes belief from the actual joint terminal readout. The decoder may
fail for arbitrary strategies; its option is preserved in this equality. -/
theorem sourceServiceRestoredPrefix_native_bayes {Parameter : Type}
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter)
    (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (strategy : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) (event : (graph setup).EventId)
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (observed : site.1 = some (past, view))
    (turn : view.application.publicView.ownTurn? who = some event)
    (absent : sourceServiceTurnInput? setup leaks who event past = none)
    (positive : 0 < (menu.information initial horizon scheduler).informationMass
      strategy who site) :
    let app := application setup leaks
    let model := menu.information initial horizon scheduler
    let certificate := (menu.bounded initial horizon scheduler).wellFoundedHistories
    let terminal := model.runBehavioralTerminalFrom certificate strategy
      (menu.protocol initial horizon scheduler).initHistory
    let antichain := menu.decisionInformationAntichain initial horizon scheduler who site
    let readBefore := fun before : model.InformationHistory who site.1 =>
      match before.1.state with
      | none => PMF.pure none
      | some control => sourceServiceRestoredPrefixReadout profile parameter event.val
          control.execution.application.config
    let readFinal := fun state : app.ProtocolState =>
      match state with
      | none => PMF.pure (none, none)
      | some control => (sourceServicePastRestoredPrefixReadout profile parameter event.val
          control.execution.application.config).map fun restored =>
            (restored, sourceServiceFirstInput? setup leaks who event
              (control.execution.recall who))
    let joint := terminal.bind fun final => readFinal final.state
    site.1 ∈ (joint.map Prod.snd).support ∧
      (model.bayesBelief strategy who site antichain positive).bind readBefore =
        (fiberPosterior joint Prod.snd site.1).map Prod.fst := by
  classical
  intro app model certificate terminal antichain readBefore readFinal joint
  have mass := sourceServiceFirstInput?_terminal_passage_mass menu initial horizon
    scheduler strategy who event site past view observed turn absent
  have truePresent : true ∈ (terminal.map (fun final => decide
      (sourceServiceFirstInput? setup leaks who event
        (app.recallAt who final.state) = site.1))).support := by
    rw [PMF.mem_support_iff, mass]
    exact positive.ne'
  obtain ⟨final, supported, flag⟩ := PMF.support_map .. ▸ truePresent
  have complete := model.runBehavioralTerminalFrom_support_terminal certificate strategy
    (menu.protocol initial horizon scheduler).initHistory final supported
  obtain ⟨control, current⟩ : ∃ control : app.Control, final.state = some control := by
    cases stateEq : final.state with
    | none => change app.terminal final.state at complete
              rw [stateEq] at complete
              exact complete.elim
    | some control => exact ⟨control, rfl⟩
  have inputEq : sourceServiceFirstInput? setup leaks who event
      (control.execution.recall who) = site.1 := by
    have equal := of_decide_eq_true flag
    simpa only [current, ReactiveApplication.recallAt] using equal
  obtain ⟨restored, chosen⟩ := (sourceServicePastRestoredPrefixReadout profile parameter event.val
    control.execution.application.config).support_nonempty
  have selected : (restored, site.1) ∈ joint.support := by
    change (restored, site.1) ∈ (terminal.bind fun final => readFinal final.state).support
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨final, supported, ?_⟩
    simp only [readFinal, current, inputEq, PMF.support_map]
    exact ⟨restored, chosen, rfl⟩
  have inputSupport : site.1 ∈ (joint.map Prod.snd).support :=
    PMF.support_map .. ▸ ⟨(restored, site.1), selected, rfl⟩
  have passage := sourceServiceRestoredPrefix_passage_law profile parameter menu initial
    horizon scheduler strategy who event site past view observed turn absent
  have bayesPassage := site.bayesBelief_bind_eq_conditional_passage model antichain certificate
    strategy positive readBefore
  refine ⟨inputSupport, ?_⟩
  apply pmf_map_injective (Option.some_injective _)
  calc
    _ = fiberPosterior (terminal.bind fun final =>
        match site.ancestor? model final with
        | none => PMF.pure none
        | some before => (readBefore before).map some) Option.isSome true := by
      convert! bayesPassage using 1
      apply congrArg (fun law => fiberPosterior law Option.isSome true)
      apply bind_congr_on_support terminal
      intro history _supported
      cases site.ancestor? model history <;> rfl
    _ = _ := by
      rw [passage]
      exact conditional_gate joint site.1 inputSupport

end Vegas

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

/-- At every positive-mass first owned input of the represented normalized
first-turn strategy, an ordinary Bayes-consistent native history belief,
followed by its actual ancestor's one common restoration draw, is the true
original source prefix posterior on the recovered compressed own view. -/
theorem normalizedFirstTurnProfile_first_input_source_belief {Parameter : Type} (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (parameter : State L service.setup.context → Parameter)
    (who : Player) (event : (graph service.setup).EventId)
    (owned : (graph service.setup).actor? event = some who) :
    let originalLaw := service.setup.initialLaw.bind fun initial =>
      ((fun law => law.bind (ProtocolState.behavioralStateStep service.setup.program
        profile))^[event.val]
          (PMF.pure (ProtocolState.entry service.setup.program
            (service.setup.initialConfig initial)))).map
              fun original => (parameter initial, original)
    let observe := fun carried : Parameter × ProtocolState service.setup.program =>
      ProtocolView.normalizeDisclosureRecall service.setup.program (fun view => view.2)
        (ProtocolState.observe who service.setup.program carried.2)
    let normalized := normalizeDisclosureProfile service.setup.program []
      (Revelations.initial service.setup.context) profile
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let model := menu.information (initialLaw service.setup) service.horizon service.scheduler
    let strategy := service.firstTurnProfile turns normalized
    ∃ recover : (application service.setup service.leaks).Info →
        Option (ProtocolView who service.setup.program),
    ∀ assessment : model.BehavioralAssessment, assessment.strategy = strategy →
      InformationModel.BehavioralAssessment.IsBayesConsistent model assessment
        (menu.decisionInformationAntichain (initialLaw service.setup) service.horizon
          service.scheduler) →
      ∀ (site : model.InformationSite who)
        (past : List (application service.setup service.leaks).PlayerEntry)
        (view : (application service.setup service.leaks).PlayerView),
        site.1 = some (past, view) →
        view.application.publicView.ownTurn? who = some event →
        sourceServiceTurnInput? service.setup service.leaks who event past = none →
        0 < model.informationMass strategy who site →
        let readBefore := fun before : model.InformationHistory who site.1 =>
          match before.1.state with
          | none => PMF.pure none
          | some control => sourceServiceRestoredPrefixReadout profile parameter event.val
              control.execution.application.config
        ∃ sourceView : ProtocolView who service.setup.program,
          recover site.1 = some sourceView ∧
            (assessment.belief who site).bind readBefore =
              (fiberPosterior originalLaw observe sourceView).map some := by
  classical
  intro originalLaw observe normalized menu model strategy
  obtain ⟨recover, posterior⟩ := sourceServiceFirstTurn_first_input_readout_posterior
    (turns := turns) service.contract service.timely profile parameter who event owned
  refine ⟨recover, ?_⟩
  intro assessment represented bayes site past view observed turn absent positive readBefore
  let app := application service.setup service.leaks
  let initial := initialLaw service.setup
  let certificate := (menu.bounded initial service.horizon service.scheduler).wellFoundedHistories
  let terminal := model.runBehavioralTerminalFrom certificate strategy
    (menu.protocol initial service.horizon service.scheduler).initHistory
  let readFinal := fun state : app.ProtocolState =>
    match state with
    | none => PMF.pure (none, none)
    | some control => (sourceServicePastRestoredPrefixReadout profile parameter event.val
        control.execution.application.config).map fun restored =>
          (restored, sourceServiceFirstInput? service.setup service.leaks who event
            (control.execution.recall who))
  let joint := terminal.bind fun final => readFinal final.state
  obtain ⟨inputSupport, nativeBayes⟩ := sourceServiceRestoredPrefix_native_bayes profile parameter
    menu initial service.horizon service.scheduler strategy who event site past view observed
      turn absent positive
  change site.1 ∈ (joint.map Prod.snd).support at inputSupport
  have actualJoint := service.normalizedFirstTurnProfile_first_input_joint_readout turns profile
    permitted parameter who event owned
  dsimp only at actualJoint
  let players := sourceServiceTurnPolicy service.setup service.leaks service.bound turns
    (firstTurnTiming service.setup turns) normalized
  let stopped := service.setup.initialLaw.bind fun initial =>
    ((application service.setup service.leaks).runUntilHorizon service.scheduler players
      (sourceServiceRankCompleted event.val) service.horizon
      (.initial (application service.setup service.leaks)
        (EventGraphRuntime.State.initial (service.setup.eventInputs initial)))).bind
          fun execution =>
          ((application service.setup service.leaks).runUntilHorizon service.scheduler players
            (fun final => sourceServiceTurnInput? service.setup service.leaks who event
              (final.recall who) ≠ none) service.horizon execution).bind fun final =>
                (sourceServiceRestoredPrefixReadout profile parameter event.val
                  final.application.config).map fun restored =>
                    (restored, sourceServiceTurnInput? service.setup service.leaks who event
                      (final.recall who))
  have actualJoint' : joint = stopped := by
    convert! actualJoint using 1
    apply bind_congr_on_support terminal
    intro history _supported
    cases history.state <;> rfl
  have stoppedSupport := inputSupport
  rw [actualJoint'] at stoppedSupport
  obtain ⟨sourceView, recovered, conditioned⟩ := posterior site.1 stoppedSupport
  have originalPosterior : (fiberPosterior joint Prod.snd site.1).map Prod.fst =
      (fiberPosterior originalLaw observe sourceView).map some := by
    rw [actualJoint']
    exact conditioned
  let antichain := menu.decisionInformationAntichain initial service.horizon service.scheduler
    who site
  have belief : assessment.belief who site =
      model.bayesBelief strategy who site antichain positive := by
    ext before
    rw [model.bayesBelief_apply]
    have actual := bayes who site (by rwa [represented]) before
    simpa only [represented] using actual
  refine ⟨sourceView, recovered, ?_⟩
  rw [belief]
  convert! nativeBayes.trans originalPosterior using 1
  apply bind_congr_on_support _
  intro before _supported
  dsimp only [readBefore]
  cases before.1.state <;> rfl

end Vegas.AsyncServiceSpec
