/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalCurrentBindingGain
import Vegas.Game.ReservedEpochPublicationComparison
import Vegas.Game.PhaseProposalPublicationAliases
import Vegas.Game.PhaseProposalPublicationPayoff

/-! # Publication timing at the original full information -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem expect_le_expect_of_support_order {α β : Type*}
    (left : PMF α) (right : PMF β) (first : α → ℝ) (second : β → ℝ)
    (leftIntegrable : PayoffIntegrable left first)
    (rightIntegrable : PayoffIntegrable right second)
    (ordered : ∀ a ∈ left.support, ∀ b ∈ right.support, second b ≤ first a) :
    expect right second ≤ expect left first := by
  have averaged := expect_mono (μ := left)
    (f := fun _ => expect right second) (g := first)
    (fun a supported => expect_le_const right second rightIntegrable (first a)
      (ordered a supported)) (payoffIntegrable_constant left _) leftIntegrable
  simpa only [expect_constant] using averaged

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  {tapeLength : Nat} (prior : PMF (ReservedEpoch.Tape Player tapeLength))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime
local notation "scheduler" => ReactiveApplication.SchedulerImplementation.scheduler
  (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime) prior)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

private theorem publication_anchored_terminal_state
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fixedScheduler : (app).Scheduler) (remaining : Nat) (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon fixedScheduler).Trace
      (some ⟨remaining, none, execution⟩)) :
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let model := (menu).information initial horizon fixedScheduler
    let certificate := ((menu).bounded initial horizon fixedScheduler).wellFoundedHistories
    let profile := fun owner => (menu).restrictPolicy initial horizon fixedScheduler owner
      (ReactiveApplication.anchoredPolicy execution players owner)
    (model.runBehavioralTerminalFrom certificate profile
      ⟨some ⟨remaining, none, execution⟩, trace⟩).map History.state =
      (app).finish initial horizon fixedScheduler players (some ⟨remaining, none, execution⟩) := by
  classical
  intro players model certificate profile
  let physical := ReactiveApplication.anchoredPolicy execution players
  have decoded : (menu).decodeProfile initial horizon fixedScheduler profile = physical := by
    funext owner
    apply (menu).decode_restrictPolicy_of_covered initial horizon fixedScheduler owner
    intro past view action supported
    exact (menu).anchoredPolicy_covered initial horizon fixedScheduler
      ⟨remaining, none, execution⟩ trace players owner
        (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values owner)
          past view action supported
  have law := (menu).terminal_run_eq_finish initial horizon fixedScheduler certificate profile
    ⟨some ⟨remaining, none, execution⟩, trace⟩
  rw [decoded] at law
  rw [law]
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind,
    physical, ReactiveApplication.runRounds_anchoredPolicy]

private theorem publication_terminal_reanchor
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fixedScheduler : (app).Scheduler) (anchor ending : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon fixedScheduler).Trace (some anchor))
    (endingTrace : ((menu).protocol initial horizon fixedScheduler).Trace (some ending))
    (retained : TracePrefix anchorTrace endingTrace) :
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let model := (menu).information initial horizon fixedScheduler
    let certificate := ((menu).bounded initial horizon fixedScheduler).wellFoundedHistories
    let profile := fun execution owner => (menu).restrictPolicy initial horizon fixedScheduler
      owner (ReactiveApplication.anchoredPolicy execution players owner)
    model.runBehavioralTerminalFrom certificate (profile anchor.execution)
      ⟨some ending, endingTrace⟩ =
    model.runBehavioralTerminalFrom certificate (profile ending.execution)
      ⟨some ending, endingTrace⟩ := by
  classical
  intro players model certificate profile
  apply model.runBehavioralTerminalFrom_congr certificate
  intro later reached _running owner
  obtain ⟨fuel, path⟩ := reached
  rcases later with ⟨state, laterTrace⟩
  have observed := (menu).info initial horizon fixedScheduler owner laterTrace
  change model.infoOf owner laterTrace = (app).observe owner state at observed
  cases state with
  | none => rw [observed]; rfl
  | some current =>
      by_cases activeOwner : current.actor = some owner
      · have endingPrefix := (app).reaches_recall_prefix initial horizon fixedScheduler
          ((menu).reaches_raw initial horizon fixedScheduler path) ending current rfl rfl owner
        have anchorPrefix := (app).reaches_recall_prefix initial horizon fixedScheduler
          ((menu).reaches_raw initial horizon fixedScheduler retained.reachesWithin)
            anchor ending rfl rfl owner
        have laws :
            ReactiveApplication.anchoredPolicy anchor.execution players owner
                (current.execution.recall owner) (current.execution.observe app owner) =
              ReactiveApplication.anchoredPolicy ending.execution players owner
                (current.execution.recall owner) (current.execution.observe app owner) := by
          rw [ReactiveApplication.anchoredPolicy_of_extends _ players owner _ _
            (anchorPrefix.trans endingPrefix),
            ReactiveApplication.anchoredPolicy_of_extends _ players owner _ _ endingPrefix]
        simp only [ReactiveApplication.observe, ite_eq_left activeOwner] at observed
        rw [observed]
        exact (menu).restrictPolicy_eq_of_law_eq initial horizon fixedScheduler owner
          _ _ _ _ laws
      · simp only [ReactiveApplication.observe, ite_eq_right activeOwner] at observed
        rw [observed]
        rfl

private theorem publication_stopped_pair_payoff_le
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (tape : ReservedEpoch.Tape Player tapeLength)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1)
      (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player)
    (bound : ℝ)
    (bounded : ∀ state,
      |phaseExclusionBase setup mode runtime leaks utility excludedPayoff state who| ≤ bound)
    (floor : ∀ state, excludedPayoff who ≤
      phaseExclusionBase setup mode runtime leaks utility excludedPayoff state who)
    (remaining : Nat) (execution : (app).Execution)
    (fixedCallback : ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, some who, execution⟩))
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ execution.application.phases.head?) (kind : phase.kind = .reveal)
    (witness : RecoverySourceWitness setup mode plan execution.application)
    (archive : witness.checkpoint.ArchivedProposals execution.network.inputs)
    (leftMaterial : WitnessedSubmission (serviceGraph setup mode))
    (pairing : PairedPublicationBoundary setup mode runtime leaks bounds plan values tape
      remaining execution who leftMaterial fixedCallback phase witness.checkpoint)
    (stop : (app).Action → ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).History →
      Prop)
    (stops : ∀ response history, stop response history =
      match history.state with
      | none => False
      | some ending => ending.execution.application.attempt ≠
          (execution.respond app who response).application.attempt) :
    let family := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime)
    let cleanPlayers := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let payoff := phaseExclusionBase setup mode runtime leaks utility excludedPayoff
    let fixedModel := (menu).information initial horizon (family tape)
    let fixedCertificate := ((menu).bounded initial horizon (family tape)).wellFoundedHistories
    let responseAnchor := fun response => execution.respond app who response
    let responseProfile := fun response owner => (menu).restrictPolicy initial horizon
      (family tape) owner (ReactiveApplication.anchoredPolicy (responseAnchor response)
        cleanPlayers owner)
    let stopped := stop
    let leftTrace := pairing.choose
    let rightTrace := pairing.choose_spec.choose
    ∀ leftFinal ∈ (fixedModel.runBehavioralUntil fixedCertificate
      (responseProfile ⟨some leftMaterial⟩) (stopped ⟨some leftMaterial⟩)
        ⟨some ⟨remaining, none, responseAnchor ⟨some leftMaterial⟩⟩, leftTrace⟩).support,
    ∀ rightFinal ∈ (fixedModel.runBehavioralUntil fixedCertificate
      (responseProfile ⟨none⟩) (stopped ⟨none⟩)
        ⟨some ⟨remaining, none, responseAnchor ⟨none⟩⟩, rightTrace⟩).support,
    expect (fixedModel.runBehavioralTerminalFrom fixedCertificate (responseProfile ⟨none⟩)
      rightFinal) (fun final => payoff final.state who) ≤
    expect (fixedModel.runBehavioralTerminalFrom fixedCertificate
      (responseProfile ⟨some leftMaterial⟩) leftFinal) (fun final => payoff final.state who) := by
  classical
  intro family cleanPlayers payoff fixedModel fixedCertificate responseAnchor responseProfile
    stopped leftTrace rightTrace
  let leftResponse : (app).Action := ⟨some leftMaterial⟩
  let rightResponse : (app).Action := ⟨none⟩
  have facts := pairing.choose_spec.choose_spec
  have leftResponsePrefix : TracePrefix fixedCallback leftTrace := facts.1
  have rightResponsePrefix : TracePrefix fixedCallback rightTrace := facts.2.1
  have closed := facts.2.2.2.2.2.2
  have expectedFloor : ∀ {α : Type} (law : PMF α) (readout : α → (app).ProtocolState),
      excludedPayoff who ≤ expect law (fun result => payoff (readout result) who) := by
    intro α distribution readout
    have monotone := expect_mono (μ := distribution)
      (f := fun _ => excludedPayoff who) (g := fun result => payoff (readout result) who)
      (fun result _ => floor (readout result)) (payoffIntegrable_constant _ _)
      (payoffIntegrable_of_bounded _ _ (fun result => bounded (readout result)))
    simpa only [expect_constant] using monotone
  intro leftFinal leftReached rightFinal rightReached
  obtain ⟨leftEnding, rightEnding, leftBefore, rightBefore, leftPrior, rightPrior,
    leftJoint, rightJoint, leftLegal, rightLegal, leftRealized, rightRealized,
    leftRaw, rightRaw, leftState, rightState, leftIdle, rightIdle,
    leftNormalized, rightNormalized, leftPrefix, rightPrefix,
    leftEndPrefix, rightEndPrefix, leftSame, rightSame, leftChanged, rightChanged,
    leftEffect, rightEffect, leftHead, rightHead, leftFinished, rightFinished,
    leftCoverage, rightCoverage, leftExcluded, rightExcluded, foreignWord, survival⟩ :=
      closed leftFinal (by
        convert leftReached using 1
        dsimp only
        congr 2
        funext history
        have same := (stops leftResponse history).symm
        cases stateEq : history.state <;>
          simpa only [stateEq, stopped, leftResponse] using same)
        rightFinal (by
          convert rightReached using 1
          dsimp only
          congr 2
          funext history
          have same := (stops rightResponse history).symm
          cases stateEq : history.state <;>
            simpa only [stateEq, stopped, rightResponse] using same)
  by_cases excluded : who ∈ (phase.drain rightRaw).excluded
  · have fixed := phase_excluded_expected_payoff setup mode runtime leaks utility
      excludedPayoff menu initial horizon (family tape) fixedCertificate
        (responseProfile ⟨none⟩) who rightFinal
          (by simpa only [PhaseExcluded, rightState, ← rightExcluded] using excluded)
    rw [fixed]
    exact expectedFloor _
      (fun final : ((menu).protocol initial horizon (family tape)).History => final.state)
  obtain ⟨leftSurvives, excludedEq, inputEq, archiveEq, controlsEq, leftNext, rightNext,
    leftPath, leftPublicSteps, leftAddresses, leftOwn,
    rightPath, rightPublicSteps, rightAddresses, rightOwn,
    leftReplay, rightReplay, pointEq, historyEq, enrichedEq, addressEq, live⟩ :=
      survival excluded
  let anchor : (app).Control := ⟨remaining, some who, execution⟩
  let leftEndingTrace : ((menu).protocol initial horizon (family tape)).Trace
      (some leftEnding) := leftState ▸ leftFinal.trace
  let rightEndingTrace : ((menu).protocol initial horizon (family tape)).Trace
      (some rightEnding) := rightState ▸ rightFinal.trace
  have leftKept : TracePrefix fixedCallback leftPrior := leftResponsePrefix.trans leftPrefix
  have rightKept : TracePrefix fixedCallback rightPrior := rightResponsePrefix.trans rightPrefix
  have rightLive : ∀ owner, owner ∉ (phase.drain rightRaw).excluded →
      ProtocolState.BindingsHoldValues owner setup.program
        (rightNext.residual.lift (ProtocolState.entry rightNext.residual.tail
          rightNext.source)) :=
    by
      intro owner survives
      rw [← pointEq]
      exact live owner (by rwa [excludedEq])
  let q0 := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  let sourcePayoff := setup.proposalRecoveryPayoff utility excludedPayoff who
  let sourceCertificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
  have leftLaw := phaseProposal_original_publication_payoff_law setup mode runtime leaks
    bounds plan complete covered maximal values fullValues tape activationGap processingGap
      gaps margin capacity utility excludedPayoff anchor fixedCallback
        witness archive phase installed kind leftBefore leftEnding leftPrior leftEndingTrace
          leftKept leftSame leftIdle leftChanged leftRaw leftEffect leftNormalized
            leftFinished leftExcluded leftNext leftPath leftPublicSteps leftAddresses leftOwn
              leftReplay live who
  have rightLaw := phaseProposal_original_publication_payoff_law setup mode runtime leaks
    bounds plan complete covered maximal values fullValues tape activationGap processingGap
      gaps margin capacity utility excludedPayoff anchor fixedCallback
        witness archive phase installed kind rightBefore rightEnding rightPrior rightEndingTrace
          rightKept rightSame rightIdle rightChanged rightRaw rightEffect rightNormalized
            rightFinished rightExcluded rightNext rightPath rightPublicSteps rightAddresses
              rightOwn rightReplay rightLive who
  have sourceLaw := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
    (setup.proposalRecoveryModel.runBehavioralTerminalFrom sourceCertificate q0 history).map
      sourcePayoff) enrichedEq
  have samePayoff := leftLaw.trans (sourceLaw.trans rightLaw.symm)
  let leftEndpoint := fun owner => (menu).restrictPolicy initial horizon
    (family tape) owner (ReactiveApplication.anchoredPolicy leftEnding.execution
      cleanPlayers owner)
  let rightEndpoint := fun owner => (menu).restrictPolicy initial horizon
    (family tape) owner (ReactiveApplication.anchoredPolicy rightEnding.execution
      cleanPlayers owner)
  have leftFinalEq : leftFinal = ⟨some leftEnding, leftEndingTrace⟩ := by
    cases leftFinal with
    | mk state trace => cases leftState; rfl
  have rightFinalEq : rightFinal = ⟨some rightEnding, rightEndingTrace⟩ := by
    cases rightFinal with
    | mk state trace => cases rightState; rfl
  have leftResponseKept : TracePrefix leftTrace leftEndingTrace := by
    cases leftFinal with
    | mk state trace =>
        cases leftState
        exact (TracePrefix.extend leftPrefix leftJoint leftLegal leftRealized).trans leftEndPrefix
  have rightResponseKept : TracePrefix rightTrace rightEndingTrace := by
    cases rightFinal with
    | mk state trace =>
        cases rightState
        exact (TracePrefix.extend rightPrefix rightJoint rightLegal rightRealized).trans
          rightEndPrefix
  have leftReanchored : fixedModel.runBehavioralTerminalFrom fixedCertificate
        (responseProfile leftResponse) leftFinal =
      fixedModel.runBehavioralTerminalFrom fixedCertificate leftEndpoint
        ⟨some leftEnding, leftEndingTrace⟩ := by
    rw [leftFinalEq]
    exact publication_terminal_reanchor setup mode runtime leaks bounds plan values (family tape)
      ⟨remaining, none, responseAnchor leftResponse⟩ leftEnding leftTrace leftEndingTrace
        leftResponseKept
  have rightReanchored : fixedModel.runBehavioralTerminalFrom fixedCertificate
        (responseProfile rightResponse) rightFinal =
      fixedModel.runBehavioralTerminalFrom fixedCertificate rightEndpoint
        ⟨some rightEnding, rightEndingTrace⟩ := by
    rw [rightFinalEq]
    exact publication_terminal_reanchor setup mode runtime leaks bounds plan values (family tape)
      ⟨remaining, none, responseAnchor rightResponse⟩ rightEnding rightTrace rightEndingTrace
        rightResponseKept
  have exactLaw := (congrArg
    (PMF.map fun final => payoff final.state who) leftReanchored).trans
      (samePayoff.trans (congrArg
        (PMF.map fun final => payoff final.state who) rightReanchored).symm)
  have exactExpectation := congrArg
    (fun distribution : PMF ℝ => expect distribution id) exactLaw
  simpa only [expect_map, Function.comp_def, id_eq] using exactExpectation.symm.le

private theorem publication_finish_le_of_stopped
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fixedScheduler : (app).Scheduler) (remaining : Nat) (left right : (app).Execution)
    (leftTrace : ((menu).protocol initial horizon fixedScheduler).Trace
      (some ⟨remaining, none, left⟩))
    (rightTrace : ((menu).protocol initial horizon fixedScheduler).Trace
      (some ⟨remaining, none, right⟩))
    (leftStop rightStop : ((menu).protocol initial horizon fixedScheduler).History → Prop)
    (payoff : (app).ProtocolState → ℝ) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ state, |payoff state| ≤ bound) :
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let model := (menu).information initial horizon fixedScheduler
    let certificate := ((menu).bounded initial horizon fixedScheduler).wellFoundedHistories
    let profile := fun execution owner => (menu).restrictPolicy initial horizon fixedScheduler
      owner (ReactiveApplication.anchoredPolicy execution players owner)
    (∀ leftFinal ∈ (model.runBehavioralUntil certificate (profile left) leftStop
      ⟨some ⟨remaining, none, left⟩, leftTrace⟩).support,
    ∀ rightFinal ∈ (model.runBehavioralUntil certificate (profile right) rightStop
      ⟨some ⟨remaining, none, right⟩, rightTrace⟩).support,
      expect (model.runBehavioralTerminalFrom certificate (profile right) rightFinal)
        (fun final => payoff final.state) ≤
      expect (model.runBehavioralTerminalFrom certificate (profile left) leftFinal)
        (fun final => payoff final.state)) →
    expect ((app).finish initial horizon fixedScheduler players
      (some ⟨remaining, none, right⟩)) payoff ≤
    expect ((app).finish initial horizon fixedScheduler players
      (some ⟨remaining, none, left⟩)) payoff := by
  classical
  intro players model certificate profile ordered
  have terminalValue (execution : (app).Execution)
      (trace : ((menu).protocol initial horizon fixedScheduler).Trace
        (some ⟨remaining, none, execution⟩)) :
      expect ((app).finish initial horizon fixedScheduler players
        (some ⟨remaining, none, execution⟩)) payoff =
      expect (model.runBehavioralTerminalFrom certificate (profile execution)
        ⟨some ⟨remaining, none, execution⟩, trace⟩) (fun final => payoff final.state) := by
    have law := publication_anchored_terminal_state setup mode runtime leaks bounds plan
      values fixedScheduler remaining execution trace
    rw [← law, expect_map]
    rfl
  rw [terminalValue right rightTrace, terminalValue left leftTrace,
    model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate
      (profile right) rightStop,
    model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate (profile left) leftStop]
  erw [expect_bind_tower_bounded _ _ _
    (fun final : ((menu).protocol initial horizon fixedScheduler).History => bounded final.state),
    expect_bind_tower_bounded _ _ _
      (fun final : ((menu).protocol initial horizon fixedScheduler).History => bounded final.state)]
  exact expect_le_expect_of_support_order _ _ _ _
    (payoffIntegrable_of_bounded _ _ (fun _ =>
      expect_abs_le_of_bounded nonnegative (fun final => bounded final.state)))
    (payoffIntegrable_of_bounded _ _ (fun _ =>
      expect_abs_le_of_bounded nonnegative (fun final => bounded final.state))) ordered

open Classical in
/-- An arbitrary current publication lottery is evaluated at the complete
original information. Its raw aliases and the callback tape posterior stay literal. -/
theorem phaseProposal_publication_gain_le
    [Fintype (E).History]
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (wellFormed : setup.WellFormed)
    (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support,
      tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
        activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1)
      (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (rates : PhaseProposalRates)
    (waitingPositive : 0 < rates.waiting.val)
    (waitingBelow : rates.waiting.val < 1)
    (slotsPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val)
    (badBelow : rates.badPreparation.val < 1)
    (assessment : (N).BehavioralAssessment)
    (prescribed : assessment.strategy =
      phaseProposalReferenceStrategy setup mode runtime leaks bounds plan
        initial horizon scheduler values rates)
    (who : Player) (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (information : site.1 = some (past, view))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (publication : (serviceGraph setup mode).outputLayout event = .publication payload)
    (requested : PhaseRuntimeState.requests view.application.2 who
      ⟨view.application.2.attempt, event⟩)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ bound)
    (excludedBound : |excludedPayoff who| ≤ bound)
    (defaultFloor : excludedPayoff who ≤ 0)
    (terminalFloor : ∀ terminal, excludedPayoff who ≤ utility terminal who)
    (law : PMF ((N).Choice who site.1)) :
    let foreignPosterior :=
      ∑ history : (N).InformationHistory who site.1 with
        (∃ owner : Player, who ≠ owner ∧
          PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds
            initial horizon scheduler owner history.val),
        (assessment.belief who site history).toReal
    (N).localGain (2 * horizon + 1) (fun history => history.state)
      (phaseExclusionBase setup mode runtime leaks utility excludedPayoff)
        assessment site law ≤
      (2 * bound) * (foreignPosterior +
        (2 * (Fintype.card Player * (2 * horizon + 1) : Nat) + 1) * rates.flagBound) := by
  classical
  intro foreignPosterior
  let fuel := 2 * horizon + 1
  let payoff := phaseExclusionBase setup mode runtime leaks utility excludedPayoff
  let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
  let deviation : (N).AssessmentDeviation who :=
    ⟨site, (assessment.strategy who).withLaw site.1 law⟩
  have runPresentation : (N).truncatedRunner fuel =
      (N).runBehavioralTerminalFrom certificate := by
    funext profile history
    exact ((N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
      ((menu).bounded initial horizon scheduler) profile history).symm
  have presentation :
      (N).localGain fuel (fun history => history.state) payoff assessment site law =
        expect ((N).assessmentComparisonWith ((N).runBehavioralTerminalFrom certificate)
          (fun history => history.state) assessment who deviation).alternative (payoff · who) -
        expect ((N).assessmentComparisonWith ((N).runBehavioralTerminalFrom certificate)
          (fun history => history.state) assessment who deviation).prescribed (payoff · who) := by
    change expect ((N).assessmentComparisonWith ((N).truncatedRunner fuel)
        (fun history => history.state) assessment who deviation).alternative (payoff · who) -
      expect ((N).assessmentComparisonWith ((N).truncatedRunner fuel)
        (fun history => history.state) assessment who deviation).prescribed (payoff · who) = _
    rw [runPresentation]
  let bad := fun history : (N).InformationHistory who site.1 =>
    ∃ owner : Player, who ≠ owner ∧
      PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds
        initial horizon scheduler owner history.val
  let error := (2 * (Fintype.card Player * (2 * horizon + 1) : Nat) + 1) *
    rates.flagBound * (2 * bound)
  have flagNonnegative : 0 ≤ rates.flagBound :=
    add_nonneg (add_nonneg (add_nonneg rates.waiting.property.1
      rates.badPreparation.property.1) rates.slots.property.1) rates.aliases.property.1
  have posteriorNonnegative : 0 ≤ foreignPosterior :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have errorNonnegative : 0 ≤ error := by
    dsimp only [error]
    positivity
  have bounded : ∀ state, |payoff state who| ≤ bound := by
    intro state
    have interval := phaseExclusionBase_mem_Icc setup mode runtime leaks utility excludedPayoff
      (fun _ => -bound) (fun _ => bound)
      (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).1)
      (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).2) state who
    have lower := (abs_le.mp excludedBound).1
    have upper := (abs_le.mp excludedBound).2
    exact abs_le.mpr (by
      simpa only [min_eq_right lower, min_eq_right (neg_nonpos.mpr nonnegative),
        max_eq_right upper, max_eq_right nonnegative, Set.mem_Icc] using interval)
  have floor : ∀ state, excludedPayoff who ≤ payoff state who := by
    intro state
    cases state with
    | none => exact defaultFloor
    | some control =>
        change excludedPayoff who ≤ if who ∈ control.execution.application.current.excluded
          then excludedPayoff who else
            (phaseSourceReadout setup mode runtime leaks (some control)).elim 0
              (fun terminal => utility terminal who)
        split_ifs
        · exact le_rfl
        · cases readout : phaseSourceReadout setup mode runtime leaks (some control) with
          | none => exact defaultFloor
          | some terminal => exact terminalFloor terminal
  have expectedFloor : ∀ {α : Type} (law : PMF α) (readout : α → (app).ProtocolState),
      excludedPayoff who ≤ expect law (fun result => payoff (readout result) who) := by
    intro α distribution readout
    have monotone := expect_mono (μ := distribution)
      (f := fun _ => excludedPayoff who) (g := fun result => payoff (readout result) who)
      (fun result _ => floor (readout result)) (payoffIntegrable_constant distribution _)
      (payoffIntegrable_of_bounded _ _ (fun result => bounded (readout result)))
    simpa only [expect_constant] using monotone
  have histories : ∀ history : (N).InformationHistory who site.1,
      (N).historyGain ((N).runBehavioralTerminalFrom certificate)
          (fun final => final.state) payoff assessment deviation history ≤
        (if bad history then 2 * bound else 0) + error := by
    intro history
    have actual : ∃ control : (app).Control, history.val.state = some control ∧
        control.actor = some who ∧ control.execution.recall who = past ∧
          control.execution.observe app who = view := by
      have observed := ((menu).info initial horizon scheduler who history.val.trace).symm.trans
        (history.property.trans information)
      cases current : history.val.state with
      | none => rw [current] at observed; cases observed
      | some control =>
          rw [current] at observed
          change (if control.actor = some who then
            some (control.execution.recall who, control.execution.observe app who) else none) =
              some (past, view) at observed
          split at observed
          · rename_i active
            exact ⟨control, rfl, active, (Prod.mk.inj (Option.some.inj observed)).1,
              (Prod.mk.inj (Option.some.inj observed)).2⟩
          · cases observed
    obtain ⟨control, current, active, recalled, observed⟩ := actual
    let counted : (E).Trace (some control) := current ▸ history.val.trace
    have rawTrace := (menu).toRawTrace initial horizon scheduler counted
    have sameInitial : initial = setup.initialLaw.map
        (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
    have original := sameInitial ▸ counted
    obtain ⟨witness, archive⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode
      runtime leaks bounds plan maximal horizon scheduler original
    obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan
      (setup.initialLaw.map encodeInputs) horizon scheduler rawTrace
    have actualRequest : PhaseRuntimeState.requests control.execution.application.publicView
        who ⟨control.execution.application.attempt, event⟩ := by
      change PhaseRuntimeState.requests (control.execution.observe app who).application.2 who
        ⟨(control.execution.observe app who).application.2.attempt, event⟩
      rwa [observed]
    have request := (control.execution.application.requests_publicView valid who
      ⟨control.execution.application.attempt, event⟩).mp actualRequest
    have callback : (E).Trace
        (some ⟨control.remaining, some who, control.execution⟩) := by
      simpa only [← active] using counted
    by_cases sent : ∃ message ∈ (app).outputs (control.execution.recall who),
        PhaseSeedScheduler.ownPacket ⟨control.execution.application.attempt, event⟩
          who message = true
    · have singleton := PhaseCount.onePacketActions_eq_singleton_of_sent runtime leaks bounds
        plan (serviceGraph_revealRelaxedOrdered setup mode) (setup.initialLaw.map encodeInputs)
          horizon scheduler control.remaining who control.execution callback _ request sent
      have singletonInput : (menu).actions who past view = {⟨none⟩} := by
        rwa [recalled, observed] at singleton
      have unique : ∀ first second : (N).Choice who site.1, first = second := by
        intro first second
        apply Subtype.ext
        have firstLegal := first.property
        have secondLegal := second.property
        simp only [information] at firstLegal secondLegal
        obtain ⟨firstAction, firstOffered, firstEq⟩ := firstLegal
        obtain ⟨secondAction, secondOffered, secondEq⟩ := secondLegal
        rw [singletonInput] at firstOffered secondOffered
        exact firstEq.trans ((congrArg some ((Finset.mem_singleton.mp firstOffered).trans
          (Finset.mem_singleton.mp secondOffered).symm)).trans secondEq.symm)
      have : Subsingleton ((N).Choice who site.1) := ⟨unique⟩
      have sameLaw : law = assessment.strategy who site.1 := by
        let choice := (assessment.strategy who site.1).support_nonempty.choose
        exact (eq_pure_of_subsingleton law choice).trans
          (eq_pure_of_subsingleton (assessment.strategy who site.1) choice).symm
      have fixed : deviation.2 = assessment.strategy who := by
        dsimp only [deviation]
        rw [sameLaw, InformationModel.BehavioralPolicy.withLaw_eq_self]
      simp only [InformationModel.historyGain, fixed, sub_self]
      exact add_nonneg (by split_ifs <;> positivity) errorNonnegative
    have unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
        PhaseCount.event? message.payload ≠
          some ⟨control.execution.application.attempt, event⟩ := by
      intro message output named
      have recalledInputs := (app).history_inputRecall initial horizon scheduler rawTrace who
      rw [← recalledInputs] at output
      have ownerEq : message.sender = who := of_decide_eq_true (List.mem_filter.mp output).2
      obtain ⟨actualEvent, actualNamed, coordinateEq⟩ := Option.map_eq_some_iff.mp named
      have coordinates := CommitAttemptEvent.mk.inj coordinateEq
      apply sent
      refine ⟨message, ?_, ?_⟩
      · rw [← recalledInputs]
        exact output
      · apply decide_eq_true
        exact ⟨ownerEq, coordinates.1, coordinates.2 ▸ actualNamed⟩
    obtain ⟨kernel, _responseLaw, responseStates, flagError⟩ :=
      phaseProposal_current_gain_flag_error setup mode
      runtime leaks bounds plan complete covered maximal values fullValues rates waitingPositive
        waitingBelow slotsPositive badPositive badBelow horizon scheduler control.remaining who
          control.execution callback
            utility excludedPayoff bound nonnegative utilityBound excludedBound
    let cleanValue := fun (responses : PMF (app).Action) =>
      expect ((responses.bind kernel).bind fun next =>
      (N).runBehavioralTerminalFrom certificate
        (fun owner => (menu).restrictPolicy initial horizon scheduler owner
          (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values owner)) next)
            (fun final => payoff final.state who)
    let decoded := (law.map fun choice => choice.1.getD ⟨none⟩)
    let prescribedClean := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan
      values who (control.execution.recall who) (control.execution.observe app who)
    let cleanPlayers := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let cleanProfile := fun owner => (menu).restrictPolicy initial horizon scheduler owner
      (cleanPlayers owner)
    let updatedClean := Profile.update (sig := (N).behavioralSignature) cleanProfile who
      ((cleanProfile who).withLaw site.1 law)
    have cleanDecoded : (menu).decodeProfile initial horizon scheduler cleanProfile =
        cleanPlayers := by
      funext owner
      exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler owner
        (cleanPlayers owner)
          (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values owner)
    have localDecoded (profile : ∀ owner, (N).BehavioralPolicy owner)
        (lottery : PMF ((N).Choice who site.1)) :
        (menu).decodeProfile initial horizon scheduler
          (Profile.update (sig := (N).behavioralSignature) profile who
            ((profile who).withLaw site.1 lottery)) who
          (control.execution.recall who) (control.execution.observe app who) =
            lottery.map (fun choice => choice.1.getD ⟨none⟩) := by
      simp only [ReactiveApplication.ResponseMenu.decodeProfile,
        ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
        PMF.map_comp, Function.comp_def, Profile.update_same]
      erw [recalled, observed, ← information,
        InformationModel.BehavioralPolicy.withLaw_self]
      rfl
    have updatedDecoded : (menu).decodeProfile initial horizon scheduler updatedClean who
        (control.execution.recall who) (control.execution.observe app who) = decoded :=
      localDecoded cleanProfile law
    let posterior := ((app).schedulerMixture prior
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime))).posterior
        control.execution.environmentRecall
    have physicalValue (profile : ∀ owner, (N).BehavioralPolicy owner)
        (responses : PMF (app).Action)
        (currentLaw : (menu).decodeProfile initial horizon scheduler profile who
          (control.execution.recall who) (control.execution.observe app who) = responses) :
        cleanValue responses = expect (posterior.bind fun tape => responses.bind fun response =>
          (app).finish initial horizon
            (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
              cleanPlayers (some ⟨control.remaining, none,
                control.execution.respond app who response⟩)) (fun state => payoff state who) := by
      have physicalLaw :
          (((responses.bind kernel).bind fun next =>
            (N).runBehavioralTerminalFrom certificate cleanProfile next).map History.state) =
          responses.bind (fun response => (app).finish initial horizon scheduler cleanPlayers
            (some ⟨control.remaining, none, control.execution.respond app who response⟩)) := by
        rw [PMF.bind_bind, PMF.map_bind]
        apply bind_congr_on_support
        intro response supported
        have nextState := responseStates profile response (by rwa [currentLaw])
        have physical := phaseProposal_response_kernel_finish setup mode runtime leaks bounds
          plan prior cleanProfile kernel control.remaining who control.execution response nextState
        rwa [cleanDecoded] at physical
      calc
        _ = expect (((responses.bind kernel).bind fun next =>
            (N).runBehavioralTerminalFrom certificate cleanProfile next).map History.state)
              (fun state => payoff state who) := (expect_map _ _ _).symm
        _ = _ := by
          rw [physicalLaw, phaseProposal_current_finish_seed_marginal setup mode runtime leaks
            plan prior cleanPlayers control.remaining who control.execution responses]
          rfl
    have cleanComparison : cleanValue decoded - cleanValue prescribedClean ≤
        if bad history then 2 * bound else 0 := by
      by_cases foreignBad : bad history
      · rw [ite_eq_left foreignBad]
        have alternative : |cleanValue decoded| ≤ bound :=
          expect_abs_le_of_bounded nonnegative (fun final => bounded final.state)
        have reference : |cleanValue prescribedClean| ≤ bound :=
          expect_abs_le_of_bounded nonnegative (fun final => bounded final.state)
        linarith [(abs_le.mp alternative).2, (abs_le.mp reference).1]
      rw [ite_eq_right foreignBad]
      have actualHistory :
          (⟨some control, counted⟩ : (E).History) = history.val := by
        rcases history with ⟨⟨state, trace⟩, _atInfo⟩
        cases current
        rfl
      have ownAlternative := (setup.commitRecovery_bindingsHoldValues_or_failedBinding
        wellFormed witness.checkpoint.trace who _ rfl).1
      -- Marginalize the ORIGINAL supported callback tape posterior. This factual
      -- equality is the projection of schedulerMixture_finish_joint; response
      -- registration preserves environmentRecall and hence that same posterior.
      rw [physicalValue updatedClean decoded updatedDecoded,
        physicalValue cleanProfile prescribedClean (by rw [cleanDecoded])]
      apply sub_nonpos.mpr
      apply expect_bind_mono_on_support
        posterior _ _ _
        (payoffIntegrable_of_bounded _ _ bounded)
        (payoffIntegrable_of_bounded _ _ bounded)
      intro tape tapeSupported
      rw [expect_bind_tower_bounded _ _ _ bounded,
        expect_bind_tower_bounded _ _ _ bounded]
      apply expect_le_expect_of_support_order prescribedClean decoded
        (fun response => expect ((app).finish initial horizon
          (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
            cleanPlayers (some ⟨control.remaining, none,
              control.execution.respond app who response⟩)) (fun state => payoff state who))
        (fun response => expect ((app).finish initial horizon
          (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
            cleanPlayers (some ⟨control.remaining, none,
              control.execution.respond app who response⟩)) (fun state => payoff state who))
        (payoffIntegrable_of_bounded _ _
          (fun _ => expect_abs_le_of_bounded nonnegative bounded))
        (payoffIntegrable_of_bounded _ _
          (fun _ => expect_abs_le_of_bounded nonnegative bounded))
      let family : ReservedEpoch.Tape Player tapeLength → (app).Scheduler :=
        ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime)
      obtain ⟨tapeInPrior, ⟨fixedRawTrace⟩⟩ :=
        (app).schedulerMixture_trace_of_posterior_support prior family initial horizon control
          rawTrace tape tapeSupported
      obtain ⟨fixedTrace⟩ := (menu).trace_of_recorded_actions
        (PhaseCount.silence_onePacket runtime leaks bounds) initial horizon (family tape) control
          fixedRawTrace (by
            intro owner earlier entry later recorded
            obtain ⟨before, _prior, _kept, _acting, _past, viewed, permitted⟩ :=
              (menu).recorded_response_at initial horizon scheduler control counted owner earlier
                entry later recorded
            rwa [← viewed] at permitted)
      have fixedCallback : ((menu).protocol initial horizon (family tape)).Trace
          (some ⟨control.remaining, some who, control.execution⟩) := by
        simpa only [← active] using fixedTrace
      intro leftResponse leftSupported rightResponse rightSupported
      have leftAvailable := phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds
        plan values who _ _ leftResponse leftSupported
      have rightAvailable : rightResponse ∈ (menu).actions who
          (control.execution.recall who) (control.execution.observe app who) := by
        obtain ⟨chosen, _positive, sameResponse⟩ := PMF.support_map .. ▸ rightSupported
        have permitted := chosen.property
        simp only [information] at permitted
        obtain ⟨actualResponse, offered, actualEq⟩ := permitted
        have same : actualResponse = rightResponse := by
          simpa only [actualEq, Option.getD_some] using sameResponse
        rw [← same, recalled, observed]
        exact offered
      rcases ownAlternative with ownGlobal | ownFailed
      swap
      · have debt : PhaseCheckpointDebt setup mode plan who
            control.execution.application := ⟨witness, Or.inr (Or.inr ownFailed)⟩
        have fixed := phaseProposal_checkpoint_debt_finish_payoff setup mode runtime leaks bounds
          plan maximal cleanPlayers tape control.remaining who control.execution fixedCallback debt
            rightResponse utility excludedPayoff
        rw [fixed]
        exact expectedFloor _ id
      have ownProper : witness.checkpoint.source.BindingsHoldValues who :=
        (ProtocolState.bindingsHoldValues_entry who witness.checkpoint.residual.tail _).mp
          ((witness.checkpoint.origin.bindingsHoldValues_lift who _).mp ownGlobal)
      have proper : ∀ owner, owner ∉ control.execution.application.current.excluded →
          witness.checkpoint.source.BindingsHoldValues owner := by
        intro owner survives
        by_cases same : owner = who
        · subst owner; exact ownProper
        · exact witness.checkpoint.bindingsHoldValues_of_no_generated_unusable setup mode
            wellFormed runtime leaks bounds plan horizon scheduler control counted owner survives
              (fun generated => foreignBad
                ⟨owner, (fun equal => same equal.symm),
                  (congrArg (fun earlier : (E).History =>
                    PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds
                      initial horizon scheduler owner earlier) actualHistory).mp generated⟩)
      obtain ⟨phase, installed, inside⟩ := request.2.1
      have kind : phase.kind = .reveal := by
        have fields := phase.fields event ((phase.mem_events event).mp inside).1
          ((phase.mem_events event).mp inside).2
        cases phaseKind : phase.kind <;>
          simp only [phaseKind, publication] at fields
        · obtain ⟨owner, ty, impossible⟩ := fields; cases impossible
        · rfl
        · obtain ⟨ty, impossible⟩ := fields; cases impossible
      obtain ⟨rowPayload, name, selected, checks, output, code, value, locked⟩ :=
        witness.checkpoint.publication_binding_row setup mode phase installed kind witness.stored
          event inside who request.2.2.2.1 ownProper
      have boundedValue : (⟨rowPayload, value⟩ : Raw L) ∈ bounds.values := by
        have coveredValue := covered event
        rw [output] at coveredValue
        exact coveredValue value
      obtain ⟨candidate, leftMaterial, accepted, transmitted, leftCall⟩ :=
        phaseProposalUnflaggedOpening_supported_truthful setup mode runtime leaks bounds plan
          values (setup.initialLaw.map encodeInputs) horizon (family tape) control.remaining who
            control.execution fixedCallback event rowPayload (witness.checkpoint.refs.get selected)
              checks output code (nodeView_eq_resolve output code) request unsent value locked
                boundedValue leftResponse leftSupported
      have leftEq : leftResponse = ⟨some leftMaterial⟩ := by
        cases leftResponse
        cases transmitted
        rfl
      subst leftResponse
      let leftResponse : (app).Action := ⟨some leftMaterial⟩
      by_cases rightSilent : rightResponse = ⟨none⟩
      swap
      · cases rightTransmission : rightResponse.transmission with
        | none =>
            cases rightResponse
            cases rightTransmission
            exact (rightSilent rfl).elim
        | some rightMaterial =>
            have rightEq : rightResponse = ⟨some rightMaterial⟩ := by
              cases rightResponse
              cases rightTransmission
              rfl
            subst rightResponse
            have same := phaseProposal_opening_alias_finish_payoff_eq setup mode runtime leaks
              bounds plan values (setup.initialLaw.map encodeInputs) horizon (family tape)
                control.remaining who
                control.execution fixedCallback event rowPayload
                  (witness.checkpoint.refs.get selected) checks output code
                    (nodeView_eq_resolve output code) request leftMaterial rightMaterial
                      leftAvailable rightAvailable utility excludedPayoff
            have expected := congrArg (fun distribution => expect distribution id) same
            exact le_of_eq (by simpa only [expect_map, Function.comp_def, id_eq]
              using expected.symm)
      subst rightResponse
      let rightResponse : (app).Action := ⟨none⟩
      have pairing := phaseProposalUnflagged_paired_publication_boundary setup mode runtime
        leaks bounds plan covered maximal values tape activationGap processingGap
          (gaps tape tapeInPrior) margin control.remaining control.execution who leftMaterial
            fixedCallback leftAvailable phase installed kind witness.checkpoint proper
      let leftTrace := pairing.choose
      let rightTrace := pairing.choose_spec.choose
      let stopped := fun response
          (history : ((menu).protocol initial horizon (family tape)).History) =>
        match history.state with
        | none => False
        | some ending => ending.execution.application.attempt ≠
            (control.execution.respond app who response).application.attempt
      have ordered := publication_stopped_pair_payoff_le setup mode runtime leaks bounds plan
        complete covered maximal values fullValues tape activationGap processingGap
          (gaps tape tapeInPrior) margin capacity utility excludedPayoff who bound
            bounded floor control.remaining control.execution fixedCallback phase installed kind
              witness archive leftMaterial pairing stopped (by
                intro response history
                dsimp only [stopped]
                cases history.state <;> rfl)
      exact publication_finish_le_of_stopped setup mode runtime leaks bounds plan values
        (family tape) control.remaining (control.execution.respond app who ⟨some leftMaterial⟩)
          (control.execution.respond app who ⟨none⟩) leftTrace rightTrace
            (stopped ⟨some leftMaterial⟩) (stopped ⟨none⟩) (fun state => payoff state who)
              bound nonnegative bounded ordered
    let noisyValue := fun (responses : PMF (app).Action) =>
      expect ((responses.bind kernel).bind fun next =>
      (N).runBehavioralTerminalFrom certificate assessment.strategy next)
        (fun final => payoff final.state who)
    let referenceNoisy := phaseProposalReferencePolicy setup mode runtime leaks bounds plan
      values rates who (control.execution.recall who) (control.execution.observe app who)
    have callbackCurrent : history.val.state =
        some ⟨control.remaining, some who, control.execution⟩ := by
      simpa only [← active] using current
    have enough : (app).rank horizon history.val.state ≤ 2 * horizon + 1 := by
      have depth := (app).trace_bound initial horizon scheduler rawTrace
      rw [current]
      omega
    have responseValue (lottery : PMF ((N).Choice who site.1)) :
        expect ((N).runBehavioralTerminalFrom certificate
          (Profile.update (sig := (N).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 lottery)) history.val)
              (fun final => payoff final.state who) =
          noisyValue (lottery.map fun choice => choice.1.getD ⟨none⟩) := by
      let responses := lottery.map (fun choice => choice.1.getD ⟨none⟩)
      let updated := Profile.update (sig := (N).behavioralSignature) assessment.strategy who
        ((assessment.strategy who).withLaw site.1 lottery)
      have direct := (menu).run_local_law_finish_of_information initial horizon scheduler
        assessment.strategy history.val who control.remaining control.execution callbackCurrent
          site.1 history.property lottery (2 * horizon) enough
      have kernelLaw :
          (((responses.bind kernel).bind fun next =>
            (N).runBehavioralTerminalFrom certificate assessment.strategy next).map History.state) =
          responses.bind (fun response => (app).finish initial horizon scheduler
            ((menu).decodeProfile initial horizon scheduler assessment.strategy)
              (some ⟨control.remaining, none, control.execution.respond app who response⟩)) := by
        rw [PMF.bind_bind, PMF.map_bind]
        apply bind_congr_on_support
        intro response supported
        have nextState := responseStates updated response (by
          rwa [localDecoded assessment.strategy lottery])
        exact phaseProposal_response_kernel_finish setup mode runtime leaks bounds plan prior
          assessment.strategy kernel control.remaining who control.execution response nextState
      have equality :
          ((N).runBehavioralTerminalFrom certificate updated history.val).map History.state =
          (((responses.bind kernel).bind fun next =>
            (N).runBehavioralTerminalFrom certificate assessment.strategy next).map
              History.state) := by
        rw [(N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
          ((menu).bounded initial horizon scheduler), direct, kernelLaw]
        rfl
      have expected := congrArg
        (fun distribution => expect distribution (fun state => payoff state who)) equality
      simpa only [expect_map, Function.comp_def] using expected
    have noisyDecoded : (menu).decodeProfile initial horizon scheduler assessment.strategy =
        phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates := by
      rw [prescribed]
      funext owner
      exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler owner _
        (phaseProposalReferencePolicy_covered setup mode runtime leaks bounds plan values rates
          owner)
    have referenceRaw : ((assessment.strategy who site.1).map
        (fun choice => choice.1.getD ⟨none⟩)) = referenceNoisy := by
      have decoded := localDecoded assessment.strategy (assessment.strategy who site.1)
      rw [InformationModel.BehavioralPolicy.withLaw_eq_self,
        Profile.update_eq_self, noisyDecoded] at decoded
      exact decoded.symm
    have prescribedValue := responseValue (assessment.strategy who site.1)
    rw [InformationModel.BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self,
      referenceRaw] at prescribedValue
    have historyEquation : (N).historyGain ((N).runBehavioralTerminalFrom certificate)
        (fun final => final.state) payoff assessment deviation history =
          noisyValue decoded - noisyValue referenceNoisy := by
      simp only [InformationModel.historyGain, deviation, expect_map, Function.comp_def,
        Profile.update_eq_self]
      rw [responseValue law, prescribedValue]
    have noisyDifference := flagError decoded
    rw [← prescribed] at noisyDifference
    change (noisyValue decoded - noisyValue referenceNoisy) -
      (cleanValue decoded - cleanValue prescribedClean) ≤ error at noisyDifference
    rw [historyEquation]
    linarith [cleanComparison, noisyDifference]
  rw [presentation,
    (N).gain_eq_expect_historyGain]
  calc
    _ ≤ expect (assessment.belief who site)
        (fun history => (if bad history then 2 * bound else 0) + error) :=
      expect_mono (fun history _ => histories history)
        (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    _ = _ := by
      have indicator : expect (assessment.belief who site)
          (fun history => if bad history then 2 * bound else 0) =
            (2 * bound) * foreignPosterior := by
        rw [expect_eq_sum]
        dsimp only [foreignPosterior]
        rw [Finset.mul_sum]
        simp only [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro history _
        by_cases failed : bad history
        all_goals
          dsimp only [bad] at failed ⊢
          simp only [failed, ite_true, ite_false, mul_zero] <;> ring
      rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
        expect_constant, indicator]
      dsimp only [error]
      ring

end Vegas
