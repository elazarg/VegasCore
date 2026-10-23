/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOriginalResetPayoff
import Vegas.Game.PhaseProposalStandingBindingDebt
import Vegas.Game.PhaseProposalNativeFutureFlags
import Vegas.Game.PhaseProposalObservableDebtPayoff
import Vegas.Game.PhaseProposalUnflaggedBinding
import Vegas.Pending.PhaseSentMenu
import Interaction.ReactiveAnchoredStopped
import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Current binding debt and foreign reset at the original full information -/

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

/-- The current response retains the original callback posterior. The raw
current lottery is arbitrary and is commuted with that SAME posterior. -/
theorem phaseProposal_current_finish_seed_marginal
    (players : Player → (app).Policy) (remaining : Nat) (who : Player)
    (execution : (app).Execution) (responses : PMF (app).Action) :
    (responses.bind fun response => (app).finish initial horizon scheduler players
        (some ⟨remaining, none, execution.respond app who response⟩)) =
      (((app).schedulerMixture prior
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime))).posterior
          execution.environmentRecall).bind fun tape =>
            responses.bind fun response =>
              (app).finish initial horizon
                (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
                  players (some ⟨remaining, none, execution.respond app who response⟩) := by
  let family : ReservedEpoch.Tape Player tapeLength → (app).Scheduler :=
    ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime)
  let posterior := ((app).schedulerMixture prior family).posterior execution.environmentRecall
  calc
    _ = responses.bind (fun response => posterior.bind fun tape =>
        (app).finish initial horizon (family tape) players
          (some ⟨remaining, none, execution.respond app who response⟩)) := by
      apply bind_congr_on_support
      intro response _
      simpa only [posterior, family, ReservedEpoch.implementation,
        ReactiveApplication.respond_environmentRecall] using
        ((app).schedulerMixture_finish_marginal prior family initial horizon players
          (some ⟨remaining, none, execution.respond app who response⟩)).symm
    _ = _ := PMF.bind_comm responses posterior _

/-- The full-history response kernel retains its actual physical continuation.
Every policy and the exact original scheduler remain literal. -/
theorem phaseProposal_response_kernel_finish
    (profile : ∀ owner, (N).BehavioralPolicy owner)
    (kernel : (app).Action → PMF (E).History)
    (remaining : Nat) (who : Player) (execution : (app).Execution)
    (response : (app).Action)
    (stateLaw : (kernel response).map History.state =
      PMF.pure (some ⟨remaining, none, execution.respond app who response⟩)) :
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    ((kernel response).bind fun history =>
      (N).runBehavioralTerminalFrom certificate profile history).map History.state =
      (app).finish initial horizon scheduler
        ((menu).decodeProfile initial horizon scheduler profile)
        (some ⟨remaining, none, execution.respond app who response⟩) := by
  intro certificate
  rw [PMF.map_bind]
  calc
    _ = (kernel response).bind (fun history =>
        (app).finish initial horizon scheduler
          ((menu).decodeProfile initial horizon scheduler profile) history.state) :=
      bind_congr_on_support _ (fun history _ =>
        (menu).terminal_run_eq_finish initial horizon scheduler certificate profile history)
    _ = ((kernel response).map History.state).bind
        ((app).finish initial horizon scheduler
          ((menu).decodeProfile initial horizon scheduler profile)) :=
      (PMF.bind_map (kernel response) History.state
        ((app).finish initial horizon scheduler
          ((menu).decodeProfile initial horizon scheduler profile))).symm
    _ = _ := by rw [stateLaw, PMF.pure_bind]

open Classical in
/-- Every current menu atom is literal. Saved debt is split before the fresh
properness gate; the two continuations keep their original scheduler posterior. -/
theorem phaseProposal_current_binding_gain_le
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
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (requested : PhaseRuntimeState.requests view.application.2 who
      ⟨view.application.2.attempt, event⟩)
    (branch :
      phaseProposalSavedBindingFailure setup mode runtime leaks who event view ∨
      phaseProposalCurrentBindingFailure setup mode runtime leaks who event view ∨
      (view.application.2.excluded \
        ((view.application.2.retired.map fun record =>
            record.2.sourceFailureFootprint.2).foldr (fun first rest => first ∪ rest) ∅ ∪
          view.application.2.native.sourceFailureFootprint.1
            view.application.2.attempt.phase)).Nonempty)
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
  by_cases saved : phaseProposalSavedBindingFailure setup mode runtime leaks who event view
  · have fixed := phaseProposalSavedBindingFailure_gain_eq_zero setup mode runtime leaks bounds
      plan maximal prior certificate assessment deviation past view information event payload
        binding requested saved utility excludedPayoff
    -- Exact full-terminal/truncated presentation, using the existing bounded horizon.
    rw [presentation, fixed]
    positivity
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
    have counted : (E).Trace (some control) := current ▸ history.val.trace
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
          (⟨some control, current ▸ history.val.trace⟩ : (E).History) = history.val := by
        rcases history with ⟨⟨state, trace⟩, _atInfo⟩
        cases current
        rfl
      have proper := witness.bindingsHoldValues_of_no_saved_failure_and_foreign_good setup mode
        wellFormed runtime leaks bounds plan maximal horizon scheduler control
          (current ▸ history.val.trace) who event payload binding request
            (by simpa only [observed] using saved)
              (fun owner different _survives generated =>
                foreignBad ⟨owner, different.symm, actualHistory ▸ generated⟩)
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
      obtain ⟨phase, remaining, installed, kind, inside⟩ := phase_ready_binding_phase runtime leaks
        plan (serviceGraph_revealRelaxedOrdered setup mode) maximal
          (setup.initialLaw.map encodeInputs)
          horizon (family tape) fixedRawTrace who event payload binding request.2.2.1
      intro leftResponse leftSupported rightResponse rightSupported
      obtain ⟨_material, _value, transmitted, _typed⟩ :=
        phaseProposalUnflaggedBinding_supported_usable setup mode runtime leaks bounds plan
          complete covered maximal values fullValues horizon (family tape) capacity
            control.remaining
            who control.execution (sameInitial ▸ fixedCallback) event payload binding request unsent
              leftResponse leftSupported
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
      obtain ⟨leftTrace, rightTrace, leftResponsePrefix, rightResponsePrefix, closed⟩ :=
        phaseProposalUnflagged_available_send_reset_boundary setup mode runtime leaks bounds
          plan complete covered maximal (serviceGraph_revealRelaxedOrdered setup mode)
            values fullValues tape activationGap processingGap
              (gaps tape tapeInPrior)
                margin capacity control.remaining control.execution who leftResponse rightResponse
                  fixedCallback
                    (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan
                      values who _ _ leftResponse leftSupported)
                    rightAvailable
                    (fun silent => by rw [silent] at transmitted; cases transmitted)
                    phase (by simp only [installed, List.head?_cons, Option.mem_some_iff])
                    kind witness.checkpoint
      -- Existing terminal-from-until identity retains the two FULL original
      -- histories; product support lets us compare every stopped pair.
      let fixedModel := (menu).information initial horizon (family tape)
      let fixedCertificate := ((menu).bounded initial horizon (family tape)).wellFoundedHistories
      let responseAnchor := fun response : (app).Action =>
        control.execution.respond app who response
      let responseProfile := fun response owner => (menu).restrictPolicy initial horizon
        (family tape) owner (ReactiveApplication.anchoredPolicy (responseAnchor response)
          cleanPlayers owner)
      let stopped := fun response
          (history : ((menu).protocol initial horizon (family tape)).History) =>
        match history.state with
        | none => False
        | some ending => ending.execution.application.attempt ≠
            (responseAnchor response).application.attempt
      have terminalValue (response : (app).Action)
          (trace : ((menu).protocol initial horizon (family tape)).Trace
            (some ⟨control.remaining, none, responseAnchor response⟩)) :
          expect ((app).finish initial horizon (family tape) cleanPlayers
            (some ⟨control.remaining, none, responseAnchor response⟩))
              (fun state => payoff state who) =
          expect (fixedModel.runBehavioralTerminalFrom fixedCertificate (responseProfile response)
            ⟨some ⟨control.remaining, none, responseAnchor response⟩, trace⟩)
              (fun final => payoff final.state who) := by
        let physical := ReactiveApplication.anchoredPolicy (responseAnchor response) cleanPlayers
        have decodedProfile : (menu).decodeProfile initial horizon (family tape)
            (responseProfile response) = physical := by
          funext owner
          apply (menu).decode_restrictPolicy_of_covered initial horizon (family tape) owner
          intro past view action supported
          exact (menu).anchoredPolicy_covered initial horizon (family tape)
            ⟨control.remaining, none, responseAnchor response⟩ trace cleanPlayers owner
              (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan
                values owner)
                past view action supported
        have physicalLaw := (menu).terminal_run_eq_finish initial horizon (family tape)
          fixedCertificate (responseProfile response)
            ⟨some ⟨control.remaining, none, responseAnchor response⟩, trace⟩
        rw [decodedProfile] at physicalLaw
        have sameFinish : (app).finish initial horizon (family tape) physical
            (some ⟨control.remaining, none, responseAnchor response⟩) =
            (app).finish initial horizon (family tape) cleanPlayers
              (some ⟨control.remaining, none, responseAnchor response⟩) := by
          simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind,
            physical, ReactiveApplication.runRounds_anchoredPolicy]
        rw [sameFinish] at physicalLaw
        rw [← physicalLaw, expect_map]
        rfl
      rw [terminalValue rightResponse rightTrace, terminalValue leftResponse leftTrace,
        fixedModel.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil fixedCertificate
          (responseProfile rightResponse) (stopped rightResponse),
        fixedModel.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil fixedCertificate
          (responseProfile leftResponse) (stopped leftResponse)]
      erw [expect_bind_tower_bounded _ _ _
        (fun final : ((menu).protocol initial horizon (family tape)).History =>
          bounded final.state),
        expect_bind_tower_bounded _ _ _
          (fun final : ((menu).protocol initial horizon (family tape)).History =>
            bounded final.state)]
      let terminalPayoff : ((menu).protocol initial horizon (family tape)).History → ℝ :=
        fun final => payoff final.state who
      let leftStopped := fixedModel.runBehavioralUntil fixedCertificate
        (responseProfile leftResponse) (stopped leftResponse)
          ⟨some ⟨control.remaining, none, responseAnchor leftResponse⟩, leftTrace⟩
      let rightStopped := fixedModel.runBehavioralUntil fixedCertificate
        (responseProfile rightResponse) (stopped rightResponse)
          ⟨some ⟨control.remaining, none, responseAnchor rightResponse⟩, rightTrace⟩
      refine expect_le_expect_of_support_order leftStopped rightStopped
        (fun history => expect (fixedModel.runBehavioralTerminalFrom fixedCertificate
          (responseProfile leftResponse) history) terminalPayoff)
        (fun history => expect (fixedModel.runBehavioralTerminalFrom fixedCertificate
          (responseProfile rightResponse) history) terminalPayoff)
        (payoffIntegrable_of_bounded _ _ (fun _ =>
          expect_abs_le_of_bounded nonnegative
            (fun final : ((menu).protocol initial horizon (family tape)).History =>
              bounded final.state)))
        (payoffIntegrable_of_bounded _ _ (fun _ =>
          expect_abs_le_of_bounded nonnegative
            (fun final : ((menu).protocol initial horizon (family tape)).History =>
              bounded final.state))) ?_
      intro leftFinal leftReached rightFinal rightReached
      obtain ⟨leftEnding, rightEnding, leftBefore, rightBefore, leftPrior, rightPrior,
        leftJoint, rightJoint, leftLegal, rightLegal, leftRealized, rightRealized,
        leftRaw, rightRaw, leftState, rightState, leftPrefix, rightPrefix,
        leftEndPrefix, rightEndPrefix, leftSame, rightSame, leftEffect, rightEffect,
        _leftHead, _rightHead, leftFinished, rightFinished, leftIdle, rightIdle,
        leftChanged, rightChanged, leftNormalized, rightNormalized,
        _leftCoverage, _rightCoverage, leftExcluded, rightExcluded, archiveEq,
        _leftAcceptance, _rightAcceptance, _foreignAcceptance, survival⟩ :=
          closed leftFinal (by
            first
            | exact leftReached
            | convert leftReached using 1
              apply congrArg (fun distribution :
                PMF ((menu).protocol initial horizon (family tape)).History => distribution.support)
              apply congrArg (fun stop => fixedModel.runBehavioralUntil fixedCertificate
                (responseProfile leftResponse) stop
                  ⟨some ⟨control.remaining, none, responseAnchor leftResponse⟩, leftTrace⟩)
              funext history
              dsimp only [stopped]
              cases history.state <;> rfl)
            rightFinal (by
              first
              | exact rightReached
              | convert rightReached using 1
                apply congrArg (fun distribution :
                  PMF ((menu).protocol initial horizon (family tape)).History =>
                    distribution.support)
                apply congrArg (fun stop => fixedModel.runBehavioralUntil fixedCertificate
                  (responseProfile rightResponse) stop
                    ⟨some ⟨control.remaining, none, responseAnchor rightResponse⟩, rightTrace⟩)
                funext history
                dsimp only [stopped]
                cases history.state <;> rfl)
      by_cases excluded : who ∈ rightEnding.execution.application.current.excluded
      · have fixed := phase_excluded_expected_payoff setup mode runtime leaks utility
          excludedPayoff menu initial horizon (family tape)
            ((menu).bounded initial horizon (family tape)).wellFoundedHistories
              (responseProfile rightResponse) who rightFinal
                (by simpa only [PhaseExcluded, rightState] using excluded)
        rw [fixed]
        exact expectedFloor _
          (fun final : ((menu).protocol initial horizon (family tape)).History => final.state)
      obtain ⟨leftSurvives, _rightAccepted, _leftAccepted, _footprintEq, excludedEq,
        _retiredEq, resetSources⟩ := survival excluded
      let anchor : (app).Control := ⟨control.remaining, some who, control.execution⟩
      let before : Bool → (app).Control := fun side =>
        match side with | false => leftBefore | true => rightBefore
      let ending : Bool → (app).Control := fun side =>
        match side with | false => leftEnding | true => rightEnding
      let raw : Bool → RecoveryState (serviceGraph setup mode) := fun side =>
        match side with | false => leftRaw | true => rightRaw
      let priors : ∀ side, ((menu).protocol initial horizon (family tape)).Trace
          (some (before side)) := fun side =>
        match side with | false => leftPrior | true => rightPrior
      let traces : ∀ side, ((menu).protocol initial horizon (family tape)).Trace
          (some (ending side)) := fun side =>
        match side with
        | false => leftState ▸ leftFinal.trace
        | true => rightState ▸ rightFinal.trace
      have kept : ∀ side, TracePrefix fixedCallback (priors side) := by
        intro side; cases side
        · exact leftResponsePrefix.trans leftPrefix
        · exact rightResponsePrefix.trans rightPrefix
      have same : ∀ side, (before side).execution.application.attempt =
          anchor.execution.application.attempt := by
        intro side; cases side
        · exact leftSame
        · exact rightSame
      have idle : ∀ side, (ending side).actor = none := by
        intro side; cases side
        · exact leftIdle
        · exact rightIdle
      have changed : ∀ side, (ending side).execution.application.attempt ≠
          (before side).execution.application.attempt := by
        intro side; cases side
        · exact fun equal => leftChanged (equal.trans leftSame)
        · exact fun equal => rightChanged (equal.trans rightSame)
      have effects : ∀ side, PhaseClosingEffect runtime leaks (before side).execution
          (ending side).execution (raw side) := by
        intro side; cases side
        · exact leftEffect
        · exact rightEffect
      have normalized : ∀ side, (ending side).execution.application =
          ({ (before side).execution.application with current := raw side } :
            PhaseRuntimeState (serviceGraph setup mode)).normalize := by
        intro side; cases side
        · exact leftNormalized
        · exact rightNormalized
      have finished : ∀ side, phase.Finished (phase.drain (raw side)) := by
        intro side; cases side
        · exact leftFinished
        · exact rightFinished
      have initialized : ∀ state ∈ (initial).support, state.Ordered := by
        intro state supported
        obtain ⟨draw, _member, rfl⟩ := PMF.support_map .. ▸ supported
        exact PhaseRuntimeState.initial_ordered plan draw
      have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
        (family tape) initialized ((menu).toRawTrace initial horizon (family tape) fixedCallback)
      have entries : ∀ side, (before side).execution.application.entry =
          anchor.execution.application.entry := by
        intro side
        exact ((phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
          (family tape) anchor (before side) fixedCallback (priors side) (kept side)
            anchorOrdered).2.2 (same side).symm).symm
      have beforeInstalled : ∀ side,
          (before side).execution.application.phases = phase :: remaining := by
        intro side
        exact ((phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds
          plan horizon (family tape) anchor (before side) fixedCallback (priors side)
            (kept side) (same side).symm).1).trans installed
      have inherited : ∀ side, anchor.execution.application.current.excluded ⊆
          (ending side).execution.application.current.excluded := by
        intro side owner member
        let invariant : (app).Invariant (fun state => owner ∈ state.current.excluded) :=
          { submit := fun state player material present =>
              (phaseApplication_exclusion_monotone runtime leaks).submit state player material
                present
            handle := fun state message next present accepted =>
              (phaseApplication_exclusion_monotone runtime leaks).handle state message next
                accepted present
            environment := fun state command next present supported =>
              (phaseApplication_exclusion_monotone runtime leaks).environment state command next
                supported present }
        have atBefore := invariant.tracePrefix menu initial horizon (family tape) anchor
          (before side) fixedCallback (priors side) (kept side) member
        cases side
        · exact (phaseApplication_exclusion_monotone runtime leaks).transition initial horizon
            (family tape) leftBefore leftEnding leftJoint leftRealized atBefore
        · exact (phaseApplication_exclusion_monotone runtime leaks).transition initial horizon
            (family tape) rightBefore rightEnding rightJoint rightRealized atBefore
      have owned : who ∈ phase.owners := by
        exact Finset.mem_biUnion.mpr ⟨event, inside,
          by simpa only [Option.mem_toFinset, Option.mem_def] using request.2.2.2.1⟩
      have survivors : ∀ side, (phase.owners \ (phase.drain (raw side)).excluded).Nonempty := by
        intro side
        refine ⟨who, Finset.mem_sdiff.mpr ⟨owned, ?_⟩⟩
        cases side
        · rwa [leftExcluded]
        · rwa [rightExcluded]
      by_cases reset : ((phase.drain rightRaw).excluded \
          anchor.execution.application.entry.excluded).Nonempty
      · have missed : ∀ side, (((phase.drain (raw side)).excluded \
            (before side).execution.application.entry.excluded) ∩ phase.owners).Nonempty := by
          intro side
          obtain ⟨_native, _binding, receipts, _stored, _remembered, _coverage⟩ :=
            phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon
              (family tape) (before side) (ending side) (priors side) (raw side)
                (effects side) (changed side)
          have failure : ((phase.drain (raw side)).excluded \
              (before side).execution.application.entry.excluded).Nonempty := by
            rw [entries side]
            cases side
            · rwa [excludedEq]
            · exact reset
          obtain ⟨owner, member⟩ := failure
          have activeOwner := (Finset.mem_sdiff.mp member).2
          have record := (receipts.exclusion.installed phase (by
            simp only [beforeInstalled side, List.head?_cons,
              Option.mem_some_iff])).phase_drain phase
          rcases (record.excluded owner).mp (Finset.mem_sdiff.mp member).1 with
            old | ⟨failedEvent, lower, acting, failed⟩
          · exact (activeOwner old).elim
          · have within := receipts.exclusion.frontier.positioned
            change PhaseRuntimeState.Positioned _ _ _ at within
            rw [show ({ (before side).execution.application with current := raw side } :
              PhaseRuntimeState (serviceGraph setup mode)).phases = phase :: remaining from
                beforeInstalled side] at within
            have upper := (phase.drain_within (raw side) within.2).2 failedEvent failed.completed
            exact ⟨owner, Finset.mem_inter.mpr ⟨member,
              Finset.mem_biUnion.mpr ⟨failedEvent,
                (phase.mem_events failedEvent).mpr ⟨lower, upper⟩,
                by simpa only [Option.mem_toFinset, Option.mem_def] using acting⟩⟩⟩
        have paired := resetSources reset
        have samePayoff := phaseProposal_original_reset_payoff_law_eq setup mode runtime leaks
          bounds plan complete covered maximal values fullValues tape activationGap processingGap
            (gaps tape tapeInPrior) margin capacity
              utility excludedPayoff anchor fixedCallback
                witness archive proper
                phase remaining installed kind before ending priors traces kept same idle changed
                  raw effects normalized finished missed survivors inherited archiveEq paired who
        let responses : Bool → (app).Action := fun side =>
          match side with | false => leftResponse | true => rightResponse
        let responseTraces : ∀ side, ((menu).protocol initial horizon (family tape)).Trace
            (some ⟨control.remaining, none, responseAnchor (responses side)⟩) := fun side =>
          match side with | false => leftTrace | true => rightTrace
        let finals : Bool → ((menu).protocol initial horizon (family tape)).History := fun side =>
          match side with | false => leftFinal | true => rightFinal
        let endpointProfile := fun side owner => (menu).restrictPolicy initial horizon
          (family tape) owner (ReactiveApplication.anchoredPolicy (ending side).execution
            cleanPlayers owner)
        have historiesEq : ∀ side, finals side = ⟨some (ending side), traces side⟩ := by
          intro side; cases side
          · cases leftFinal with
            | mk state trace => cases leftState; rfl
          · cases rightFinal with
            | mk state trace => cases rightState; rfl
        have keptResponses : ∀ side, TracePrefix (responseTraces side) (traces side) := by
          intro side; cases side
          · change TracePrefix leftTrace (leftState ▸ leftFinal.trace)
            cases leftFinal with
            | mk state trace =>
                cases leftState
                exact (TracePrefix.extend leftPrefix leftJoint leftLegal leftRealized).trans
                  leftEndPrefix
          · change TracePrefix rightTrace (rightState ▸ rightFinal.trace)
            cases rightFinal with
            | mk state trace =>
                cases rightState
                exact (TracePrefix.extend rightPrefix rightJoint rightLegal rightRealized).trans
                  rightEndPrefix
        have reanchored : ∀ side,
            fixedModel.runBehavioralTerminalFrom fixedCertificate (responseProfile (responses side))
                (finals side) =
              fixedModel.runBehavioralTerminalFrom fixedCertificate (endpointProfile side)
                ⟨some (ending side), traces side⟩ := by
          intro side
          rw [historiesEq side]
          apply fixedModel.runBehavioralTerminalFrom_congr fixedCertificate
          intro later reached _running owner
          obtain ⟨fuel, path⟩ := reached
          rcases later with ⟨state, laterTrace⟩
          have observed := (menu).info initial horizon (family tape) owner laterTrace
          change fixedModel.infoOf owner laterTrace = (app).observe owner state at observed
          cases state with
          | none => rw [observed]; rfl
          | some current =>
              by_cases activeOwner : current.actor = some owner
              · have endingPrefix := (app).reaches_recall_prefix initial horizon (family tape)
                  ((menu).reaches_raw initial horizon (family tape) path)
                    (ending side) current rfl rfl owner
                have responsePrefix := (app).reaches_recall_prefix initial horizon (family tape)
                  ((menu).reaches_raw initial horizon (family tape)
                    (keptResponses side).reachesWithin)
                    ⟨control.remaining, none, responseAnchor (responses side)⟩
                      (ending side) rfl rfl owner
                have laws :
                    ReactiveApplication.anchoredPolicy (responseAnchor (responses side))
                        cleanPlayers owner (current.execution.recall owner)
                          (current.execution.observe app owner) =
                      ReactiveApplication.anchoredPolicy (ending side).execution cleanPlayers
                        owner (current.execution.recall owner)
                          (current.execution.observe app owner) := by
                  rw [ReactiveApplication.anchoredPolicy_of_extends _ cleanPlayers owner _ _
                    (responsePrefix.trans endingPrefix),
                    ReactiveApplication.anchoredPolicy_of_extends _ cleanPlayers owner _ _
                      endingPrefix]
                simp only [ReactiveApplication.observe, ite_eq_left activeOwner] at observed
                rw [observed]
                exact (menu).restrictPolicy_eq_of_law_eq initial horizon (family tape) owner
                  _ _ _ _ laws
              · simp only [ReactiveApplication.observe, ite_eq_right activeOwner] at observed
                rw [observed]
                rfl
        have exactLaw := (congrArg
          (PMF.map fun final => payoff final.state who) (reanchored false)).trans
            (samePayoff.trans (congrArg
              (PMF.map fun final => payoff final.state who) (reanchored true)).symm)
        have exactExpectation := congrArg
          (fun distribution : PMF ℝ => expect distribution id) exactLaw
        simpa only [expect_map, Function.comp_def, id_eq] using exactExpectation.symm.le
      · have currentFailed : phaseProposalCurrentBindingFailure setup mode runtime leaks who
            event (control.execution.observe app who) := by
          rcases branch with old | failed | forced
          · exact (saved old).elim
          · simpa only [observed] using failed
          · have savedE := PhaseRuntimeState.saved_excluded_eq_public_failures witness.exclusions
              witness.failures witness.receipts.exclusion.frontier phase remaining installed
            have archivedE :
                (anchor.execution.application.publicView.retired.map fun record =>
                  record.2.sourceFailureFootprint.2).foldr (fun first rest => first ∪ rest) ∅ =
                PhaseRuntimeState.archivedFailureOwners anchor.execution.application.retired := by
              have records := PhaseRuntimeState.sourceRecordFailures_sourceControlRecords
                anchor.execution.application.retired
              simpa only [RuntimePhasePlan.sourceRecordFailures,
                PhaseRuntimeState.sourceControlRecords, PhaseRuntimeState.publicView,
                List.map_map, Function.comp_def, State.sourceFailureFootprint_read,
                State.sourceFailureFootprint] using records
            have publicSaved :
                ((view.application.2.retired.map fun record =>
                    record.2.sourceFailureFootprint.2).foldr (fun first rest => first ∪ rest) ∅ ∪
                  view.application.2.native.sourceFailureFootprint.1
                    view.application.2.attempt.phase) =
                  anchor.execution.application.entry.excluded := by
              rw [← observed]
              dsimp only [ReactiveApplication.Execution.observe, phaseApplication,
                PhaseRuntimeState.playerView]
              rw [archivedE]
              dsimp only [PhaseRuntimeState.publicView]
              rw [State.sourceFailureFootprint_read]
              exact savedE.symm
            have forcedActual : (anchor.execution.application.current.excluded \
                anchor.execution.application.entry.excluded).Nonempty := by
              rw [publicSaved] at forced
              simpa only [← observed, ReactiveApplication.Execution.observe,
                phaseApplication, PhaseRuntimeState.playerView, PhaseRuntimeState.publicView,
                anchor] using forced
            obtain ⟨owner, member⟩ := forcedActual
            apply False.elim
            apply reset
            refine ⟨owner, Finset.mem_sdiff.mpr ⟨?_, (Finset.mem_sdiff.mp member).2⟩⟩
            rw [rightExcluded]
            exact inherited true (Finset.mem_sdiff.mp member).1
        obtain ⟨rightWitness, _rightArchive, _rightHistory, _saved, _checkpointEq⟩ :=
          RecoverySourceWitness.prefix_at_same_attempt setup mode runtime leaks bounds plan maximal
            (family tape) anchor rightBefore fixedCallback rightPrior
              (rightResponsePrefix.trans rightPrefix) rightSame witness archive
        have clean : ¬ (((phase.drain rightRaw).excluded \
            rightBefore.execution.application.entry.excluded) ∩ phase.owners).Nonempty := by
          intro failure
          obtain ⟨owner, member⟩ := failure
          apply reset
          refine ⟨owner, ?_⟩
          simpa only [show rightBefore.execution.application.entry =
            anchor.execution.application.entry from entries true] using
              (Finset.mem_inter.mp member).1
        have debt := phaseProposal_current_binding_failure_checkpointed_at_original_close
          setup mode runtime leaks bounds plan maximal horizon (family tape) anchor rightBefore
            rightEnding fixedCallback rightPrior (rightResponsePrefix.trans rightPrefix)
              rightSame.symm rightWitness phase remaining installed kind
            who event payload binding request currentFailed rightRaw
            rightEffect (changed true) rightFinished clean rightNormalized
              (setup.proposalRecoveryNormalizedTrembledProfile
                0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        have fixed : ∀ profile : ∀ owner,
            ((menu).information initial horizon (family tape)).BehavioralPolicy owner,
            expect (((menu).information initial horizon (family tape)).runBehavioralTerminalFrom
              ((menu).bounded initial horizon (family tape)).wellFoundedHistories profile
                rightFinal)
                (fun final => payoff final.state who) = excludedPayoff who := by
          intro profile
          rw [expect_congr_on_support (g := fun _ => excludedPayoff who)]
          · exact expect_constant _ _
          intro final supported
          let closed : (app).ProtocolState → Prop := fun state =>
            ∃ ending : (app).Control, state = some ending ∧
              PhaseCheckpointDebt setup mode plan who ending.execution.application
          have retained := fixedModel.runBehavioralTerminalFrom_support_closed
              ((menu).bounded initial horizon (family tape)).wellFoundedHistories profile closed
              (fun before joint _ after valid reached => by
                obtain ⟨before, rfl, owed⟩ := valid
                obtain ⟨after, rfl, _recall⟩ := (app).transition_recall_prefix initial horizon
                  (family tape) before after joint reached
                exact ⟨after, rfl, phaseCheckpointDebt_transition setup mode runtime leaks plan
                  maximal initial horizon (family tape) before after joint who owed reached⟩)
              rightFinal ⟨rightEnding, rightState, debt⟩ final supported
          obtain ⟨finalControl, finalState, owed⟩ := retained
          have terminal := fixedModel.runBehavioralTerminalFrom_support_terminal
              ((menu).bounded initial horizon (family tape)).wellFoundedHistories profile
                rightFinal final supported
          have rawFinal := (menu).toRawTrace initial horizon (family tape)
            (finalState ▸ final.trace)
          have finished := (ReservedEpoch.terminal_history_complete runtime leaks tape plan
            (serviceGraph_revealRelaxedOrdered setup mode) maximal
              (setup.initialLaw.map encodeInputs)
              finalControl rawFinal (finalState ▸ terminal)).1
          rw [finalState]
          exact phaseExclusionBase_of_excluded setup mode runtime leaks utility excludedPayoff
            finalControl who (phaseCheckpointDebt_excluded_of_finished setup mode runtime leaks
              plan (setup.initialLaw.map encodeInputs) horizon (family tape) finalControl rawFinal
                finished who owed)
        rw [fixed]
        exact expectedFloor _
          (fun final : ((menu).protocol initial horizon (family tape)).History => final.state)
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
