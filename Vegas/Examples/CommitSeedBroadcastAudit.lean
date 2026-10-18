/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastRuntime
import Vegas.Game.PhaseOnePacketExtension
import Vegas.Game.PhaseExclusionPayoff
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveLocalContinuation
import Interaction.ReactiveMenuContinuation
import GameTheory.Analysis.Protocol.SupportedChoices

/-! # Certain count collection and full-input clean-owner incentives -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

abbrev rawProtocol := rawMenu.protocol initial horizon scheduler
abbrev rawModel := rawMenu.information initial horizon scheduler
abbrev countedProtocol := countedMenu.protocol initial horizon scheduler
abbrev countedModel := countedMenu.information initial horizon scheduler

theorem countedInRaw : countedMenu.IncludedIn rawMenu :=
  PhaseCount.onePacketMenu_in_raw runtime leaks bounds

theorem canonicalCertificate : rawProtocol.WellFoundedHistories :=
  (rawMenu.bounded initial horizon scheduler).wellFoundedHistories

/-- All signed evidence is observed and included at settlement. -/
def evidenceService : EvidenceReportService (PhaseCount.Evidence graph) where
  window := ⟨0, 0, 0, by omega⟩
  observations := PMF.pure
  reports := fun observed => PMF.pure (observed.map fun evidence => ⟨evidence, 0, 0⟩)
  observations_authentic := by
    intro actual observed supported
    cases (PMF.mem_support_pure_iff _ _).mp supported
    exact List.Subset.refl _
  reports_authentic := by
    intro observed delivered supported report member
    cases (PMF.mem_support_pure_iff _ _).mp supported
    obtain ⟨evidence, present, rfl⟩ := List.mem_map.mp member
    exact present
  reports_timelySubmitted := by
    intro observed delivered supported report member
    cases (PMF.mem_support_pure_iff _ _).mp supported
    obtain ⟨evidence, _, rfl⟩ := List.mem_map.mp member
    exact ⟨le_rfl, le_rfl⟩

theorem evidenceService_sample (actual : List (PhaseCount.Evidence graph)) :
    evidenceService.sample actual = PMF.pure actual := by
  classical
  simp only [EvidenceReportService.sample, evidenceService, PMF.pure_bind, PMF.pure_map]
  congr 1
  induction actual with
  | nil => rfl
  | cons first rest ih =>
      simpa [EvidenceReport.deliveredEvidence] using congrArg (first :: ·) ih

theorem evidenceService_coverage :
    PhaseCount.EvidenceCoverage evidenceService (fun _ => 1) (fun _ => 1) := by
  classical
  intro actual report member _
  constructor
  · simp [evidenceService, PMF.toOuterMeasure_pure_apply, member]
  · intro seen supported present
    cases (PMF.mem_support_pure_iff _ _).mp supported
    have delivered : report ∈ EvidenceReport.deliveredEvidence 0
        (actual.map fun evidence => (⟨evidence, 0, 0⟩ : EvidenceReport _)) := by
      rcases report with ⟨left, right⟩
      simpa [EvidenceReport.deliveredEvidence, List.map_map, Function.comp_def] using
        (show ∃ a b, (a, b) ∈ actual ∧ (a, b) = (left, right) from
          ⟨left, right, present, rfl⟩)
    simp [evidenceService, PMF.toOuterMeasure_pure_apply, delivered]

def audit : List app.TrafficRecord → PMF (Player → Bool) :=
  PhaseCount.audit runtime leaks evidenceService.sample

def basePayoff : app.ProtocolState → Player → ℝ :=
  phaseExclusionBase setup .concurrentReveals runtime leaks utility excludedPayoff

def netPayoff : app.ProtocolState → Player → ℝ :=
  TerminalAudit.utility basePayoff app.stateTraffic audit deposit

def rawPayoff (who : Player) (history : rawProtocol.History) : ℝ :=
  netPayoff history.state who

theorem basePayoff_mem_Icc (state : app.ProtocolState) (who : Player) :
    basePayoff state who ∈ Set.Icc (-(3 / 2) : ℝ) 1 := by
  classical
  have bounds := phaseExclusionBase_mem_Icc setup .concurrentReveals runtime leaks
    utility excludedPayoff (fun _ => 0) (fun _ => 1)
    (fun terminal owner => (utility_mem_Icc terminal owner).1)
    (fun terminal owner => (utility_mem_Icc terminal owner).2) state who
  norm_num [excludedPayoff] at bounds
  exact bounds

theorem netPayoff_mem_Icc (state : app.ProtocolState) (who : Player) :
    netPayoff state who ∈ Set.Icc (-(9 / 2) : ℝ) 1 := by
  classical
  have base := basePayoff_mem_Icc state who
  have charge := TerminalAudit.charge_mem_Icc app.stateTraffic audit state who
  change -(9 / 2) ≤ basePayoff state who - _ * deposit who ∧
    basePayoff state who - _ * deposit who ≤ 1
  dsimp only [deposit]
  constructor <;> nlinarith [base.1, base.2, charge.1, charge.2]

theorem rawPayoff_abs_le (who : Player) (history : rawProtocol.History) :
    |rawPayoff who history| ≤ 9 / 2 := by
  classical
  have bounds := netPayoff_mem_Icc history.state who
  exact abs_le.mpr ⟨bounds.1, bounds.2.trans (by norm_num)⟩

theorem rawPayoff_integrable (law : PMF rawProtocol.History) (who : Player) :
    PayoffIntegrable law (rawPayoff who) :=
  payoffIntegrable_of_bounded law _ (C := 9 / 2) (rawPayoff_abs_le who)

/-- A player's own signed input record is clean; foreign packets are unrestricted. -/
def OwnPermitted (who : Player) (execution : app.Execution) : Prop :=
  PhaseCount.CountRecall runtime leaks execution ∧
    ∀ message ∈ execution.network.inputs, message.sender = who →
      PhaseCount.permits execution.network.inputs message = true

def ownPastPermitted (past : List app.PlayerEntry) : Prop :=
  ∀ message ∈ app.outputs past, PhaseCount.permits (app.outputs past) message = true

theorem ownPermitted_iff_past (who : Player) (execution : app.Execution)
    (recalled : PhaseCount.CountRecall runtime leaks execution) :
    OwnPermitted who execution ↔ ownPastPermitted (execution.recall who) := by
  classical
  have verdict (message : Message Player (CommitAttemptPacket graph))
      (owner : message.sender = who) :
      PhaseCount.permits execution.network.inputs message =
        PhaseCount.permits (app.outputs (execution.recall who)) message := by
    apply PhaseCount.permits_congr
    intro other
    have outputs := recalled.1 who
    constructor
    · rintro ⟨present, same, lower⟩
      refine ⟨?_, same, lower⟩
      rw [← outputs]
      exact List.mem_filter.mpr ⟨present, by simp [same, owner]⟩
    · rintro ⟨present, same, lower⟩
      rw [← outputs] at present
      exact ⟨(List.mem_filter.mp present).1, same, lower⟩
  constructor
  · rintro ⟨_, clean⟩ message present
    have outputs := recalled.1 who
    rw [← outputs] at present
    obtain ⟨member, owner⟩ := List.mem_filter.mp present
    have owner' : message.sender = who := by simpa using owner
    rw [← verdict message owner']
    exact clean message member owner'
  · intro clean
    refine ⟨recalled, ?_⟩
    intro message member owner
    rw [verdict message owner]
    apply clean
    rw [← recalled.1 who]
    exact List.mem_filter.mpr ⟨member, by simpa using owner⟩

theorem ownPermitted_initial (who : Player) (state : app.State) :
    OwnPermitted who (ReactiveApplication.Execution.initial app state) := by
  classical
  have clean := PhaseCount.countClean_initial runtime leaks state
  exact ⟨clean.1, fun message member _ => clean.2 message member⟩

theorem ownPermitted_respond (who actor : Player) (execution : app.Execution)
    (action : app.Action) (valid : OwnPermitted who execution)
    (silent : actor = who → action.transmission = none) :
    OwnPermitted who (execution.respond app actor action) := by
  classical
  refine ⟨PhaseCount.countRecall_respond runtime leaks execution valid.1 actor action, ?_⟩
  cases action with
  | mk transmission =>
      cases transmission with
      | none => exact valid.2
      | some material =>
          obtain ⟨inputs, _, kept⟩ :=
            PhaseCount.permits_respond runtime leaks execution valid.1 actor material
          intro message member owner
          rw [inputs] at member
          rcases List.mem_append.mp member with old | new
          · rw [kept message old]
            exact valid.2 message old owner
          · have same := List.mem_singleton.mp new
            have actorEq : actor = who := by
              rw [same] at owner
              exact (show (PhaseCount.localEnvelope runtime leaks actor
                (execution.recall actor) (execution.observe app actor) material).sender =
                  actor from rfl).symm.trans owner
            cases silent actorEq

theorem ownPermitted_environment (who : Player) (execution next : app.Execution)
    (command : app.Command) (valid : OwnPermitted who execution)
    (moved : next ∈ (execution.environmentStep app command).support) :
    OwnPermitted who next := by
  classical
  refine ⟨⟨app.environment_inputRecall execution next command valid.1.1 moved,
    app.environment_serialRecall execution next command valid.1.2.1 moved,
    fun observer => ?_⟩, ?_⟩
  · rw [app.environmentStep_inputs execution next command moved,
      app.environmentStep_nextSerial execution next command moved]
    exact valid.1.2.2 observer
  · rw [app.environmentStep_inputs execution next command moved]
    exact valid.2

theorem ownPermitted_silent_invariant (who : Player) (players : Player → app.Policy)
    (silent : players who = app.silentPolicy) :
    app.PolicyInvariant players (OwnPermitted who) where
  respond execution actor action valid supported := by
    classical
    apply ownPermitted_respond who actor execution action valid
    intro same
    subst actor
    rw [silent] at supported
    exact congrArg ReactiveApplication.Action.transmission
      (app.silentPolicy_cases _ _ action supported)
  environment execution next command valid moved :=
    ownPermitted_environment who execution next command valid moved

def silentContinuation (who : Player) : rawModel.BehavioralPolicy who :=
  rawMenu.restrictPolicy initial horizon scheduler who app.silentPolicy

theorem decode_silentContinuation (who : Player) :
    app.decodePolicy (rawMenu.embedPolicy initial horizon scheduler who
      (silentContinuation who)) = app.silentPolicy := by
  classical
  apply rawMenu.decode_restrictPolicy_of_covered
  intro past view response supported
  rw [app.silentPolicy_cases past view response supported]
  exact (PhaseCount.onePacketMenu_in_raw runtime leaks bounds) who past view
    (PhaseCount.silence_onePacket runtime leaks bounds who past view)

theorem ownPermitted_silent_run (profile : ∀ who, rawModel.BehavioralPolicy who)
    (who : Player) (history : rawProtocol.History) (valid :
      ReactiveApplication.executionInvariant (OwnPermitted who) history.state)
    (fuel : Nat) (final : rawProtocol.History)
    (supported : final ∈ (rawModel.runBehavioralFrom
      (Profile.update (sig := rawModel.behavioralSignature)
        profile who (silentContinuation who)) fuel history).support) :
    ReactiveApplication.executionInvariant (OwnPermitted who) final.state := by
  classical
  let updated := Profile.update (sig := rawModel.behavioralSignature)
    profile who (silentContinuation who)
  let players := rawMenu.decodeProfile initial horizon scheduler updated
  have silent : players who = app.silentPolicy := by
    simpa [players, updated, ReactiveApplication.ResponseMenu.decodeProfile,
      Profile.update_same] using decode_silentContinuation who
  have invariant := ownPermitted_silent_invariant who players silent
  have projection := rawMenu.run_map_controlSteps initial horizon scheduler updated fuel history
  have stateSupported : final.state ∈
      ((rawModel.runBehavioralFrom updated fuel history).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, supported, rfl⟩
  rw [projection] at stateSupported
  have propagate (count : Nat) (state : app.ProtocolState)
      (member : state ∈ ((fun law => law.bind
        (app.controlStep initial horizon scheduler players))^[count]
          (PMF.pure history.state)).support) :
      ReactiveApplication.executionInvariant (OwnPermitted who) state := by
    induction count generalizing state with
    | zero =>
        cases (PMF.mem_support_pure_iff _ _).mp member
        exact valid
    | succ count ih =>
        rw [Function.iterate_succ_apply'] at member
        obtain ⟨before, prior, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
        exact invariant.controlStep initial horizon scheduler
          (fun state _ => ownPermitted_initial who state) before state (ih before prior) reached
  exact propagate fuel final.state stateSupported

theorem ownPermitted_charge_zero (who : Player) (history : rawProtocol.History)
    (valid : ReactiveApplication.executionInvariant (OwnPermitted who) history.state) :
    TerminalAudit.charge app.stateTraffic audit history.state who = 0 := by
  classical
  apply app.sampledTrafficAudit_sound _ _ _ _ _ who
    (fun observed supported => evidenceService.sample_authentic _ observed supported)
  intro record present owner
  have inputs := app.stateTraffic_inputs initial horizon scheduler
    (rawMenu.toRawTrace initial horizon scheduler history.trace)
  cases state : history.state with
  | none =>
      rw [state] at present
      exact (List.not_mem_nil present).elim
  | some control =>
      rw [state] at inputs valid present
      have member := List.mem_map_of_mem (f := ReactiveApplication.TrafficRecord.envelope) present
      rw [inputs] at member
      dsimp only [PhaseCount.evidence]
      rw [inputs]
      exact valid.2 record.envelope member owner

theorem silentContinuation_payoff_lower
    (profile : ∀ who, rawModel.BehavioralPolicy who) (who : Player)
    (history : rawProtocol.History)
    (valid : ReactiveApplication.executionInvariant (OwnPermitted who) history.state) :
    -(3 / 2) ≤ expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature)
        profile who (silentContinuation who)) history) (rawPayoff who) := by
  classical
  rw [rawModel.runBehavioralTerminalFrom_eq_remaining canonicalCertificate _
    (rawMenu.bounded initial horizon scheduler)]
  rw [← expect_constant _ (-(3 / 2) : ℝ)]
  apply expect_mono _ (payoffIntegrable_constant _ _) (rawPayoff_integrable _ who)
  intro final supported
  have clean := ownPermitted_silent_run profile who history valid _ final supported
  have zero := ownPermitted_charge_zero who final clean
  simpa [rawPayoff, netPayoff, TerminalAudit.utility, zero] using
    (basePayoff_mem_Icc final.state who).1

open Classical in
theorem forbidden_committed_payoff_upper
    (profile : ∀ who, rawModel.BehavioralPolicy who)
    (history : rawProtocol.History) (who : Player) (remaining : Nat)
    (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : rawModel.InfoState who) (choice : rawModel.Choice who info)
    (observed : rawModel.infoOf who history.trace = info)
    (material : app.Submission) (selected : choice.1 = some ⟨some material⟩)
    (forbidden : PhaseCount.permits (app.outputs (execution.recall who))
      (PhaseCount.localEnvelope runtime leaks who (execution.recall who)
        (execution.observe app who) material) = false) :
    expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature)
        profile who ((profile who).commit info choice)) history)
      (rawPayoff who) ≤ -2 := by
  classical
  let law := rawModel.runBehavioralTerminalFrom canonicalCertificate
    (Profile.update (sig := rawModel.behavioralSignature) profile who
      ((profile who).commit info choice)) history
  have collected := PhaseCount.countForbidden_collection_committed rawMenu initial horizon
    scheduler canonicalCertificate evidenceService (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) evidenceService_coverage profile history who remaining execution
    current info choice observed material selected forbidden
  have baseBound : PayoffIntegrable law (fun final => basePayoff final.state who) := by
    apply payoffIntegrable_of_bounded _ _ (C := 3 / 2)
    intro final
    have bounds := basePayoff_mem_Icc final.state who
    exact abs_le.mpr ⟨(by linarith [bounds.1]), bounds.2.trans (by norm_num)⟩
  have baseUpper := expect_le_const law (fun final => basePayoff final.state who)
    baseBound 1 (fun final _ => (basePayoff_mem_Icc final.state who).2)
  have multiplied : PayoffIntegrable law (fun final : rawProtocol.History =>
      TerminalAudit.charge app.stateTraffic audit final.state who * 3) := by
    apply payoffIntegrable_of_bounded _ _ (C := 3)
    intro final
    have bounds := TerminalAudit.charge_mem_Icc app.stateTraffic audit final.state who
    rw [abs_of_nonneg (by nlinarith [bounds.1])]
    nlinarith [bounds.2]
  change expect law (fun final => basePayoff final.state who -
    TerminalAudit.charge app.stateTraffic audit final.state who * 3) ≤ -2
  rw [expect_sub baseBound multiplied, expect_mul_const]
  change (1 : ℝ) * 1 ≤ expect law
    (fun final => TerminalAudit.charge app.stateTraffic audit final.state who) at collected
  linarith

open Classical in
/-- A forbidden current transmission is excluded by sequential rationality
on an entire clean own-recall fiber, including its zero-belief histories. -/
theorem no_forbidden_supported_of_ownPastPermitted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : rawModel.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (atSite : site.1 = some (past, view)) (clean : ownPastPermitted past)
    (choice : rawModel.Choice who site.1) (material : app.Submission)
    (selected : choice.1 = some ⟨some material⟩)
    (forbidden : PhaseCount.permits (app.outputs past)
      (PhaseCount.localEnvelope runtime leaks who past view material) = false) :
    choice ∉ (assessment.strategy who site.1).support := by
  classical
  have rational := equilibrium.1 who site
  have factor := rawModel.runnerFactorsAt_terminal canonicalCertificate
    (rawMenu.decisionRecall initial horizon scheduler).actsOnceWhereItMatters
    (rawMenu.informationSite_allNonterminal initial horizon scheduler who site)
  have bound (final : rawProtocol.History) (_ : rawProtocol.terminal final.state) :
      |rawPayoff who final| ≤ 9 / 2 := rawPayoff_abs_le who final
  apply assessment.not_supported_choice_of_uniform_gap
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site factor (rawPayoff who)
    rational (assessment.continuationContext_integrable_of_bounded_terminal
      canonicalCertificate site (rawPayoff who) (9 / 2) bound (assessment.strategy who))
    choice (silentContinuation who)
    (assessment.continuationContext_integrable_of_bounded_terminal
      canonicalCertificate site (rawPayoff who) (9 / 2) bound (silentContinuation who))
    (-2) (-(3 / 2)) (by norm_num)
  · intro history
    have observed := ((rawMenu.info initial horizon scheduler who history.1.trace).symm.trans
      (history.2.trans atSite))
    cases state : history.1.state with
    | none => simp [ReactiveApplication.observe, state] at observed
    | some control =>
        rcases control with ⟨remaining, actor, execution⟩
        by_cases active : actor = some who
        · subst actor
          simp only [ReactiveApplication.observe, state, ↓reduceIte] at observed
          have pair : (execution.recall who, execution.observe app who) = (past, view) := by
            exact Option.some.inj observed
          apply forbidden_committed_payoff_upper assessment.strategy history.1 who remaining
            execution state site.1 choice history.2 material selected
          have recallEq : execution.recall who = past := congrArg Prod.fst pair
          have viewEq : execution.observe app who = view := congrArg Prod.snd pair
          rw [recallEq, viewEq]
          exact forbidden
        · simp [ReactiveApplication.observe, state, active] at observed
  · intro history
    apply silentContinuation_payoff_lower assessment.strategy who history.1
    have observed := ((rawMenu.info initial horizon scheduler who history.1.trace).symm.trans
      (history.2.trans atSite))
    cases state : history.1.state with
    | none => trivial
    | some control =>
        by_cases active : control.actor = some who
        · simp only [ReactiveApplication.observe, state, active, ↓reduceIte] at observed
          have pair : (control.execution.recall who, control.execution.observe app who) =
              (past, view) := by
            exact Option.some.inj observed
          change OwnPermitted who control.execution
          apply (ownPermitted_iff_past who control.execution
            (PhaseCount.countRecall_history runtime leaks
              (state ▸ rawMenu.toRawTrace initial horizon scheduler history.1.trace))).mpr
          have recallEq : control.execution.recall who = past := congrArg Prod.fst pair
          rw [recallEq]
          exact clean
        · simp [ReactiveApplication.observe, state, active] at observed

/-- On any clean full-input fiber, a supported physical response belongs to
the actual count-filtered menu. No restriction is asserted after a sunk charge. -/
theorem clean_supported_response_counted (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : rawModel.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (atSite : site.1 = some (past, view)) (clean : ownPastPermitted past)
    (choice : rawModel.Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support)
    (response : app.Action) (selected : choice.1 = some response) :
    response ∈ countedMenu.actions who past view := by
  classical
  have available : response ∈ rawMenu.actions who past view := by
    have member : (some response : Option app.Action) ∈ rawModel.menu who site.1 :=
      selected ▸ choice.2
    rw [atSite] at member
    change ∃ action : app.Action, action ∈ rawMenu.actions who past view ∧
      some response = some action at member
    obtain ⟨action, permitted, equal⟩ := member
    have same : action = response := Option.some.inj equal.symm
    simpa only [same] using permitted
  by_contra absent
  have extra : ∃ material : app.Submission, response.transmission = some material ∧
      PhaseCount.permits (app.outputs past)
        (PhaseCount.localEnvelope runtime leaks who past view material) = false :=
    PhaseCount.onePacket_extra runtime leaks bounds who past view response available absent
  obtain ⟨material, sent, forbidden⟩ := extra
  have rawSelected : choice.1 = some ⟨some material⟩ := by
    rw [selected]
    congr 1
    cases response
    cases sent
    rfl
  exact no_forbidden_supported_of_ownPastPermitted assessment equilibrium who site past view
    atSite clean choice material rawSelected forbidden supported


/-- Only the focal recalled record is clean. Foreign traffic in the full
information fiber need not belong to the one-packet menu. -/
theorem raw_equilibrium_clean_response_counted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : rawModel.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (atSite : site.1 = some (past, view)) (clean : ownPastPermitted past)
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
      who past view).support) : response ∈ countedMenu.actions who past view := by
  classical
  rcases site with ⟨info, decision⟩
  dsimp only at atSite
  subst info
  let target : rawModel.InformationSite who := ⟨some (past, view), decision⟩
  change response ∈ (app.decodePolicy
    (rawMenu.embedPolicy initial horizon scheduler who (assessment.strategy who))
      past view).support at supported
  rw [ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    PMF.map_comp, PMF.support_map] at supported
  change ∃ choice : rawModel.Choice who (some (past, view)),
    choice ∈ (assessment.strategy who (some (past, view))).support ∧
      choice.1.getD ⟨none⟩ = response at supported
  obtain ⟨choice, chosen, value⟩ := supported
  change choice.1.getD ⟨none⟩ = response at value
  obtain ⟨physical, _available, physicalEq⟩ := choice.2
  rw [physicalEq, Option.getD_some] at value
  have selected : choice.1 = some response := physicalEq.trans (congrArg some value)
  exact clean_supported_response_counted assessment equilibrium who target past view rfl
    clean choice chosen response selected


/-- Every genuine counted decision has a clean own recalled record, even if
its probability under the assessed raw profile is zero. -/
theorem counted_site_ownPastPermitted (who : Player)
    (site : countedModel.InformationSite who) (past : List app.PlayerEntry)
    (view : app.PlayerView) (atSite : site.1 = some (past, view)) :
    ownPastPermitted past := by
  classical
  obtain ⟨history, _running, _action, _permitted⟩ := site.2
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state)
    history.1.trace
  have observed : app.observe who history.1.state = some (past, view) :=
    (countedMenu.info initial horizon scheduler who history.1.trace).symm.trans
      (history.2.trans atSite)
  cases state : history.1.state with
  | none => simp [ReactiveApplication.observe, state] at observed
  | some control =>
      rw [state] at clean
      by_cases active : control.actor = some who
      · have pair := Option.some.inj (by
          simpa only [ReactiveApplication.observe, state, active, ite_true] using observed)
        have recallEq : control.execution.recall who = past := congrArg Prod.fst pair
        have own : OwnPermitted who control.execution :=
          ⟨clean.1, fun message member _ => clean.2 message member⟩
        rw [← recallEq]
        exact (ownPermitted_iff_past who control.execution clean.1).mp own
      · simp [ReactiveApplication.observe, state, active] at observed

/-- The decoded actual raw strategy is supported in the count menu at every
genuine counted site. This is inferred from sequential rationality, rather
than imposed on the foreign continuation. -/
theorem raw_equilibrium_counted_site_covered
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (site : countedModel.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (atSite : site.1 = some (past, view)) (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
      who past view).support) : response ∈ countedMenu.actions who past view := by
  classical
  rcases site with ⟨info, decision⟩
  dsimp only at atSite
  subst info
  let source : countedModel.InformationSite who := ⟨some (past, view), decision⟩
  let target := (countedInRaw.actionRestriction initial horizon scheduler).site who source
  have clean := counted_site_ownPastPermitted who source past view rfl
  exact raw_equilibrium_clean_response_counted assessment equilibrium who target past view rfl
    clean response supported

/-- Restrict the actual decoded strategy. The default branch is irrelevant at
genuine counted decision sites by the preceding support theorem. -/
def countedAssessmentProfile (assessment : rawModel.BehavioralAssessment)
    (who : Player) : countedModel.BehavioralPolicy who :=
  countedMenu.restrictPolicy initial horizon scheduler who
    (rawMenu.decodeProfile initial horizon scheduler assessment.strategy who)

private theorem decoded_profile_map_some (assessment : rawModel.BehavioralAssessment)
    (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView) :
    (rawMenu.decodeProfile initial horizon scheduler assessment.strategy who past view).map some =
      (assessment.strategy who (some (past, view))).map Subtype.val := by
  have encoded := congrFun (app.encode_decodePolicy
    (rawMenu.embedPolicy initial horizon scheduler who (assessment.strategy who)))
      (some (past, view))
  have projected := congrArg (fun law => law.map Subtype.val) encoded
  simpa only [ReactiveApplication.encodePolicy,
    ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
    ReactiveApplication.ResponseMenu.rawChoice] using projected

/-- The assessed raw strategy extends this counted profile on all retained
sites, including genuine sites that are off path under both profiles. -/
theorem raw_equilibrium_extends_counted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    (countedInRaw.actionRestriction initial horizon scheduler).ExtendsProfile
      (countedAssessmentProfile assessment) assessment.strategy := by
  classical
  rintro who ⟨info, decision⟩
  cases info with
  | none =>
      obtain ⟨_history, _running, action, permitted⟩ := decision
      change (some action : Option app.Action) = none at permitted
      cases permitted
  | some input =>
      rcases input with ⟨past, view⟩
      let site : countedModel.InformationSite who := ⟨some (past, view), decision⟩
      have siteObserved : site.1 = some (past, view) := rfl
      have covered (response : app.Action)
          (supported : response ∈ (rawMenu.decodeProfile initial horizon scheduler
            assessment.strategy who past view).support) :
          response ∈ countedMenu.actions who past view := by
        change response ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions who past view
        exact raw_equilibrium_counted_site_covered assessment equilibrium who site past view
          siteObserved response supported
      apply pmf_map_injective (f := Subtype.val)
      · exact Subtype.val_injective
      · calc
          _ = (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
              who past view).map some :=
            (decoded_profile_map_some assessment who past view).symm
          _ = (countedAssessmentProfile assessment who (some (past, view))).map Subtype.val :=
            (countedMenu.restrictPolicy_map_val initial horizon scheduler who _ past view
              covered).symm
          _ = _ := by rw [PMF.map_comp]; rfl


/-- The actual counted restriction of the assessed profile has the unchanged
raw physical continuation law at every genuine counted history. The equality
comes from the derived full-site extension, not a global raw coverage premise. -/
theorem counted_assessment_run_state
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (fuel : Nat) (history : countedProtocol.History)
    (enough : app.rank horizon history.state ≤ fuel) :
    (countedModel.runBehavioralFrom (countedAssessmentProfile assessment) fuel history).map
      ExecutionProtocol.History.state =
    app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) history.state := by
  have law := (countedInRaw.actionRestriction initial horizon scheduler).runFrom_law
    (countedAssessmentProfile assessment) assessment.strategy
      (raw_equilibrium_extends_counted assessment equilibrium) fuel history
  have projected := congrArg (fun distribution =>
    distribution.map ExecutionProtocol.History.state) law
  rw [PMF.map_comp] at projected
  simp only [Function.comp_def] at projected
  have forget : (fun retained : countedProtocol.History =>
      ((countedInRaw.actionRestriction initial horizon scheduler).history retained).state) =
      ExecutionProtocol.History.state := by
    funext retained
    exact countedInRaw.history_state initial horizon scheduler retained
  rw [forget] at projected
  have target := rawMenu.run_eq_finish initial horizon scheduler assessment.strategy fuel
    ((countedInRaw.actionRestriction initial horizon scheduler).history history) enough
  exact projected.trans target

/-- Decoding the actual counted restriction changes no physical continuation
from a genuine counted prefix, even at an off-path prefix. -/
theorem counted_assessment_finish_eq
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (history : countedProtocol.History) :
    app.finish initial horizon scheduler
        (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        history.state =
      app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) history.state := by
  have counted := countedMenu.run_eq_finish initial horizon scheduler
    (countedAssessmentProfile assessment) (app.rank horizon history.state) history le_rfl
  exact counted.symm.trans (counted_assessment_run_state assessment equilibrium _ history le_rfl)

end Vegas.Examples.CommitSeedBroadcast
