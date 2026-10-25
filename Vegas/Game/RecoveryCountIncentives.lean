/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionCountMenu
import Vegas.Game.RecoveryOnePacketExtension
import GameTheory.Analysis.Protocol.SupportedChoices
import Interaction.ReactivePolicyMenuInvariant
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Silence preserves a clean own prefix against arbitrary opponents -/

noncomputable section

namespace Vegas.EventGraphRuntime.Recovery

open Interaction GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private abbrev countApplication := runtime.recoveryApplication leaks

/-- Only envelopes attributed to the selected player must have permitted verdicts. -/
def OwnerCountClean (who : Player) (execution : (countApplication runtime leaks).Execution) :
  Prop :=
  ∀ message ∈ execution.network.inputs, message.sender = who →
    countPermits execution.network.inputs message = true

theorem ownerCountClean_initial (who : Player) (state : (countApplication runtime leaks).State) :
    OwnerCountClean runtime leaks who (ReactiveApplication.Execution.initial (countApplication
      runtime leaks) state) := by
  intro message present
  cases present

/-- An opponent's arbitrary response cannot alter the player's old verdicts. -/
theorem ownerCountClean_respond (who actor : Player) (execution : (countApplication runtime
  leaks).Execution)
    (clean : OwnerCountClean runtime leaks who execution) (action : (countApplication runtime
      leaks).Action)
    (allowed : actor ≠ who ∨ action.transmission = none) :
    OwnerCountClean runtime leaks who (execution.respond (countApplication runtime leaks) actor
      action) := by
  rcases action with ⟨_ | material⟩
  · exact clean
  · have different : actor ≠ who := by
      rcases allowed with different | impossible
      · exact different
      · cases impossible
    let envelope : Message Player (WitnessedPacket graph) :=
      ⟨(actor, execution.network.nextSerial actor),
        (countApplication runtime leaks).packet ((countApplication runtime leaks).submit
          execution.application actor material) actor
          (execution.network.known actor) material⟩
    let inputs : List (Message Player (WitnessedPacket graph)) := execution.network.inputs
    change ∀ message : Message Player (WitnessedPacket graph),
      message ∈ inputs ++ [envelope] → message.sender = who →
        countPermits (inputs ++ [envelope]) message = true
    intro message present owner
    have old : message ∈ inputs := by
      rcases List.mem_append.mp present with old | fresh
      · exact old
      · have same := List.mem_singleton.mp fresh
        subst message
        exact (different owner).elim
    have kept : countPermits (inputs ++ [envelope]) message = countPermits inputs message :=
      countPermits_append_later inputs [envelope] message (by
        intro newer member sender
        have same := List.mem_singleton.mp member
        subst newer
        exact (different (sender.trans owner)).elim)
    exact kept.trans (clean message old owner)

theorem ownerCountClean_environment (who : Player) (execution next : (countApplication runtime
  leaks).Execution)
    (command : (countApplication runtime leaks).Command) (clean : OwnerCountClean runtime leaks
      who execution)
    (moved : next ∈ (execution.environmentStep (countApplication runtime leaks) command).support) :
    OwnerCountClean runtime leaks who next := by
  intro message present owner
  have unchanged := (countApplication runtime leaks).environmentStep_inputs
    execution next command moved
  rw [unchanged] at present ⊢
  exact clean message present owner

/-- Silence of one player suffices; no opponent conformance is assumed. -/
theorem ownerCountClean_invariant (players : Player → (countApplication runtime leaks).Policy)
  (who : Player)
    (silent : players who = (countApplication runtime leaks).silentPolicy) :
    (countApplication runtime leaks).PolicyInvariant players (OwnerCountClean runtime leaks who)
      where
  respond execution actor action clean supported := by
    apply ownerCountClean_respond runtime leaks who actor execution clean action
    by_cases same : actor = who
    · subst actor
      rw [silent] at supported
      have chosen := (countApplication runtime leaks).silentPolicy_cases _ _ action supported
      exact Or.inr (congrArg ReactiveApplication.Action.transmission chosen)
    · exact Or.inl same
  environment execution next command clean moved :=
    ownerCountClean_environment runtime leaks who execution next command clean moved

/-- Authentic sampling can charge the player only for one of its own forbidden records. -/
theorem countAudit_charge_zero_of_owner
    (service : EvidenceReportService (CountEvidence graph))
    (traffic : List (countApplication runtime leaks).TrafficRecord) (who : Player)
    (clean : ∀ record ∈ traffic, record.envelope.sender = who →
      countPermits (traffic.map ReactiveApplication.TrafficRecord.envelope)
        record.envelope = true) :
    (((countAudit runtime leaks service.sample traffic).map
      (fun verdict => verdict who)) true).toReal = 0 := by
  exact (countApplication runtime leaks).sampledTrafficAudit_sound _ _ _ _ traffic who
    (fun observed supported => service.sample_authentic _ observed supported) clean

variable [Fintype Player] (menu : (countApplication runtime leaks).ResponseMenu)
    (initial : PMF (countApplication runtime leaks).State) (horizon : Nat) (scheduler :
      (countApplication runtime leaks).Scheduler)

/-- The actual continuation preserves own cleanliness after the player adopts silence. -/
theorem silent_terminal_ownerClean
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player)
    (silent : menu.decodeProfile initial horizon scheduler profile who = (countApplication
      runtime leaks).silentPolicy)
    (history : (menu.protocol initial horizon scheduler).History)
    (clean : ReactiveApplication.executionInvariant (OwnerCountClean runtime leaks who)
      history.state) :
    ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralTerminalFrom
      certificate profile history).support,
      ReactiveApplication.executionInvariant (OwnerCountClean runtime leaks who) final.state := by
  let players := menu.decodeProfile initial horizon scheduler profile
  have invariant := ownerCountClean_invariant runtime leaks players who silent
  intro final supported
  have terminalLaw := InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (menu.information initial horizon scheduler) certificate
      (menu.bounded initial horizon scheduler) profile history
  rw [terminalLaw] at supported
  exact ReactiveApplication.PolicyInvariant.run_menu menu initial horizon scheduler profile
    invariant (fun state _ => ownerCountClean_initial runtime leaks who state)
    (2 * horizon + 1) history clean final supported

omit [Fintype Player] in
/-- Own cleanliness gives zero audit charge, even if other owners emitted forbidden packets. -/
theorem ownerClean_countCharge_zero
    (service : EvidenceReportService (CountEvidence graph))
    (history : (menu.protocol initial horizon scheduler).History) (who : Player)
    (clean : ReactiveApplication.executionInvariant (OwnerCountClean runtime leaks who)
      history.state) :
    TerminalAudit.charge (countApplication runtime leaks).stateTraffic (countAudit runtime leaks
      service.sample)
      history.state who = 0 := by
  have inputs := (countApplication runtime leaks).stateTraffic_inputs initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)
  change ((countApplication runtime leaks).stateTraffic history.state).map
    ReactiveApplication.TrafficRecord.envelope =
    history.state.elim [] (fun control => control.execution.network.inputs) at inputs
  unfold TerminalAudit.charge
  apply countAudit_charge_zero_of_owner runtime leaks service _ who
  intro record present owner
  cases current : history.state with
  | none =>
    rw [current] at present
    cases present
  | some control =>
    rw [current] at inputs clean present
    have typedInputs :
        ((countApplication runtime leaks).stateTraffic (some control)).map
            (fun item => (item.envelope : Message Player (WitnessedPacket graph))) =
          (control.execution.network.inputs : List (Message Player (WitnessedPacket graph))) :=
      inputs
    change countPermits
      (((countApplication runtime leaks).stateTraffic (some control)).map
        (fun item => (item.envelope : Message Player (WitnessedPacket graph))))
      (record.envelope : Message Player (WitnessedPacket graph)) = true
    rw [typedInputs]
    apply clean record.envelope ?_ owner
    rw [← typedInputs]
    exact List.mem_map_of_mem present

/-- The safe continuation's expected charge is zero at every own-clean history. -/
theorem silent_terminal_expected_charge_zero
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player)
    (silent : menu.decodeProfile initial horizon scheduler profile who = (countApplication
      runtime leaks).silentPolicy)
    (service : EvidenceReportService (CountEvidence graph))
    (history : (menu.protocol initial horizon scheduler).History)
    (clean : ReactiveApplication.executionInvariant (OwnerCountClean runtime leaks who)
      history.state) :
    expect ((menu.information initial horizon scheduler).runBehavioralTerminalFrom
      certificate profile history)
      (fun final => TerminalAudit.charge (countApplication runtime leaks).stateTraffic
        (countAudit runtime leaks service.sample)
        final.state who) = 0 := by
  calc
    _ = expect _ (fun _ => (0 : ℝ)) := by
      apply expect_congr_on_support
      intro final supported
      exact ownerClean_countCharge_zero runtime leaks menu initial horizon scheduler service
        final who (silent_terminal_ownerClean runtime leaks menu initial horizon scheduler
          certificate profile who silent history clean final supported)
    _ = 0 := expect_constant _ _

variable (bounds : MessageBounds graph)

private abbrev effectiveMenu := Vegas.EventGraphRuntime.Recovery.menu runtime leaks bounds

/-- The actual effective menu provides one silent comparator for all own-clean
histories and all opponent behavioral policies. -/
theorem exists_effective_silent_continuation (who : Player) :
    ∃ alternative : ((effectiveMenu runtime leaks bounds).information initial horizon
      scheduler).BehavioralPolicy who,
      ∀ (profile : ∀ owner,
          ((effectiveMenu runtime leaks bounds).information initial horizon
            scheduler).BehavioralPolicy owner)
        (service : EvidenceReportService (CountEvidence graph))
        (history : ((effectiveMenu runtime leaks bounds).protocol initial horizon
          scheduler).History),
        ReactiveApplication.executionInvariant (OwnerCountClean runtime leaks who) history.state →
        expect (((effectiveMenu runtime leaks bounds).information initial horizon
          scheduler).runBehavioralTerminalFrom
            ((effectiveMenu runtime leaks bounds).bounded initial horizon
              scheduler).wellFoundedHistories
            (Profile.update
              (sig := ((effectiveMenu runtime leaks bounds).information initial horizon
                scheduler).behavioralSignature) profile who alternative) history)
          (fun final => TerminalAudit.charge (countApplication runtime leaks).stateTraffic
            (countAudit runtime leaks service.sample) final.state who) = 0 := by
  let alternative := (effectiveMenu runtime leaks bounds).restrictPolicy initial horizon
    scheduler who (countApplication runtime leaks).silentPolicy
  refine ⟨alternative, ?_⟩
  intro profile service history clean
  apply silent_terminal_expected_charge_zero runtime leaks (effectiveMenu runtime leaks bounds)
    initial horizon scheduler
    ((effectiveMenu runtime leaks bounds).bounded initial horizon scheduler).wellFoundedHistories
    (Profile.update
              (sig := ((effectiveMenu runtime leaks bounds).information initial horizon
                scheduler).behavioralSignature) profile who alternative)
    who ?_ service history clean
  rw [(effectiveMenu runtime leaks bounds).decodeProfile_update, Function.update_self]
  exact (effectiveMenu runtime leaks bounds).decode_restrictPolicy_of_covered initial horizon
    scheduler who (countApplication runtime leaks).silentPolicy
    (fun past view response supported => by
      have selected := (countApplication runtime leaks).silentPolicy_cases past view response
        supported
      subst response
      exact silence_menu runtime leaks bounds who past view)


/-- A strict collected-deposit margin rules out a forbidden response at every
own-clean information fiber, regardless of opponents' later policies. -/
theorem forbidden_choice_not_supported
    (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ owner, 0 ≤ deliveryRate owner)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (utility : (countApplication runtime leaks).ProtocolState → Player → ℝ) (deposit : Player → ℝ)
    (who : Player) (lower upper : ℝ)
    (lower_le : ∀ state, lower ≤ utility state who)
    (le_upper : ∀ state, utility state who ≤ upper)
    (nonnegative : 0 ≤ deposit who)
    (strict : upper - lower < observationRate who * deliveryRate who * deposit who)
    (assessment : ((effectiveMenu runtime leaks bounds).information initial horizon
      scheduler).BehavioralAssessment)
    (site : ((effectiveMenu runtime leaks bounds).information initial horizon
      scheduler).InformationSite who)
    (clean : ∀ history :
        ((effectiveMenu runtime leaks bounds).information initial horizon
          scheduler).InformationHistory who site.1,
      ReactiveApplication.executionInvariant (OwnerCountClean runtime leaks who) history.1.state)
    (past : List (countApplication runtime leaks).PlayerEntry) (view : (countApplication runtime
      leaks).PlayerView) (input : site.1 = some (past, view))
    (choice : ((effectiveMenu runtime leaks bounds).information initial horizon
      scheduler).Choice who site.1)
    (material : (countApplication runtime leaks).Submission) (selected : choice.1 = some ⟨some
      material⟩)
    (forbidden : countPermits ((countApplication runtime leaks).outputs past)
      (localEnvelope runtime leaks who past view material) = false) :
    let certificate := ((effectiveMenu runtime leaks bounds).bounded initial horizon
      scheduler).wellFoundedHistories
    let model := (effectiveMenu runtime leaks bounds).information initial horizon scheduler
    let payoff := fun final : ((effectiveMenu runtime leaks bounds).protocol initial horizon
      scheduler).History =>
      TerminalAudit.utility utility (countApplication runtime leaks).stateTraffic (countAudit
        runtime leaks service.sample)
        deposit final.state who
    assessment.IsSequentiallyRationalAt site
      (assessment.continuationContextWith (model.runBehavioralTerminalFrom certificate)
        site payoff) →
      choice ∉ (assessment.strategy who site.1).support := by
  classical
  intro certificate model payoff rational
  let base := fun final : ((effectiveMenu runtime leaks bounds).protocol initial horizon
    scheduler).History =>
    utility final.state who
  let charge := fun final : ((effectiveMenu runtime leaks bounds).protocol initial horizon
    scheduler).History =>
    TerminalAudit.charge (countApplication runtime leaks).stateTraffic (countAudit runtime leaks
      service.sample) final.state who
  have read : payoff = fun final => base final - deposit who * charge final := by
    funext final
    dsimp only [payoff, base, charge, TerminalAudit.utility]
    ring
  have baseBound : ∀ final, |base final| ≤ |lower| + |upper| := by
    intro final
    apply abs_le.mpr
    constructor
    · have := lower_le final.state
      linarith [neg_abs_le lower, abs_nonneg upper]
    · have := le_upper final.state
      linarith [le_abs_self upper, abs_nonneg lower]
  have baseIntegrable (law : PMF ((effectiveMenu runtime leaks bounds).protocol initial horizon
    scheduler).History) :
      PayoffIntegrable law base := payoffIntegrable_of_bounded law base baseBound
  have chargeIntegrable (law : PMF ((effectiveMenu runtime leaks bounds).protocol initial
    horizon scheduler).History) :
      PayoffIntegrable law charge := TerminalAudit.payoffIntegrable_charge law _ _ who
  have averaged (law : PMF ((effectiveMenu runtime leaks bounds).protocol initial horizon
    scheduler).History) :
      expect law payoff = expect law base - deposit who * expect law charge := by
    rw [read, expect_sub (baseIntegrable law)
      (payoffIntegrable_const_mul (chargeIntegrable law)), expect_const_mul]
  have integrable (law : PMF ((effectiveMenu runtime leaks bounds).protocol initial horizon
    scheduler).History) :
      PayoffIntegrable law payoff := by
    rw [read]
    exact payoffIntegrable_sub (baseIntegrable law)
      (payoffIntegrable_const_mul (chargeIntegrable law))
  obtain ⟨alternative, safe⟩ := exists_effective_silent_continuation (runtime := runtime)
    (leaks := leaks) (initial := initial) (horizon := horizon) (scheduler := scheduler)
    (bounds := bounds) who
  refine assessment.not_supported_choice_of_uniform_gap
    (model.runBehavioralTerminalFrom certificate) site
    (model.runnerFactorsAt_terminal certificate
      ((effectiveMenu runtime leaks bounds).decisionRecall initial horizon
        scheduler).actsOnceWhereItMatters
      ((effectiveMenu runtime leaks bounds).informationSite_allNonterminal initial horizon
        scheduler who site))
    payoff rational (integrable _) choice alternative (integrable _)
    (upper - observationRate who * deliveryRate who * deposit who) lower (by linarith) ?_ ?_
  · intro history
    let law := model.runBehavioralTerminalFrom certificate
      (Profile.update (sig := model.behavioralSignature) assessment.strategy who
        ((assessment.strategy who).commit site.1 choice))
        history.1
    change expect law payoff ≤ upper - observationRate who * deliveryRate who * deposit who
    have collected : observationRate who * deliveryRate who ≤ expect law charge := by
      have observed : (countApplication runtime leaks).observe who history.1.state = some (past,
        view) :=
        ((effectiveMenu runtime leaks bounds).info initial horizon scheduler who
          history.1.trace).symm.trans
          (history.2.trans input)
      cases current : history.1.state with
      | none => simp [ReactiveApplication.observe, current] at observed
      | some control =>
        rcases control with ⟨remaining, actor, execution⟩
        by_cases active : actor = some who
        · subst actor
          simp only [ReactiveApplication.observe, current, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at observed
          obtain ⟨rfl, rfl⟩ := observed
          exact countForbidden_collection_committed (runtime := runtime) (leaks := leaks)
            (effectiveMenu runtime leaks bounds) initial horizon scheduler certificate service
              observationRate deliveryRate
            delivery_nonnegative coverage assessment.strategy history.1 who remaining execution
            current site.1 choice history.2 material selected forbidden
        · simp [ReactiveApplication.observe, current, active] at observed
    have upperBound := expect_le_const law base (baseIntegrable law) upper
      (fun final _ => le_upper final.state)
    have charged := mul_le_mul_of_nonneg_left collected nonnegative
    rw [averaged law]
    nlinarith
  · intro history
    let law := model.runBehavioralTerminalFrom certificate
      (Profile.update (sig := model.behavioralSignature) assessment.strategy who alternative)
        history.1
    change lower ≤ expect law payoff
    have noCharge : expect law charge = 0 :=
      safe assessment.strategy service history.1 (clean history)
    have lowerBound := expect_mono (μ := law) (fun final _ => lower_le final.state)
      (payoffIntegrable_constant law lower) (baseIntegrable law)
    rw [expect_constant] at lowerBound
    rw [averaged law, noCharge, mul_zero, sub_zero]
    exact lowerBound

end Vegas.EventGraphRuntime.Recovery
