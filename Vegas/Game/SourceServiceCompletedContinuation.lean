/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceClearAudit
import Vegas.Game.SourceServiceReadout
import Vegas.Game.SourceServiceOwnerSettled
import Vegas.Pending.ReactiveCompletedConfig
import Interaction.ReactiveResponseEvaluation
import Interaction.ReactiveFiniteAssessment
import GameTheoryExtensions.Analysis.Protocol.TerminalAuditContinuation

/-! # Completed source configurations and actual owner continuation audit

An actual compatible owner prefix supplies permitted current packets. Once
all events have completed, their accepted content survives arbitrary later
service operations. Silent owner continuation adds no owner packets or misses,
while foreign responses remain arbitrary. The typed source readout is fixed
under every raw continuation; nonnegative escrow therefore bounds audited
utility by that fixed base payoff. No claim concerns an unfinished cut.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem completed_permitted_good
    (execution : (application setup leaks).Execution)
    (complete : execution.application.config.cut.completed = Finset.univ)
    (message : Message Player (WitnessedPacket (graph setup)))
    (allowed : ((runtime setup).settledRecord leaks execution).permits message = true) :
    SettledGood setup leaks execution message := by
  have permitted := (SettledRecord.permits_eq_true_iff _ _).mp allowed
  unfold SettledRecord.Permits at permitted
  cases named : message.payload.call.event? (graph setup) with
  | none => simp only [named] at permitted
  | some event =>
      rw [named] at permitted
      have completed : event ∈ execution.application.config.cut.completed := by
        rw [complete]
        exact Finset.mem_univ event
      have settled := (execution.application.config.history_exact event).mpr completed
      rcases permitted with unsettled | accepted
      · exact (unsettled settled).elim
      · exact ⟨event, named, Or.inr ⟨accepted.1, completed, accepted.2⟩⟩

private theorem completed_good_environment
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (complete : execution.application.config.cut.completed = Finset.univ)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (message : Message Player (WitnessedPacket (graph setup)))
    (good : SettledGood setup leaks execution message) :
    SettledGood setup leaks next message := by
  obtain ⟨event, named, pending | accepted⟩ := good
  · have completed : event ∈ execution.application.config.cut.completed := by
      rw [complete]
      exact Finset.mem_univ event
    exact (pending.1.1 completed).elim
  · have step := contractStep_environment (runtime setup) leaks execution next command reached
    have receiptsPrefix := (application setup leaks).environmentStep_receipts_prefix execution next
      command reached
    exact ⟨event, named, Or.inr ⟨receiptsPrefix.subset accepted.1,
      step.completed_mono accepted.2.1,
      settledContent_step step execution.receipts next.receipts message event named
        accepted.2.1 accepted.2.2⟩⟩

private theorem completed_silent_invariant
    (players : Player → (application setup leaks).Policy) (who : Player)
    (follows : players who = (application setup leaks).silentPolicy)
    (config : (graph setup).Config) (complete : config.cut.completed = Finset.univ) :
    (application setup leaks).PolicyInvariant players (fun execution =>
      execution.application.config = config ∧ SettledFacts setup leaks execution ∧
        execution.application.publicView.missedDecisionBy who = false ∧
        ∀ message, message.sender = who → Emitted setup leaks execution message →
          SettledGood setup leaks execution message) := by
  let app := application setup leaks
  let invariant := (runtime setup).reactiveCompletedConfigInvariant leaks config complete
  constructor
  · intro execution responder response valid chosen
    obtain ⟨same, facts, noMiss, good⟩ := valid
    have publicEq := ((runtime setup).reactive_respond_application leaks execution responder
      response).2
    refine ⟨invariant.respond execution responder response same,
      settledFacts_respond execution facts responder response, ?_, ?_⟩
    · rw [publicEq]
      exact noMiss
    · apply owner_good_response facts who responder response good
      intro owned material submitted
      subst responder
      rw [follows] at chosen
      obtain rfl := app.silentPolicy_cases _ _ response chosen
      cases submitted
  · intro execution next command valid reached
    obtain ⟨same, facts, noMiss, good⟩ := valid
    have completeNow : execution.application.config.cut.completed = Finset.univ := by
      rw [same]
      exact complete
    refine ⟨invariant.environmentStep execution next command same reached,
      settledFacts_environment execution next command facts reached, ?_, ?_⟩
    · rw [PublicView.missedDecisionBy_eq_false_iff] at noMiss ⊢
      intro event owned marked
      have clear := noMiss event owned
      obtain ⟨_, ready, _, _⟩ := (runtime setup).reactive_new_missedEvent leaks command reached
        event clear marked
      apply ready.1
      rw [completeNow]
      exact Finset.mem_univ event
    · intro message authored emitted
      have previous : Emitted setup leaks execution message := by
        unfold Emitted at emitted ⊢
        rw [← app.environmentStep_inputs execution next command reached]
        exact emitted
      exact completed_good_environment execution next command completeNow reached message
        (good message authored previous)

/-- The whole typed source readout is constant throughout an arbitrary raw
response and continuation from a completed configuration. -/
theorem sourceServiceCompleted_finish_readout
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (complete : execution.application.config.cut.completed = Finset.univ)
    (final : (application setup leaks).ProtocolState)
    (reached : final ∈ ((application setup leaks).finish initial horizon scheduler players
      (some ⟨remaining, some who, execution⟩)).support) :
    sourceReadout setup leaks final =
      sourceReadout setup leaks (some ⟨remaining, some who, execution⟩) := by
  let app := application setup leaks
  change final ∈ (((app.resume players (some who) execution).bind
    (app.runRounds scheduler players remaining)).map app.finished).support at reached
  obtain ⟨last, continued, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨first, chosen, rounds⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ continued)
  obtain ⟨response, _selected, responseEq⟩ := PMF.support_map .. ▸ chosen
  have invariant := (runtime setup).reactiveCompletedConfigInvariant leaks
    execution.application.config complete
  have same := (invariant.policyInvariant app players).runRounds scheduler remaining first last
    (responseEq ▸ invariant.respond execution who response rfl) rounds
  unfold sourceReadout ReactiveApplication.finished
  simp only [Option.bind_some]
  rw [same]

/-- Nonnegative escrow cannot improve the fixed source value of a completed
configuration, under any whole raw continuation policy. -/
theorem sourceServiceCompleted_finish_value_le
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (complete : execution.application.config.cut.completed = Finset.univ)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who) :
    expect ((application setup leaks).finish initial horizon scheduler players
      (some ⟨remaining, some who, execution⟩))
        (fun final => TerminalAudit.utility (baseUtility setup leaks utility)
          ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
          deposit final who) ≤
      baseUtility setup leaks utility (some ⟨remaining, some who, execution⟩) who := by
  let law := (application setup leaks).finish initial horizon scheduler players
    (some ⟨remaining, some who, execution⟩)
  let value := baseUtility setup leaks utility (some ⟨remaining, some who, execution⟩) who
  have constant : ∀ final ∈ law.support, baseUtility setup leaks utility final who = value := by
    intro final reached
    unfold baseUtility
    rw [sourceServiceCompleted_finish_readout initial horizon scheduler players who remaining
      execution complete final reached]
    rfl
  have integrable := payoffIntegrable_congr_on_support (fun final supported =>
    (constant final supported).symm) (payoffIntegrable_constant law value)
  rw [TerminalAudit.expect_utility law (baseUtility setup leaks utility)
    ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
    deposit who integrable]
  have base := (expect_congr_on_support constant).trans (expect_constant law value)
  rw [base]
  exact sub_le_self _ (mul_nonneg (expect_nonneg law _ fun final _ =>
    (TerminalAudit.charge_mem_Icc ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) final who).1) nonnegative)

variable [Fintype Player]

namespace AsyncServiceSpec

variable (service : AsyncServiceSpec Player L)

/-- At a compatible actual raw prefix with a completed cut, silence preserves
zero owner charge against arbitrary foreign raw continuations. The conclusion
uses the actual later settled record and authentic partial sampling. -/
theorem sourceCompatibleInfo_completed_silent_continuation
    (who : Player) (remaining : Nat)
    (execution : (application service.setup service.leaks).Execution)
    (trace : ((application service.setup service.leaks).protocol (initialLaw service.setup)
      service.horizon service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who,
        execution.observe (application service.setup service.leaks) who)))
    (complete : execution.application.config.cut.completed = Finset.univ)
    (players : Player → (application service.setup service.leaks).Policy)
    (follows : players who = (application service.setup service.leaks).silentPolicy)
    (response : (application service.setup service.leaks).Action)
    (chosen : response ∈ ((application service.setup service.leaks).silentPolicy
      (execution.recall who)
        (execution.observe (application service.setup service.leaks) who)).support)
    (count : Nat) (within : count ≤ remaining)
    (next : (application service.setup service.leaks).Execution)
    (reached : next ∈ ((application service.setup service.leaks).runRounds service.scheduler players
      count (execution.respond (application service.setup service.leaks) who response)).support)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    next.application.config = execution.application.config ∧
      TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample)
          (some ⟨remaining - count, none, next⟩) who = 0 := by
  let app := application service.setup service.leaks
  obtain ⟨noMiss, allowed⟩ := service.sourceCompatibleInfo_raw_history_clear
    ⟨remaining, some who, execution⟩ trace who compatible
  have inputs := app.stateTraffic_inputs (initialLaw service.setup) service.horizon
    service.scheduler trace
  change (app.executionTraffic execution).map ReactiveApplication.TrafficRecord.envelope =
    execution.network.inputs at inputs
  have initialGood : ∀ message, message.sender = who →
      Emitted service.setup service.leaks execution message →
      SettledGood service.setup service.leaks execution message := by
    intro message authored emitted
    unfold Emitted at emitted
    rw [← inputs] at emitted
    obtain ⟨record, member, same⟩ := List.mem_map.mp emitted
    apply completed_permitted_good execution complete message
    rw [← same]
    exact allowed record member (same ▸ authored)
  let invariant := completed_silent_invariant players who follows execution.application.config
    complete
  have initial : execution.application.config = execution.application.config ∧
      SettledFacts service.setup service.leaks execution ∧
        execution.application.publicView.missedDecisionBy who = false ∧
        ∀ message, message.sender = who → Emitted service.setup service.leaks execution message →
          SettledGood service.setup service.leaks execution message :=
    ⟨rfl, settledFacts_history (initialLaw service.setup) service.horizon service.scheduler trace,
      noMiss, initialGood⟩
  have firstChosen : response ∈ (players who (execution.recall who)
      (execution.observe app who)).support := by
    rw [follows]
    exact chosen
  obtain ⟨same, _, noMissNext, goodNext⟩ := invariant.runRounds service.scheduler count _ next
    (invariant.respond execution who response initial firstChosen) reached
  refine ⟨same, ?_⟩
  obtain ⟨responseTrace⟩ := app.raw_trace_respond (initialLaw service.setup) service.horizon
    service.scheduler remaining execution who response trace
  have budgetTrace : (app.protocol (initialLaw service.setup) service.horizon
      service.scheduler).Trace (some ⟨(remaining - count) + count, none,
        execution.respond app who response⟩) := by
    simpa only [Nat.sub_add_cancel within] using responseTrace
  obtain ⟨nextTrace⟩ := app.raw_trace_runRounds (initialLaw service.setup) service.horizon
    service.scheduler players (remaining - count) count _ next budgetTrace reached
  have nextInputs := app.stateTraffic_inputs (initialLaw service.setup) service.horizon
    service.scheduler nextTrace
  change (app.executionTraffic next).map ReactiveApplication.TrafficRecord.envelope =
    next.network.inputs at nextInputs
  unfold sourceServiceAudit
  rw [(runtime service.setup).serviceAudit_charge, noMissNext]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply app.sampledTrafficAudit_sound
  · exact authentic _
  · intro record member authored
    apply SettledGood.permits
    apply goodNext record.envelope authored
    unfold Emitted
    rw [← nextInputs]
    exact List.mem_map.mpr ⟨record, member, rfl⟩

/-- The silent owner's whole physical continuation attains the unchanged base
value, without demanding full observation or constraining foreign policies. -/
theorem sourceCompatibleInfo_completed_silent_value
    (who : Player) (remaining : Nat)
    (execution : (application service.setup service.leaks).Execution)
    (trace : ((application service.setup service.leaks).protocol (initialLaw service.setup)
      service.horizon service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who,
        execution.observe (application service.setup service.leaks) who)))
    (complete : execution.application.config.cut.completed = Finset.univ)
    (players : Player → (application service.setup service.leaks).Policy)
    (follows : players who = (application service.setup service.leaks).silentPolicy)
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) :
    expect ((application service.setup service.leaks).finish (initialLaw service.setup)
      service.horizon service.scheduler players (some ⟨remaining, some who, execution⟩))
        (fun final => TerminalAudit.utility (baseUtility service.setup service.leaks utility)
          ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) deposit final who) =
      baseUtility service.setup service.leaks utility (some ⟨remaining, some who, execution⟩)
        who := by
  let app := application service.setup service.leaks
  let law := app.finish (initialLaw service.setup) service.horizon service.scheduler players
    (some ⟨remaining, some who, execution⟩)
  refine (expect_congr_on_support (μ := law) ?_).trans (expect_constant law _)
  intro final reached
  have readout := sourceServiceCompleted_finish_readout (initialLaw service.setup) service.horizon
    service.scheduler players who remaining execution complete final reached
  change final ∈ (((app.resume players (some who) execution).bind
    (app.runRounds service.scheduler players remaining)).map app.finished).support at reached
  simp only [ReactiveApplication.resume, ReactiveApplication.invoke, follows,
    ReactiveApplication.silentPolicy, PMF.pure_map, PMF.pure_bind] at reached
  obtain ⟨last, continued, rfl⟩ := PMF.support_map .. ▸ reached
  have noCharge := (service.sourceCompatibleInfo_completed_silent_continuation who remaining
    execution trace compatible complete players follows ⟨none⟩ (app.silentPolicy_support _ _)
    remaining le_rfl last continued sample authentic).2
  simp only [Nat.sub_self] at noCharge
  change TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
    (sourceServiceAudit service.setup service.leaks sample) (app.finished last) who = 0 at noCharge
  unfold TerminalAudit.utility
  rw [noCharge, zero_mul, sub_zero]
  unfold baseUtility
  rw [readout]

private theorem completed_information_history
    (menu : (application service.setup service.leaks).ResponseMenu)
    (who : Player)
    (site : (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    (completed : ∀ event, event ∈ view.application.publicView.observation.completionOrder)
    (history : (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).InformationHistory who site.1) :
    ∃ remaining execution, history.1.state = some ⟨remaining, some who, execution⟩ ∧
      service.sourceCompatibleInfo who
        (some (execution.recall who,
          execution.observe (application service.setup service.leaks) who)) ∧
      execution.application.config.cut.completed = Finset.univ := by
  rcases history with ⟨⟨state, trace⟩, same⟩
  change (menu.signals (initialLaw service.setup) service.horizon service.scheduler).infoOf who
    trace = site.1 at same
  rw [menu.info (initialLaw service.setup) service.horizon service.scheduler who trace,
    observed] at same
  cases state with
  | none => cases same
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at same
        have input := Option.some.inj same
        refine ⟨control.remaining, control.execution, ?_, ?_, ?_⟩
        · cases control
          simp only at active ⊢
          rw [active]
        · rw [observed] at compatible
          exact (congrArg some input).symm ▸ compatible
        · apply Finset.eq_univ_of_forall
          intro event
          apply (control.execution.application.config.history_exact event).mp
          have orderEq := congrArg
            (fun pair => pair.2.application.publicView.observation.completionOrder) input
          change control.execution.application.config.history.map EventGraph.Completion.event =
            view.application.publicView.observation.completionOrder at orderEq
          rw [orderEq]
          exact completed event
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at same
        cases same

private theorem completed_native_comparison
    (menu : (application service.setup service.leaks).ResponseMenu)
    (silence : ∀ player past view,
      (⟨none⟩ : (application service.setup service.leaks).Action) ∈ menu.actions player past view)
    (who : Player)
    (site : (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    (completed : ∀ event, event ∈ view.application.publicView.observation.completionOrder)
    (history : (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).InformationHistory who site.1)
    (profile : ∀ player, (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy player)
    (alternative : (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy who)
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who) :
    let model := menu.information (initialLaw service.setup) service.horizon service.scheduler
    let silent := menu.restrictPolicy (initialLaw service.setup) service.horizon service.scheduler
      who (application service.setup service.leaks).silentPolicy
    let payoff := fun final : (menu.protocol (initialLaw service.setup) service.horizon
      service.scheduler).History =>
        TerminalAudit.utility (baseUtility service.setup service.leaks utility)
          ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) deposit final.state who
    expect (model.runBehavioralFrom
      (GameTheory.Profile.update (sig := model.behavioralSignature) profile who alternative)
      (2 * service.horizon + 1) history.1) payoff ≤
      expect (model.runBehavioralFrom
        (GameTheory.Profile.update (sig := model.behavioralSignature) profile who silent)
        (2 * service.horizon + 1) history.1) payoff := by
  intro model silent payoff
  let app := application service.setup service.leaks
  obtain ⟨remaining, execution, current, actualCompatible, complete⟩ :=
    completed_information_history service menu who site compatible past view observed completed
      history
  have traced := menu.toRawTrace (initialLaw service.setup) service.horizon service.scheduler
    history.1.trace
  have enough : app.rank service.horizon history.1.state ≤ 2 * service.horizon + 1 :=
    (Nat.le_add_left _ _).trans (app.trace_bound _ _ _ traced)
  have silentDecoded : app.decodePolicy (menu.embedPolicy (initialLaw service.setup)
      service.horizon service.scheduler who silent) = app.silentPolicy := by
    apply menu.decode_restrictPolicy_of_covered
    intro earlier atView response chosen
    obtain rfl := app.silentPolicy_cases _ _ response chosen
    exact silence who earlier atView
  have silentFollow : menu.decodeProfile (initialLaw service.setup) service.horizon
      service.scheduler
      (GameTheory.Profile.update (sig := model.behavioralSignature) profile who silent) who =
        app.silentPolicy := by
    rw [menu.decodeProfile_update]
    exact (Function.update_self _ _ _).trans silentDecoded
  have alternateLaw := menu.run_eq_finish (initialLaw service.setup) service.horizon
    service.scheduler
    (GameTheory.Profile.update (sig := model.behavioralSignature) profile who alternative)
      (2 * service.horizon + 1) history.1 enough
  have silentLaw := menu.run_eq_finish (initialLaw service.setup) service.horizon
    service.scheduler
    (GameTheory.Profile.update (sig := model.behavioralSignature) profile who silent)
      (2 * service.horizon + 1) history.1 enough
  let audited := fun final : app.ProtocolState =>
    TerminalAudit.utility (baseUtility service.setup service.leaks utility)
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit final who
  have alternateValue := (expect_map ExecutionProtocol.History.state
    (model.runBehavioralFrom
      (GameTheory.Profile.update (sig := model.behavioralSignature) profile who alternative)
      (2 * service.horizon + 1) history.1) audited).symm.trans
        (congrArg (fun law => expect law audited) alternateLaw)
  have alternateAt := congrArg (fun state => expect (app.finish (initialLaw service.setup)
    service.horizon service.scheduler (menu.decodeProfile (initialLaw service.setup)
      service.horizon service.scheduler
      (GameTheory.Profile.update (sig := model.behavioralSignature) profile who alternative)) state)
        audited) current
  have silentValue := (expect_map ExecutionProtocol.History.state
    (model.runBehavioralFrom
      (GameTheory.Profile.update (sig := model.behavioralSignature) profile who silent)
      (2 * service.horizon + 1) history.1) audited).symm.trans
        (congrArg (fun law => expect law audited) silentLaw)
  have silentAt := congrArg (fun state => expect (app.finish (initialLaw service.setup)
    service.horizon service.scheduler (menu.decodeProfile (initialLaw service.setup)
      service.horizon service.scheduler
      (GameTheory.Profile.update (sig := model.behavioralSignature) profile who silent)) state)
        audited) current
  have exactValue := service.sourceCompatibleInfo_completed_silent_value who remaining execution
    (current ▸ traced) actualCompatible complete
    (menu.decodeProfile (initialLaw service.setup) service.horizon service.scheduler
      (GameTheory.Profile.update (sig := model.behavioralSignature) profile who silent))
      silentFollow
      utility sample authentic deposit
  have alternateBound := sourceServiceCompleted_finish_value_le (initialLaw service.setup)
    service.horizon
    service.scheduler (menu.decodeProfile (initialLaw service.setup) service.horizon
      service.scheduler
      (GameTheory.Profile.update (sig := model.behavioralSignature) profile who alternative))
      who remaining
        execution complete utility sample deposit nonnegative
  exact (alternateValue.trans alternateAt).trans_le
    (alternateBound.trans_eq (silentValue.trans (silentAt.trans exactValue)).symm)

/-- In an actual finite response menu retaining silence, silent whole continuation is optimal
at a compatible owner input whose public record shows every event complete.
The comparison covers every hidden history under any belief and arbitrary
foreign menu policies. It does not supply rationality at unfinished sites. -/
theorem sourceCompatibleInfo_completed_silent_optimal
    (menu : (application service.setup service.leaks).ResponseMenu)
    (silence : ∀ player past view,
      (⟨none⟩ : (application service.setup service.leaks).Action) ∈ menu.actions player past view)
    (who : Player)
    (site : (menu.information
      (initialLaw service.setup) service.horizon service.scheduler).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    (completed : ∀ event, event ∈ view.application.publicView.observation.completionOrder)
    (assessment : (menu.information
      (initialLaw service.setup) service.horizon service.scheduler).BehavioralAssessment)
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who) :
    let silent := menu.restrictPolicy (initialLaw service.setup) service.horizon service.scheduler
      who (application service.setup service.leaks).silentPolicy
    (assessment.truncatedContinuationContext site
      (fun final => TerminalAudit.utility (baseUtility service.setup service.leaks utility)
        ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) deposit final.state who)
      (2 * service.horizon + 1)).IsLocallyOptimal Set.univ silent := by
  intro silent
  let model := menu.information (initialLaw service.setup) service.horizon service.scheduler
  let payoff := fun final : (menu.protocol (initialLaw service.setup) service.horizon
    service.scheduler).History =>
      TerminalAudit.utility (baseUtility service.setup service.leaks utility)
        ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) deposit final.state who
  let context := assessment.truncatedContinuationContext site payoff (2 * service.horizon + 1)
  have integrable (alternative : model.BehavioralPolicy who) : context.IntegrableAt alternative :=
    payoffIntegrable_of_finite _ _
  apply GameTheory.Protocol.Context.isLocallyOptimal_iff_of_integrable (integrable silent)
    (fun alternative _ => integrable alternative) |>.mpr
  intro alternative _
  have alternateTower := assessment.continuationContextWith_value_tower
    (model.truncatedRunner (2 * service.horizon + 1)) site payoff alternative
      (integrable alternative)
  have silentTower := assessment.continuationContextWith_value_tower
    (model.truncatedRunner (2 * service.horizon + 1)) site payoff silent (integrable silent)
  refine alternateTower.trans_le ((expect_mono ?_ (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)).trans_eq silentTower.symm)
  intro history _
  exact completed_native_comparison service menu silence who site compatible past view observed
    completed history assessment.strategy alternative utility sample authentic deposit nonnegative

end AsyncServiceSpec

end Vegas
