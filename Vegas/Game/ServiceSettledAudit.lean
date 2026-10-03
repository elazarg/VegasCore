/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAudit
import Vegas.Game.ServiceSettledEvidence
import Vegas.Pending.ReactiveAuditEquilibrium
import GameTheoryExtensions.Analysis.Protocol.TerminalPayoffCongruence

/-! # Settled terminal audits in the bounded native runtime

The contract settles once every event has completed. Settlement samples
authentic signed packets, judges each against the settled record
(`Vegas.EventGraphRuntime.SettledRecord.Permits`), and charges the packet's
author. The audit uses `Vegas.EventGraphRuntime.serviceAuditObservation` at
every history; settlement pays out only after complete play.

Any retained response menu whose settled executions are clean, and whose every
additional response transmits a packet breaking the send-time conformance rule,
extends to the full bounded raw game. The send-time rule is a proof device: a
breach dooms its author, so a complete settlement forbids some packet the author
signed (`Vegas.settled_breach_of_sendTime_breach`). No verdict reads when a
packet was sent.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- After one response that breaks the send-time rule, every complete
continuation charges its author with at least the sampling rate. Subsequent
responses and scheduling are arbitrary. -/
theorem settledAudit_collection_after_step (count : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (menu : (application setup leaks).ResponseMenu)
    (completes : ∀ (history : (menu.protocol (initialLaw setup) count scheduler).History)
      control, history.state = some control → (application setup leaks).terminal history.state →
        control.execution.application.config.cut.Terminal)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (who : Player) (rate : ℝ)
    (coverage : ∀ actual (record : SettledEvidence setup), record ∈ actual →
      record.2.sender = who → record.1.permits record.2 = false →
      rate ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (profile : ∀ player,
      (menu.information (initialLaw setup) count scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol (initialLaw setup) count scheduler).History)
    (long : 2 * count + 1 ≤ history.trace.length + 1 + fuel)
    (evidence : ∀ next ∈ ((menu.information (initialLaw setup) count scheduler).runBehavioralFrom
      profile 1 history).support,
      ∃ record ∈ (application setup leaks).stateTraffic next.state,
        record.envelope.sender = who ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.envelope = false) :
    rate ≤ ((((((menu.information (initialLaw setup) count scheduler).runBehavioralFrom profile
      (1 + fuel) history).map (fun final =>
        (runtime setup).serviceAuditObservation leaks final.state)).bind
          (sourceServiceAudit setup leaks sample)).map (fun verdict => verdict who))
            true).toReal := by
  let app := application setup leaks
  let model := menu.information (initialLaw setup) count scheduler
  let protocol := menu.protocol (initialLaw setup) count scheduler
  rw [model.runBehavioralFrom_add, TerminalAudit.collection_probability,
    expect_bind_tower _ _ _ (TerminalAudit.payoffIntegrable_charge _ _ _ _)]
  calc
    rate = expect (model.runBehavioralFrom profile 1 history) (fun _ => rate) :=
      (expect_constant _ _).symm
    _ ≤ _ := by
      refine expect_mono ?_ (payoffIntegrable_constant _ _) ?_
      rotate_left
      · exact payoffIntegrable_of_bounded _ _ (C := 1) fun next => by
          rw [abs_of_nonneg (expect_nonneg _ _ fun _ _ =>
            (TerminalAudit.charge_mem_Icc _ _ _ _).1)]
          exact expect_le_const _ _ (TerminalAudit.payoffIntegrable_charge _ _ _ _) _
            fun _ _ => (TerminalAudit.charge_mem_Icc _ _ _ _).2
      intro next stepped
      obtain ⟨record, present, author, breach⟩ := evidence next stepped
      calc
        rate = expect (model.runBehavioralFrom profile fuel next) (fun _ => rate) :=
          (expect_constant _ _).symm
        _ ≤ _ := by
          refine expect_mono ?_ (payoffIntegrable_constant _ _)
            (TerminalAudit.payoffIntegrable_charge _ _ _ _)
          intro final supported
          have path := protocol.runRandomizedFor_reachesWithin
            (model.randomizedChooser profile) fuel next final supported
          have kept : record ∈ app.stateTraffic final.state := by
            have reaches := (menu.trafficAudit_reaches (initialLaw setup) count scheduler
              path).subset
            rw [menu.trafficAudit_eq_stateTraffic, menu.trafficAudit_eq_stateTraffic] at reaches
            exact reaches present
          have stopped : app.terminal final.state := by
            rcases protocol.runRandomizedFor_terminal_or_length
                (model.randomizedChooser profile) 1 history next stepped with
              nextStopped | nextLong
            · have same := path.eq_of_terminal nextStopped
              rw [same]
              exact nextStopped
            · rcases protocol.runRandomizedFor_terminal_or_length
                  (model.randomizedChooser profile) fuel next final supported with
                finalStopped | finalLong
              · exact finalStopped
              · have finalBound := app.trace_bound (initialLaw setup) count scheduler
                  (menu.toRawTrace (initialLaw setup) count scheduler final.trace)
                rw [menu.toRawTrace_length] at finalBound
                have empty : app.rank count final.state = 0 := by omega
                exact (app.rank_zero count final.state).mp empty
          have settledFinal := completes final
          rcases final with ⟨state, trace⟩
          cases state with
          | none => exact stopped.elim
          | some control =>
              have rawTrace := menu.toRawTrace (initialLaw setup) count scheduler trace
              have settled := settledFinal control rfl stopped
              change record ∈ app.executionTraffic control.execution at kept
              obtain ⟨other, otherPresent, sameAuthor, forbidden⟩ :=
                settled_breach_of_sendTime_breach (initialLaw setup) count scheduler rawTrace
                  settled record kept breach
              change rate ≤ TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
                ((runtime setup).serviceAudit leaks _) (some control) who
              exact (runtime setup).serviceAudit_charge_from_record leaks
                (fun settled traffic => (settled, traffic.envelope))
                (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
                sample who rate coverage control other otherPresent (sameAuthor.trans author)
                forbidden

open Classical in
/-- **Settled audits preserve sequential equilibrium.** Clean settled
executions of the retained menu, and a send-time breach by every additional
response, suffice for standard SE in the full bounded raw game with the actual
randomized settlement law. Audit randomness and player verdicts may be
correlated. -/
theorem settled_audited_raw_sequential_equilibrium
    (bounds : MessageBounds (graph setup)) (count : Nat)
    (scheduler : (application setup leaks).Scheduler)
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    (retained : (application setup leaks).ResponseMenu)
    (included : retained.IncludedIn (bounds.menu (runtime setup) leaks))
    (completes : ∀ (history : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
      count scheduler).History) control, history.state = some control →
        (application setup leaks).terminal history.state →
          control.execution.application.config.cut.Terminal)
    (depth : ∀ who,
      (retained.information (initialLaw setup) count scheduler).InformationSite who → Nat)
    (clock : ∀ who site, InformationModel.InformationSite.CommonDepth
      ((bounds.menu (runtime setup) leaks).information (initialLaw setup) count scheduler)
      ((included.actionRestriction (initialLaw setup) count scheduler).site who site)
      (depth who site))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (conforming : ∀ (history : (retained.protocol (initialLaw setup) count scheduler).History)
      (control : (application setup leaks).Control), history.state = some control →
      (application setup leaks).terminal history.state →
        (∀ who, control.execution.application.publicView.missedDecisionBy who = false) ∧
        ∀ record ∈ (application setup leaks).executionTraffic control.execution,
          ((runtime setup).settledRecord leaks control.execution).permits
            record.envelope = true)
    (evidence : ∀ (profile : Profile ((bounds.menu (runtime setup) leaks).information
        (initialLaw setup) count scheduler).behavioralSignature) who
      (site : (retained.information (initialLaw setup) count scheduler).InformationSite who)
      (action : ((bounds.menu (runtime setup) leaks).information (initialLaw setup) count
        scheduler).Choice who
        ((included.actionRestriction (initialLaw setup) count scheduler).site who site).1),
      action ∉ Set.range ((included.actionRestriction (initialLaw setup) count scheduler).choice
        who site.1) →
      ∀ history : (retained.information (initialLaw setup) count scheduler).InformationHistory
        who site.1,
      ∀ next ∈ (((bounds.menu (runtime setup) leaks).information (initialLaw setup) count
        scheduler).runBehavioralFrom
        (Profile.update profile who ((profile who).commit
          ((included.actionRestriction (initialLaw setup) count scheduler).site who site).1
            action))
        1 ((included.actionRestriction (initialLaw setup) count scheduler).history
          history.1)).support,
      ∃ record ∈ (application setup leaks).stateTraffic next.state,
        record.envelope.sender = who ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.envelope = false)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (baseInvariant : ∀ state,
      base (((runtime setup).reactiveNormalization leaks).state state) = base state)
    (lower upper probability deposit : Player → ℝ)
    (nonnegative : ∀ who, 0 ≤ deposit who)
    (below : ∀ (history : (retained.protocol (initialLaw setup) count scheduler).History) who,
      lower who ≤ base history.state who)
    (above : ∀ (history : ((bounds.menu (runtime setup) leaks).protocol
        (initialLaw setup) count scheduler).History) who,
      base history.state who ≤ upper who)
    (sufficient : ∀ who, upper who - probability who * deposit who ≤ lower who)
    (coverage : ∀ who actual (record : SettledEvidence setup), record ∈ actual →
      record.2.sender = who → record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    {Observation : Type}
    (observe : (application setup leaks).ProtocolState → Observation)
    (observationInvariant : ∀ state,
      observe (((runtime setup).reactiveNormalization leaks).state state) = observe state)
    (source : (retained.information (initialLaw setup) count scheduler).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      (retained.decisionInformationAntichain (initialLaw setup) count scheduler)
      (fun who site => source.truncatedContinuationContext site (fun final => base final.state who)
        (2 * count + 1))) :
    let audit := sourceServiceAudit setup leaks sample
    let observeAudit := (runtime setup).serviceAuditObservation leaks
    let utility := TerminalAudit.utility base observeAudit audit deposit
    let settle := TerminalAudit.settlement base observeAudit audit deposit
    ∃ target : ((bounds.rawMenu (runtime setup) leaks).information (initialLaw setup) count
        scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu (runtime setup) leaks).decisionInformationAntichain (initialLaw setup)
          count scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun final => utility final.state who) (2 * count + 1)) ∧
      (((bounds.rawMenu (runtime setup) leaks).information (initialLaw setup) count
        scheduler).runBehavioral target.strategy (2 * count + 1)).bind
          (fun final => (settle final.state).map (fun payoffs => (observe final.state, payoffs))) =
        ((retained.information (initialLaw setup) count scheduler).runBehavioral source.strategy
          (2 * count + 1)).map
            (fun final => (observe final.state, base final.state)) := by
  classical
  intro audit observeAudit utility settle
  let initial := initialLaw setup
  let app := application setup leaks
  let effective := bounds.menu (runtime setup) leaks
  let restriction := included.actionRestriction initial count scheduler
  have sourceBounded := retained.bounded initial count scheduler
  have sourceCertificate := sourceBounded.wellFoundedHistories
  have targetBounded := effective.bounded initial count scheduler
  have targetCertificate := targetBounded.wellFoundedHistories
  -- The extension lemma needs zero charge at every retained history. This
  -- internal observation agrees with the actual audit on complete continuations.
  let proofObserve (state : app.ProtocolState) :=
    if app.terminal state then observeAudit state else ([], none)
  have proofObserve_terminal (state : app.ProtocolState) (stopped : app.terminal state) :
      proofObserve state = observeAudit state := ite_eq_left stopped
  have terminalObservation
      (profile : ∀ who, (effective.information initial count scheduler).BehavioralPolicy who)
      (history : (effective.protocol initial count scheduler).History) :
      ((effective.information initial count scheduler).runBehavioralTerminalFrom
        targetCertificate profile history).map (fun final => proofObserve final.state) =
      ((effective.information initial count scheduler).runBehavioralTerminalFrom
        targetCertificate profile history).map (fun final => observeAudit final.state) := by
    apply map_congr_on_support _
    intro final supported
    exact proofObserve_terminal final.state
      ((effective.information initial count scheduler).runBehavioralTerminalFrom_support_terminal
        targetCertificate profile history final supported)
  have sourceTerminal := (source.isSequentialEquilibrium_iff_truncated_of_bounded
    (retained.information initial count scheduler)
    (retained.decisionInformationAntichain initial count scheduler) sourceCertificate
    sourceBounded (fun who final => base final.state who)).mpr equilibrium
  have sound (history : (retained.protocol initial count scheduler).History) (who : Player) :
      TerminalAudit.charge (fun final => proofObserve final.state) audit
        (restriction.history history) who = 0 := by
    change TerminalAudit.charge proofObserve audit history.state who = 0
    by_cases settled : app.terminal history.state
    · rw [show TerminalAudit.charge proofObserve audit history.state who =
          TerminalAudit.charge observeAudit audit history.state who by
        unfold TerminalAudit.charge
        rw [proofObserve_terminal _ settled]]
      obtain ⟨state, trace⟩ := history
      cases state with
      | none => exact settled.elim
      | some control =>
      obtain ⟨complete, permitted⟩ := conforming ⟨_, trace⟩ control rfl settled
      change TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
        ((runtime setup).serviceAudit leaks _) (some control) who = 0
      rw [(runtime setup).serviceAudit_charge, complete who]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply app.sampledTrafficAudit_sound
      · exact authentic _
      · intro record member _
        exact permitted record member
    · unfold TerminalAudit.charge
      rw [show proofObserve history.state = ([], none) from ite_eq_right settled]
      change (((PMF.pure fun _ : Player => false).map (fun verdict => verdict who)) true).toReal = 0
      rw [PMF.pure_map, PMF.pure_apply_of_ne _ _ Bool.noConfusion, ENNReal.toReal_zero]
  have collection (profile : Profile
      (effective.information initial count scheduler).behavioralSignature) who
      (site : (retained.information initial count scheduler).InformationSite who)
      (action : (effective.information initial count scheduler).Choice who
        (restriction.site who site).1)
      (extra : action ∉ Set.range (restriction.choice who site.1))
      (history : (retained.information initial count scheduler).InformationHistory who site.1) :
      probability who ≤
        (((((InformationModel.runBehavioralTerminalFrom
        (effective.information initial count scheduler) targetCertificate
        (Profile.update profile who ((profile who).commit (restriction.site who site).1 action))
        (restriction.history history.1)).map (fun final => proofObserve final.state)).bind
          audit).map (fun verdict => verdict who)) true).toReal := by
    rw [terminalObservation]
    have length : (restriction.history history.1).trace.length = depth who site := by
      have same := clock who site (restriction.informationHistory who site history)
      simpa only [InformationModel.ActionRestriction.informationHistory_val] using same
    rw [InformationModel.runBehavioralTerminalFrom_eq_remaining _ targetCertificate _
      targetBounded, length]
    have within : depth who site < 2 * count + 1 := by
      obtain ⟨reference, running, _action⟩ := site.2
      have sameDepth := clock who site (restriction.informationHistory who site reference)
      simp only [InformationModel.ActionRestriction.informationHistory_val,
        restriction.length] at sameDepth
      by_contra late
      exact running (retained.bounded initial count scheduler reference.1.state
        reference.1.trace (by
          change ¬ depth who site < 2 * count + 1 at late
          omega))
    have bound := settledAudit_collection_after_step setup leaks count scheduler effective
      completes sample who (probability who) (coverage who)
      (Profile.update profile who ((profile who).commit (restriction.site who site).1 action))
      (2 * count + 1 - depth who site - 1) (restriction.history history.1)
      (by rw [length]; omega) (evidence profile who site action extra history)
    have fuel : 1 + (2 * count + 1 - depth who site - 1) = 2 * count + 1 - depth who site := by
      omega
    simpa only [fuel] using bound
  obtain ⟨effectiveTarget, targetTerminal, _agrees, _beliefs, _historyLaw, joint, _clean⟩ :=
    restriction.sequential_equilibrium_extends_of_terminal_audit
      (retained.decisionInformationAntichain initial count scheduler) sourceCertificate
      targetCertificate (effective.uniformAssessment initial count scheduler)
      (effective.uniform_fullyMixed initial count scheduler)
      (effective.decisionRecall initial count scheduler)
      depth clock
      (fun final who => base final.state who) (fun final who => base final.state who)
      (fun final => proofObserve final.state) audit (fun _ _ => rfl) sound
      lower upper probability deposit nonnegative below above sufficient collection source
      sourceTerminal
  have actualTerminal :=
    (effectiveTarget.isSequentialEquilibrium_iff_of_terminal_payoff_eq
      (effective.decisionRecall initial count scheduler).decisionInformationAntichain
      targetCertificate
      (fun who final => TerminalAudit.utility (fun history who => base history.state who)
        (fun history => proofObserve history.state) audit deposit final who)
      (fun who final => utility final.state who) (fun who final stopped => by
        simp only [TerminalAudit.utility, TerminalAudit.charge,
          proofObserve_terminal final.state stopped, utility])).mp targetTerminal
  have actualJoint :
      ((retained.information initial count scheduler).runBehavioralTerminalFrom
        sourceCertificate source.strategy
          (retained.protocol initial count scheduler).initHistory).map
          (fun history => (restriction.history history, base history.state)) =
      ((effective.information initial count scheduler).runBehavioralTerminalFrom
        targetCertificate effectiveTarget.strategy
          (effective.protocol initial count scheduler).initHistory).bind
          (fun history => (settle history.state).map (fun payoffs => (history, payoffs))) := by
    refine joint.trans ?_
    apply bind_congr_on_support _
    intro final supported
    have stopped :=
      (effective.information initial count scheduler).runBehavioralTerminalFrom_support_terminal
        targetCertificate effectiveTarget.strategy
        (effective.protocol initial count scheduler).initHistory final supported
    simp only [TerminalAudit.settlement, proofObserve_terminal final.state stopped, settle]
  rw [InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded _
      sourceCertificate sourceBounded,
    InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded _
      targetCertificate targetBounded] at actualJoint
  have targetFull := (effectiveTarget.isSequentialEquilibrium_iff_truncated_of_bounded
    (effective.information initial count scheduler)
    (effective.decisionRecall initial count scheduler).decisionInformationAntichain
    targetCertificate targetBounded (fun who final => utility final.state who)).mp actualTerminal
  obtain ⟨target, _strategy, targetSE, _beliefs, stateLaw⟩ :=
    bounds.exists_canonicalRaw_sequentialEquilibrium (runtime setup) leaks initial count
      scheduler effectiveTarget (fun who state => utility state who) targetFull
  have observationAudit (state : app.ProtocolState) :
      observeAudit (((runtime setup).reactiveNormalization leaks).state state) =
        observeAudit state :=
    (runtime setup).serviceAuditObservation_normalization leaks _ state
  have utilityInvariant (state : app.ProtocolState) :
      utility (((runtime setup).reactiveNormalization leaks).state state) = utility state := by
    funext who
    simp only [utility, TerminalAudit.utility, TerminalAudit.charge, baseInvariant,
      observationAudit]
  have settlementInvariant (state : app.ProtocolState) :
      settle (((runtime setup).reactiveNormalization leaks).state state) = settle state := by
    simp only [settle, TerminalAudit.settlement, observationAudit, baseInvariant]
  refine ⟨target, ?_, ?_⟩
  · simpa only [utilityInvariant] using targetSE
  · have rawJoint := congrArg (fun law => law.bind fun state =>
        (settle state).map (fun payoffs => (observe state, payoffs))) stateLaw
    simp only [PMF.bind_map, Function.comp_def, settlementInvariant, observationInvariant]
      at rawJoint
    rw [rawJoint]
    have projected := congrArg (fun law => law.map fun result =>
      (observe result.1.state, result.2)) actualJoint
    have sameState (history : (retained.protocol initial count scheduler).History) :
        (restriction.history history).state = history.state := rfl
    simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, sameState,
      settle, TerminalAudit.settlement, InformationModel.runBehavioral] using projected.symm

end Vegas
