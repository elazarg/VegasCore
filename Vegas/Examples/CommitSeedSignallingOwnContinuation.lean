/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingTimingIncentives
import Interaction.ReactiveLocalContinuation

/-! # A clean owner's actual assessed continuation with arbitrary foreign history -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob)

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
  obtain ⟨choice, chosen, value⟩ := supported
  change choice.1.getD ⟨none⟩ = response at value
  obtain ⟨physical, _available, physicalEq⟩ := choice.2
  rw [physicalEq, Option.getD_some] at value
  have selected : choice.1 = some response := physicalEq.trans (congrArg some value)
  exact clean_supported_response_counted assessment equilibrium who target past view rfl
    clean choice chosen response selected

private theorem assessed_controlStep_ownPermitted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (history : rawProtocol.History)
    (valid : ReactiveApplication.executionInvariant (OwnPermitted who) history.state)
    (next : app.ProtocolState)
    (reached : next ∈ (app.controlStep initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      history.state).support) :
    ReactiveApplication.executionInvariant (OwnPermitted who) next := by
  classical
  cases state : history.state with
  | none =>
      simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, state,
        Option.bind_none, ReactiveApplication.transition] at reached
      obtain ⟨native, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact ownPermitted_initial who native
  | some current =>
      rcases current with ⟨remaining, active, execution⟩
      rw [state] at valid
      change OwnPermitted who execution at valid
      cases active with
      | none =>
          cases remaining with
          | zero =>
              simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, state,
                Option.bind_some, ReactiveApplication.transition, PMF.mem_support_pure_iff]
                at reached
              cases reached
              exact valid
          | succ remaining =>
              simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, state,
                Option.bind_some, ReactiveApplication.transition, PMF.support_bind] at reached
              obtain ⟨command, _chosen, moved⟩ := Set.mem_iUnion₂.mp reached
              obtain ⟨executionNext, environmentMoved, sameState⟩ := PMF.support_map .. ▸ moved
              cases sameState
              exact ownPermitted_environment who execution executionNext command valid
                environmentMoved
      | some actor =>
          simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, state,
            Option.bind_some, PMF.support_bind] at reached
          obtain ⟨response, supported, moved⟩ := Set.mem_iUnion₂.mp reached
          simp only [ReactiveApplication.transition, ite_true, Option.getD_some,
            PMF.mem_support_pure_iff] at moved
          cases moved
          change OwnPermitted who (execution.respond app actor response)
          by_cases same : actor = who
          · subst actor
            have running : ¬ rawProtocol.terminal history.state := by
              rw [state]
              intro stopped
              cases stopped.2
            have acts : rawProtocol.active history.state who := by rw [state]; rfl
            obtain ⟨site, observed⟩ := rawModel.exists_informationSite_of_active who history
              running acts
            have atSite : site.1 = some (execution.recall who, execution.observe app who) := by
              rw [observed]
              change (rawMenu.signals initial horizon scheduler).infoOf who history.trace = _
              rw [rawMenu.info, state]
              simp only [ReactiveApplication.observe, ite_true]
            have clean := (ownPermitted_iff_past who execution valid.1).mp valid
            exact ownPermitted_counted_respond who execution response valid
              (raw_equilibrium_clean_response_counted assessment equilibrium who site _ _
                atSite clean response supported)
          · exact ownPermitted_respond who actor execution response valid
              (fun equal => (same equal).elim)

private theorem assessed_one_ownPermitted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (history final : rawProtocol.History)
    (valid : ReactiveApplication.executionInvariant (OwnPermitted who) history.state)
    (supported : final ∈ (rawModel.runBehavioralFrom assessment.strategy 1 history).support) :
    ReactiveApplication.executionInvariant (OwnPermitted who) final.state := by
  have law := rawMenu.run_map_controlSteps initial horizon scheduler assessment.strategy 1 history
  simp only [Function.iterate_one, PMF.pure_bind] at law
  have stateSupported : final.state ∈
      ((rawModel.runBehavioralFrom assessment.strategy 1 history).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, supported, rfl⟩
  rw [law] at stateSupported
  exact assessed_controlStep_ownPermitted assessment equilibrium who history valid _ stateSupported

/-- Sequential rationality keeps this owner's record clean along the actual
unchanged continuation from every genuine raw history with a clean own past. -/
theorem raw_equilibrium_ownPermitted_run
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (fuel : Nat) (history final : rawProtocol.History)
    (valid : ReactiveApplication.executionInvariant (OwnPermitted who) history.state)
    (supported : final ∈ (rawModel.runBehavioralFrom assessment.strategy fuel history).support) :
    ReactiveApplication.executionInvariant (OwnPermitted who) final.state := by
  induction fuel generalizing history with
  | zero =>
      change final ∈ (PMF.pure history).support at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact valid
  | succ fuel ih =>
      rw [show fuel + 1 = 1 + fuel by omega, rawModel.runBehavioralFrom_add, PMF.support_bind]
        at supported
      obtain ⟨middle, first, future⟩ := Set.mem_iUnion₂.mp supported
      exact ih middle (assessed_one_ownPermitted assessment equilibrium who history middle valid
        first) future

/-- The focal owner incurs no future audit charge; no global assumption on
the opponents' past or future packets is needed. -/
theorem raw_equilibrium_own_clean_terminal_charge_zero
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (history final : rawProtocol.History)
    (valid : ReactiveApplication.executionInvariant (OwnPermitted who) history.state)
    (supported : final ∈ (rawModel.runBehavioralTerminalFrom canonicalCertificate
      assessment.strategy history).support) :
    TerminalAudit.charge app.stateTraffic audit final.state who = 0 := by
  rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
    (rawMenu.bounded initial horizon scheduler)] at supported
  exact ownPermitted_charge_zero who final
    (raw_equilibrium_ownPermitted_run assessment equilibrium who (2 * horizon + 1) history final
      valid supported)

end Vegas.Examples.CommitSeedSignalling
