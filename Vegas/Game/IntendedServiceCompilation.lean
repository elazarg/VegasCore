/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.IntendedPreservation
import Vegas.Game.SourceServiceCompilation
import Vegas.Game.SourceServiceChoiceSupport

/-! # Intended equilibria in the audited calendar runtime

Composing intended-game preservation
(`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_preserved`) with the
audited calendar runtime
(`Vegas.SourceServiceSpec.audited_raw_sequentialEquilibrium_preserved`) at the
forfeited utility gives, for a well-formed setup, a sequential equilibrium of the
bounded raw runtime for every sequential equilibrium of the intended game. Its
joint law of terminal store and realized settlement is the intended law of
terminal store and payoff, the audit charges no player on its paths, and no
reveal fails on them. The deposit is the one the runtime fixes for the forfeited
utility, whose range grows with the forfeit times the number of reveals.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- **Intended equilibria in the audited calendar runtime.** For a well-formed
setup, every sequential equilibrium of the intended game has a sequential
equilibrium of the audited bounded raw runtime under the forfeit pass, with the
intended joint law of terminal store and payoff realized as settlement, no
charge and no failed reveal on its paths. -/
theorem intended_audited_raw_sequentialEquilibrium {Parameter : Type}
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (intended : service.setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium service.setup.intended_decision_antichain
      service.setup.intended_bounded.wellFoundedHistories
      (fun who final => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who))) :
    let forfeited := forfeitUtility service.setup.program forfeit utility
    let raw := service.bounds.rawMenu (runtime service.setup) service.leaks
    let base := baseUtility service.setup service.leaks
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    ∃ target : (raw.information (initialLaw service.setup) service.planLength
        service.scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain (initialLaw service.setup) service.planLength
          service.scheduler) service.rawTerminates
        (fun who history => payoff history.state who) ∧
      (∀ final ∈ ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioralTerminalFrom service.rawTerminates target.strategy
            service.rawInitial).support, ∀ who,
        TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) final.state who = 0) ∧
      (∀ final ∈ ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioralTerminalFrom service.rawTerminates target.strategy
            service.rawInitial).support, ∀ terminal,
        sourceReadout service.setup service.leaks final.state = some terminal → ∀ who,
          failedReveals service.setup.program who
            (publicOutcome service.setup.program terminal) = 0) ∧
      ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioralTerminalFrom service.rawTerminates target.strategy
            service.rawInitial).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (sourceReadout service.setup service.leaks final.state, payoffs))) =
        (service.setup.intendedModel.runBehavioralTerminalFrom
            service.setup.intended_bounded.wellFoundedHistories intended.strategy
            service.setup.intendedProtocol.initHistory).map
          (fun final => (service.setup.protocolReadout final.state,
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who))) := by
  intro forfeited raw base deposit payoff settle
  obtain ⟨source, sourceEquilibrium, _, sourceLaw⟩ :=
    service.setup.intended_sequentialEquilibrium_preserved
      (CommitmentInterface.values service.setup.program)
      (sourceService_finiteBindingTypes service.setup service.bounds service.values)
      wellFormed parameter utility forfeit range _ service.sourceTerminates intended equilibrium
  obtain ⟨target, targetEquilibrium, uncharged, targetLaw⟩ :=
    service.audited_raw_sequentialEquilibrium_preserved parameter forfeited sample authentic
      probability positive coverage source sourceEquilibrium
  have law := targetLaw.trans sourceLaw
  refine ⟨target, targetEquilibrium, uncharged, ?_, law⟩
  intro final reached terminal read who
  obtain ⟨payoffs, settled⟩ := (settle final.state).support_nonempty
  have member : (sourceReadout service.setup service.leaks final.state, payoffs) ∈
      (((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioralTerminalFrom service.rawTerminates target.strategy
            service.rawInitial).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (sourceReadout service.setup service.leaks final.state, payoffs)))).support :=
    (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨final, reached, (PMF.mem_support_map_iff _ _ _).mpr ⟨payoffs, settled, rfl⟩⟩
  rw [law, PMF.support_map] at member
  obtain ⟨intendedFinal, _, same⟩ := member
  have intendedRead : service.setup.protocolReadout intendedFinal.state = some terminal :=
    (congrArg Prod.fst same).trans read
  exact service.setup.failedReveals_eq_zero_of_intendedState
    (service.setup.intendedState_trace wellFormed intendedFinal.trace) who intendedRead

end SourceServiceSpec

end Vegas
