/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.IntendedNash
import Vegas.Game.SourceServiceNash

/-! # Approximate Nash equilibria of the intended game on the calendar ledger

Composing Nash preservation for the intended game
(`Vegas.SourceProgram.Setup.intended_isεNash_preserved`) with the approximate
Nash correspondence of the audited calendar runtime
(`Vegas.SourceServiceSpec.isεNash_compileProfile_iff`) at the forfeited utility:
for a well-formed setup, the compiled raw profile of every source profile that
extends an `ε`-Nash equilibrium of the intended game is an `ε`-Nash equilibrium
of the audited bounded raw runtime, and its joint law of typed outcome and
audited payoff vector is the intended joint law of terminal store and payoff.
The deposit is the one the runtime fixes for the forfeited utility.
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

/-- **Intended approximate Nash equilibria on the audited calendar ledger.** For
a well-formed setup and a forfeit no smaller than the payoff range, the compiled
raw profile of every source profile extending an `ε`-Nash equilibrium of the
intended game is an `ε`-Nash equilibrium of the audited bounded raw runtime
under the forfeit pass, with the intended joint law of terminal store and
payoff realized as the audited expected payoff. -/
theorem intended_audited_raw_isεNash {Parameter : Type}
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
    (intended : Profile service.setup.intendedModel.behavioralSignature)
    (source : Profile service.sourceModel.behavioralSignature)
    (agrees : service.setup.intendedRestriction.ExtendsProfile intended source) (ε : ℝ)
    (equilibrium : IsεNash (service.setup.intendedModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
      (fun final who => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who)) ε intended) :
    let forfeited := forfeitUtility service.setup.program forfeit utility
    let raw := service.bounds.rawMenu (runtime service.setup) service.leaks
    let base := baseUtility service.setup service.leaks
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    IsεNash ((raw.information (initialLaw service.setup) service.planLength
        service.scheduler).toBehavioralGameForm service.fuel)
        (fun history who => payoff history.state who) ε (service.compileProfile source) ∧
      ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioral (service.compileProfile source) service.fuel).map
          (fun final => (sourceReadout service.setup service.leaks final.state,
            payoff final.state)) =
        (service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => (service.setup.protocolReadout final.state,
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who))) := by
  intro forfeited raw base deposit payoff
  obtain ⟨sourceNash, _, sourceLaw⟩ := service.setup.intended_isεNash_preserved
    (sourceService_finiteBindingTypes service.setup service.bounds service.values)
    wellFormed parameter utility forfeit range intended source agrees ε equilibrium
  exact ⟨(service.isεNash_compileProfile_iff parameter forfeited sample authentic probability
      positive coverage ε source).mpr sourceNash,
    (service.compileProfile_payoff_law parameter forfeited sample authentic probability
      source).trans sourceLaw⟩

end SourceServiceSpec

end Vegas
