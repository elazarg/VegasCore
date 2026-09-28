/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterChoiceEvidence
import Vegas.Game.RevealServiceRosterTrafficSound
import Vegas.Pending.ReactiveAuditEquilibrium
import Vegas.Game.ServicePayoffBounds

/-! # Audited revelation rosters extend to the full bounded native game

One fixed deposit vector, computed from the finite payoff range and a positive
conditional observation rate, suffices for every retained sequential equilibrium.
All traffic certificates and the native decision clock are discharged here.
The audit remains an explicit authentic terminal observation/collection service.
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
  (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
  (network : (runtime setup).NetworkPolicy leaks)

local instance : Nonempty ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History :=
  ⟨((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).initHistory⟩

open Classical in
/-- Standard SE and the joint observation/realized settlement law survive
restoration of every bounded raw response. There is no strategic watcher slot. -/
theorem roster_audited_sequential_equilibrium
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (baseInvariant : ∀ state,
      base (((runtime setup).reactiveNormalization leaks).state state) = base state)
    (sample : List (EnvelopeEvidence setup leaks) → FinDist (List (EnvelopeEvidence setup leaks)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.2.sender = who →
      permittedRosterEnvelope setup leaks record = false →
      probability who ≤ (sample actual).probOf {observed | record ∈ observed})
    {Observation : Type} (observe : (application setup leaks).ProtocolState → Observation)
    (observationInvariant : ∀ state,
      observe (((runtime setup).reactiveNormalization leaks).state state) = observe state)
    (source : ((rosterMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((rosterMenu setup leaks bounds rosters).decisionInformationAntichain (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network))
      (fun who site => source.continuationContext site (fun final => base final.state who)
        (2 * (rosterPlan setup rosters).length + 1))) :
    let deposit := rosterAuditDeposit setup leaks bounds rosters network base probability
    let audit := (application setup leaks).sampledTrafficAudit (envelopeEvidence setup leaks)
      (fun evidence => evidence.2.2.sender) (permittedRosterEnvelope setup leaks) sample
    let utility := TerminalAudit.utility base (application setup leaks).stateTraffic audit deposit
    let settle := TerminalAudit.settlement base (application setup leaks).stateTraffic audit deposit
    ∃ target : ((bounds.rawMenu (runtime setup) leaks).information (initialLaw setup)
        (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu (runtime setup) leaks).decisionInformationAntichain (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network))
        (fun who site => target.continuationContext site (fun final => utility final.state who)
          (2 * (rosterPlan setup rosters).length + 1)) ∧
      (((bounds.rawMenu (runtime setup) leaks).information (initialLaw setup)
        (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).runBehavioral
          target.strategy (2 * (rosterPlan setup rosters).length + 1)).bind (fun final =>
            (settle final.state).map (fun payoffs => (observe final.state, payoffs))) =
        (((rosterMenu setup leaks bounds rosters).information (initialLaw setup)
          (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).runBehavioral source.strategy
            (2 * (rosterPlan setup rosters).length + 1)).map
              (fun final => (observe final.state, base final.state)) := by
  intro deposit audit utility settle
  let effective := bounds.menu (runtime setup) leaks
  let retained := rosterMenu setup leaks bounds rosters
  let initial := initialLaw setup
  let count := (rosterPlan setup rosters).length
  let scheduler := rosterScheduler setup leaks rosters network
  let included := rosterMenu_in_effective setup leaks bounds rosters
  let payoff := fun who (history : (effective.protocol initial count scheduler).History) =>
    base history.state who
  let lower := fun who => FinitePayoffBounds.lower (payoff who)
  let upper := fun who => FinitePayoffBounds.upper (payoff who)
  choose depth clock using roster_menu_common_depth setup leaks rosters network effective
  have nonnegative (who : Player) : 0 ≤ deposit who :=
    div_nonneg (sub_nonneg.mpr (FinitePayoffBounds.lower_le_upper (payoff who))) (positive who).le
  have sufficient (who : Player) : upper who - probability who * deposit who ≤ lower who := by
    change upper who - probability who * ((upper who - lower who) / probability who) ≤ lower who
    rw [mul_div_cancel₀ _ (positive who).ne']
    linarith
  exact bounds.audited_raw_sequential_equilibrium (runtime setup) leaks initial count scheduler
    retained included depth clock (envelopeEvidence setup leaks)
    (fun evidence => evidence.2.2.sender)
    (permittedRosterEnvelope setup leaks) sample authentic
    (roster_history_traffic setup leaks bounds rosters network reveals openable)
    (roster_extra_choice_traffic setup leaks bounds rosters network reveals openable)
    base baseInvariant lower upper probability deposit nonnegative
    (fun history who => FinitePayoffBounds.lower_le (payoff who)
      ((included.actionRestriction initial count scheduler).history history))
    (fun history who => FinitePayoffBounds.le_upper (payoff who) history) sufficient coverage
    observe observationInvariant source equilibrium

end Vegas
