/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceEvaluatorRepair
import Vegas.Game.SourceServiceRepairSettlement
import Vegas.Game.ServiceRosterClock

/-! # Conditional settlement dominance by one retained continuation

The replacement policy depends on the deviator's information and original
continuation, and is shared by every hidden history in that information set.
The actual evaluator coupling supplies either preserved initial parameters and
public outcomes or incremental collectible evidence. The deposit uses the
range of all effective histories and is fixed before profiles or beliefs.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Math.Probability GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem sourceService_continuation_settlement_comparison {Parameter : Type}
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    [leaks.FiniteSupport]
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks) [network.FiniteSupport]
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (source : ∀ who, ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who)
    (target : ∀ who, ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who)
    (agrees : ((sourceServiceMenu_in_effective setup leaks bounds rosters).actionRestriction
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).ExtendsProfile source target)
    (who : Player)
    (site : ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).InformationSite who)
    (depth : Nat)
    (clock : InformationModel.InformationSite.CommonDepth
      ((sourceServiceMenu setup leaks bounds rosters).information
        (initialLaw setup) (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)) site depth)
    (alternative : ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who) :
    let menu := sourceServiceMenu setup leaks bounds rosters
    let effective := bounds.menu (runtime setup) leaks
    let count := (rosterPlan setup rosters).length
    let scheduler := rosterScheduler setup leaks rosters network
    let restriction := (sourceServiceMenu_in_effective setup leaks bounds rosters).actionRestriction
      (initialLaw setup) count scheduler
    let base := baseUtility setup leaks
      (fun state => utility (setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit setup leaks bounds rosters network base
      (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    ∃ repair : (menu.information (initialLaw setup) count scheduler).BehavioralPolicy who,
      ∀ belief : PMF
        ((menu.information (initialLaw setup) count scheduler).InformationHistory who site.1),
      expect belief (fun history =>
        expect ((effective.information (initialLaw setup) count scheduler).runBehavioralFrom
          (Function.update target who alternative) (2 * count + 1 - depth)
          (restriction.history history.1)) (fun final => payoff final.state who)) ≤
      expect belief (fun history =>
        expect ((menu.information (initialLaw setup) count scheduler).runBehavioralFrom
          (Function.update source who repair) (2 * count + 1 - depth)
          history.1) (fun final => base final.state who)) := by
  classical
  intro menu effective count scheduler restriction base deposit payoff
  let app := application setup leaks
  let reference := site.1.elim [] Prod.fst
  let policy := app.decodePolicy (effective.embedPolicy (initialLaw setup) count scheduler
    who alternative)
  let repair := BindingMemory.retainedPolicy (runtime setup) leaks menu (initialLaw setup)
    count scheduler who reference policy
  refine ⟨repair, fun belief => expect_mono (fun history _ => ?_) (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)⟩
  have active := InformationModel.InformationSite.active _ site history
  obtain ⟨control, current, acting⟩ := app.control_of_active (initialLaw setup) count scheduler
    (menu.toRawHistory (initialLaw setup) count scheduler history.1) who active
  have current' : history.1.state = some control := current
  have observation := (menu.info (initialLaw setup) count scheduler who history.1.trace).symm.trans
    history.2
  rw [current'] at observation
  change (if control.actor = some who then
    some (control.execution.recall who, control.execution.observe app who) else none) = site.1
      at observation
  rw [ite_eq_left acting] at observation
  have recalled : control.execution.recall who = reference := by
    simp only [reference, ← observation, Option.elim_some]
  have currentActive : history.1.state =
      some ⟨control.remaining, some who, control.execution⟩ := by
    rw [current']
    cases control
    cases acting
    rfl
  have bound := app.trace_bound (initialLaw setup) count scheduler
    (menu.toRawTrace (initialLaw setup) count scheduler history.1.trace)
  rw [menu.toRawTrace_length] at bound
  have rank : app.rank count history.1.state = 2 * control.remaining + 1 := by
    rw [currentActive]
    rfl
  rw [rank] at bound
  have sameDepth := clock history
  have enough : 2 * control.remaining + 1 ≤ 2 * count + 1 - depth := by
    change history.1.trace.length + (2 * control.remaining + 1) ≤ 2 * count + 1 at bound
    change history.1.trace.length = depth at sameDepth
    omega
  obtain ⟨coupled, left, right, related⟩ := active_evaluator_stopped_coupling setup leaks bounds
    values capacity rosters opportunities network source target agrees who reference
    alternative control.remaining (2 * count + 1 - depth) enough control.execution history.1
      currentActive recalled
  change coupled.map (fun pair => some pair.1) =
    ((effective.information (initialLaw setup) count scheduler).runBehavioralFrom
      (Function.update target who alternative) (2 * count + 1 - depth)
        (restriction.history history.1)).map History.state at left
  change coupled.map (fun pair => some pair.2.1) =
    ((menu.information (initialLaw setup) count scheduler).runBehavioralFrom
      (Function.update source who repair) (2 * count + 1 - depth) history.1).map History.state
        at right
  have realized (pair) (supported : pair ∈ coupled.support) :
      Nonempty ((effective.protocol (initialLaw setup) count scheduler).Trace (some pair.1)) := by
    have reached : some pair.1 ∈
        (((effective.information (initialLaw setup) count scheduler).runBehavioralFrom
          (Function.update target who alternative) (2 * count + 1 - depth)
          (restriction.history history.1)).map History.state).support := by
      rw [← left, PMF.support_map]
      exact ⟨pair, supported, rfl⟩
    obtain ⟨final, _, same⟩ := PMF.support_map .. ▸ reached
    exact ⟨same ▸ final.trace⟩
  have finished (pair) (supported : pair ∈ coupled.support) :
      pair.1.execution.application.config.cut.Terminal := by
    have reached : some pair.1 ∈
        (((effective.information (initialLaw setup) count scheduler).runBehavioralFrom
          (Function.update target who alternative) (2 * count + 1 - depth)
          (restriction.history history.1)).map History.state).support := by
      rw [← left, PMF.support_map]
      exact ⟨pair, supported, rfl⟩
    obtain ⟨final, member, same⟩ := PMF.support_map .. ▸ reached
    have stopped : app.terminal final.state := by
      rcases (effective.protocol (initialLaw setup) count
          scheduler).runRandomizedFor_terminal_or_length _ _ _ final member with terminal | long
      · exact terminal
      · have finalBound := app.trace_bound (initialLaw setup) count scheduler
          (effective.toRawTrace (initialLaw setup) count scheduler final.trace)
        rw [effective.toRawTrace_length] at finalBound
        have startLength := restriction.length history.1
        change history.1.trace.length = depth at sameDepth
        have empty : app.rank count final.state = 0 := by omega
        exact (app.rank_zero count final.state).mp empty
    rw [same] at stopped
    have finalTrace := effective.toRawTrace (initialLaw setup) count scheduler final.trace
    rw [same] at finalTrace
    exact rosterScheduler_completesPlay setup leaks rosters network pair.1 finalTrace stopped
  have compared := sourceService_repair_range_settlement_le setup leaks bounds values capacity
    rosters opportunities network parameter utility sample authentic who probability
    (positive who) (coverage who) coupled realized
    (fun pair member => (related pair member).1) finished
    (fun pair member => (related pair member).2.1)
    (fun pair member => (related pair member).2.2)
  rw [left, right] at compared
  dsimp only at compared
  have settledIntegrable (law : PMF app.ProtocolState) (finite : law.support.Finite)
      (settle : app.ProtocolState → PMF (Player → ℝ))
      (settleFinite : ∀ outcome, (settle outcome).support.Finite) :
      PayoffIntegrable (law.bind settle) (fun payoffs => payoffs who) :=
    payoffIntegrable_of_finite_support _ _
      (bind_support_finite finite fun outcome _ => settleFinite outcome)
  have settleFinite {Observation : Type} (observe : app.ProtocolState → Observation)
      (audit : Observation → PMF (Player → Bool)) (payoffs : app.ProtocolState → Player → ℝ)
      (charges : Player → ℝ) (outcome : app.ProtocolState) :
      (TerminalAudit.settlement payoffs observe audit charges outcome).support.Finite := by
    rw [TerminalAudit.settlement, PMF.support_map]
    exact (Set.toFinite _).image _
  rw [expect_bind_tower _ _ _ (settledIntegrable _
      (by rw [PMF.support_map]; exact (Set.toFinite _).image _) _ (settleFinite _ _ _ _)),
    expect_bind_tower _ _ _ (settledIntegrable _
      (by rw [PMF.support_map]; exact (Set.toFinite _).image _) _ (settleFinite _ _ _ _))]
    at compared
  simp only [expect_map, Function.comp_def, TerminalAudit.settlement_expect] at compared
  apply compared.trans_eq
  apply expect_congr_on_support
  intro final _
  have clear := sourceService_history_audit_clear setup leaks bounds values capacity rosters
    opportunities network sample authentic final who
  change base final.state who - _ * deposit who = base final.state who
  rw [clear, zero_mul, sub_zero]

end Vegas
