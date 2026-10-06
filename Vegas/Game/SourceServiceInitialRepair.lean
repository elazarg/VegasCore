/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceContinuationComparison

/-! # Settlement dominance of a whole-policy deviation from the initial history

The fixed retained repair of an arbitrary effective deviation, started with
empty private memory, has at least the deviation's audited expected payoff
under the audited effective game, from the initial history. The coupling runs
the existing stopped repair through every source event from each initial
execution; the comparison is the range-sized deposit's settlement bound. This
is the initial-history counterpart of
`Vegas.sourceService_continuation_settlement_comparison`, where the deviator
is not active.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Math.Probability GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- From one supported initial execution, the deviation's rounds and the
repair's joint run are coupled through every source event, retaining the
repair's private memory and the stopped-repair invariant. -/
theorem initial_events_stopped_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (source : ∀ who, ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who)
    (target : ∀ who, ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who)
    (agrees : ((sourceServiceMenu_in_effective setup leaks bounds rosters).actionRestriction
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).ExtendsProfile source target)
    (owner : Player)
    (alternative : ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy owner)
    (state : EventGraphRuntime.State (graph setup))
    (supported : state ∈ (initialLaw setup).support) :
    let app := application setup leaks
    let effective := bounds.menu (runtime setup) leaks
    let horizon := (rosterPlan setup rosters).length
    let scheduler := rosterScheduler setup leaks rosters network
    let policy := app.decodePolicy (effective.embedPolicy (initialLaw setup) horizon scheduler
      owner alternative)
    let players := Function.update (effective.decodeProfile (initialLaw setup) horizon scheduler
      target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner [] policy
    let initial := ReactiveApplication.Execution.initial app state
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.runRounds scheduler players horizon initial ∧
      coupling.map Prod.snd = strategy.runJoint owner players scheduler horizon initial
        (BindingMemory.atRecall (runtime setup) leaks []) ∧
      ∀ next ∈ coupling.support,
        Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
          horizon scheduler).Trace (some ⟨0, none, next.2.1⟩)) ∧
        next.2.2.shadow.OwnBindings owner ∧
        ((∃ record ∈ app.executionTraffic next.1, record.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
          next.1.application.publicView.missedBindingBy owner = true ∨
          BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1) := by
  intro app effective horizon scheduler policy players strategy initial
  obtain ⟨trace⟩ := (sourceServiceMenu setup leaks bounds rosters).trace_initial (initialLaw setup)
    horizon scheduler state supported
  have binding : initial.application.BindingInvariant := by
    obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact State.initial_bindingInvariant _
  have split : rosterPlan setup rosters = [] ++
      (List.finRange (graph setup).order.eventCount).flatMap (rosterBlock setup rosters) ++ [] := by
    simp only [List.nil_append, List.append_nil]
    rfl
  obtain ⟨coupling, first, second, related⟩ := remaining_events_stopped_coupling setup leaks bounds
    values capacity rosters opportunities network source target agrees owner policy
    (fun past view response chosen => effective.decode_embedPolicy_covered (initialLaw setup)
      horizon scheduler owner alternative past view response chosen)
    [] (BindingMemory.atRecall (runtime setup) leaks []) initial initial
    (BindingMemory.frame_atRecall (runtime setup) leaks owner initial)
    (BindingShadow.ownBindings_empty owner) (Nat.zero_le _) (app.initial_inputRecall state)
    (((runtime setup).packetEvidence leaks).sound_initial state) binding
    (List.finRange (graph setup).order.eventCount) 0 (by rw [Nat.zero_add]; exact trace)
    [] [] split 0 List.drop_zero.symm
    (by simp only [rosterPlanPrefix, List.take_zero, List.flatMap_nil]) rfl
  refine ⟨coupling, ?_, ?_, related⟩
  · refine first.trans ?_
    exact (roster_segment_rounds setup leaks rosters network players []
      (List.finRange (graph setup).order.eventCount |>.flatMap (rosterBlock setup rosters)) []
      split initial rfl).symm
  · simp only [Function.update_self] at second
    exact second

/-- **Initial settlement dominance.** For extending source and effective
profiles and an arbitrary effective whole-policy deviation, the fixed retained
repair of the deviation, started with empty private memory, has at least the
deviation's audited expected payoff. The deposit uses the range of all
effective histories and is fixed before profiles and deviations. -/
theorem sourceService_initial_settlement_comparison {Parameter : Type}
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    [leaks.FiniteSupport]
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
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
    (alternative : ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who) :
    let app := application setup leaks
    let menu := sourceServiceMenu setup leaks bounds rosters
    let effective := bounds.menu (runtime setup) leaks
    let count := (rosterPlan setup rosters).length
    let scheduler := rosterScheduler setup leaks rosters network
    let base := baseUtility setup leaks
      (fun state => utility (setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit setup leaks bounds rosters network base
      (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    let repair := BindingMemory.retainedPolicy (runtime setup) leaks menu (initialLaw setup)
      count scheduler who [] (app.decodePolicy (effective.embedPolicy (initialLaw setup) count
        scheduler who alternative))
    expect ((effective.information (initialLaw setup) count scheduler).runBehavioral
        (Function.update target who alternative) (2 * count + 1))
        (fun final => payoff final.state who) ≤
      expect ((menu.information (initialLaw setup) count scheduler).runBehavioral
        (Function.update source who repair) (2 * count + 1))
        (fun final => base final.state who) := by
  classical
  intro app menu effective count scheduler base deposit payoff repair
  let policy := app.decodePolicy (effective.embedPolicy (initialLaw setup) count scheduler
    who alternative)
  let players := Function.update (effective.decodeProfile (initialLaw setup) count scheduler
    target) who policy
  have pick (state : EventGraphRuntime.State (graph setup))
      (supported : state ∈ (initialLaw setup).support) :=
    initial_events_stopped_coupling setup leaks bounds values capacity rosters opportunities
      network source target agrees who alternative state supported
  let coupling := fun state supported => (pick state supported).choose
  let coupled : PMF (app.Control × app.Control × BindingMemory (runtime setup) leaks) :=
    (initialLaw setup).bindOnSupport fun state supported =>
      (coupling state supported).map fun next =>
        ((⟨0, none, next.1⟩ : app.Control), (⟨0, none, next.2.1⟩ : app.Control), next.2.2)
  have left : coupled.map (fun pair => some pair.1) =
      ((effective.information (initialLaw setup) count scheduler).runBehavioral
        (Function.update target who alternative) (2 * count + 1)).map History.state := by
    have decoded : effective.decodeProfile (initialLaw setup) count scheduler
        (Function.update target who alternative) = players :=
      effective.decodeProfile_update (initialLaw setup) count scheduler target who alternative
    have run := effective.run_eq_finish (initialLaw setup) count scheduler
      (Function.update target who alternative) (2 * count + 1)
      (effective.protocol (initialLaw setup) count scheduler).initHistory le_rfl
    refine Eq.trans ?_ run.symm
    rw [decoded]
    change _ = (initialLaw setup).bind fun state =>
      (app.runRounds scheduler players count
        (ReactiveApplication.Execution.initial app state)).map app.finished
    rw [map_bindOnSupport]
    apply bindOnSupport_eq_bind_of_eq_on_support
    intro state supported
    rw [PMF.map_comp, ← (pick state supported).choose_spec.1, PMF.map_comp]
    rfl
  have right : coupled.map (fun pair => some pair.2.1) =
      ((menu.information (initialLaw setup) count scheduler).runBehavioral
        (Function.update source who repair) (2 * count + 1)).map History.state := by
    rw [BindingMemory.retainedPolicy_initialLaw (runtime setup) leaks menu effective
      (sourceServiceMenu_in_effective setup leaks bounds rosters) (initialLaw setup) count
      scheduler source target agrees who policy (2 * count + 1) le_rfl, map_bindOnSupport]
    apply bindOnSupport_eq_bind_of_eq_on_support
    intro state supported
    rw [PMF.map_comp, ← (pick state supported).choose_spec.2.1, PMF.map_comp]
    rfl
  have coupledSupport (pair) (member : pair ∈ coupled.support) :
      ∃ state supported, ∃ next ∈ (coupling state supported).support,
        pair = ((⟨0, none, next.1⟩ : app.Control), (⟨0, none, next.2.1⟩ : app.Control),
          next.2.2) := by
    obtain ⟨state, supported, inner⟩ := Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ member)
    obtain ⟨next, nextMember, rfl⟩ := PMF.support_map .. ▸ inner
    exact ⟨state, supported, next, nextMember, rfl⟩
  have reachedLeft (pair) (member : pair ∈ coupled.support) :
      ∃ final ∈ ((effective.information (initialLaw setup) count scheduler).runBehavioral
        (Function.update target who alternative) (2 * count + 1)).support,
          final.state = some pair.1 := by
    have reached : some pair.1 ∈
        (((effective.information (initialLaw setup) count scheduler).runBehavioral
          (Function.update target who alternative) (2 * count + 1)).map History.state).support := by
      rw [← left, PMF.support_map]
      exact ⟨pair, member, rfl⟩
    rw [PMF.support_map] at reached
    exact reached
  have realized (pair) (member : pair ∈ coupled.support) :
      Nonempty ((effective.protocol (initialLaw setup) count scheduler).Trace (some pair.1)) := by
    obtain ⟨final, _, same⟩ := reachedLeft pair member
    exact ⟨same ▸ final.trace⟩
  have finished (pair) (member : pair ∈ coupled.support) :
      pair.1.execution.application.config.cut.Terminal := by
    obtain ⟨final, reached, same⟩ := reachedLeft pair member
    have stopped : app.terminal final.state := by
      rcases (effective.protocol (initialLaw setup) count
          scheduler).runRandomizedFor_terminal_or_length _ _ _ final reached with terminal | long
      · exact terminal
      · have finalBound := app.trace_bound (initialLaw setup) count scheduler
          (effective.toRawTrace (initialLaw setup) count scheduler final.trace)
        rw [effective.toRawTrace_length] at finalBound
        change 0 + (2 * count + 1) ≤ final.trace.length at long
        have empty : app.rank count final.state = 0 := by omega
        exact (app.rank_zero count final.state).mp empty
    rw [same] at stopped
    have finalTrace := effective.toRawTrace (initialLaw setup) count scheduler final.trace
    rw [same] at finalTrace
    exact rosterScheduler_completesPlay setup leaks rosters network pair.1 finalTrace stopped
  have related (pair) (member : pair ∈ coupled.support) :
      Nonempty ((menu.protocol (initialLaw setup) count scheduler).Trace (some pair.2.1)) ∧
      pair.2.2.shadow.OwnBindings who ∧
      ((∃ record ∈ app.executionTraffic pair.1.execution, record.envelope.sender = who ∧
        (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.envelope = false) ∨
        pair.1.execution.application.publicView.missedBindingBy who = true ∨
        BindingMemory.Frame (runtime setup) leaks pair.2.2 who pair.1.execution
          pair.2.1.execution) := by
    obtain ⟨state, supported, next, nextMember, same⟩ := coupledSupport pair member
    subst same
    exact (pick state supported).choose_spec.2.2 next nextMember
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
