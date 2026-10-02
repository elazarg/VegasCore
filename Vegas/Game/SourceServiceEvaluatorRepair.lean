/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceActiveRepair
import Vegas.Pending.ReactiveBindingRealization

/-! # Stopped repair of the actual behavioral continuation evaluators

The initial own recall fixes one legal behavioral repair for every hidden
history in an information set. Both marginals below are the existing game
evaluators; the coupling retains the private implementation memory needed to
compare initial parameters, public outcomes and incremental audit evidence.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem active_evaluator_stopped_coupling
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
    (owner : Player) (reference : List (application setup leaks).PlayerEntry)
    (alternative : ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy owner)
    (remaining fuel : Nat) (enough : 2 * remaining + 1 ≤ fuel)
    (execution : (application setup leaks).Execution)
    (history : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History)
    (current : history.state = some ⟨remaining, some owner, execution⟩)
    (recalled : execution.recall owner = reference) :
    let app := application setup leaks
    let menu := sourceServiceMenu setup leaks bounds rosters
    let effective := bounds.menu (runtime setup) leaks
    let horizon := (rosterPlan setup rosters).length
    let scheduler := rosterScheduler setup leaks rosters network
    let inclusion := sourceServiceMenu_in_effective setup leaks bounds rosters
    let policy := app.decodePolicy (effective.embedPolicy (initialLaw setup) horizon scheduler
      owner alternative)
    let repair := BindingMemory.retainedPolicy (runtime setup) leaks menu (initialLaw setup)
      horizon scheduler owner reference policy
    ∃ coupled : PMF (app.Control × app.Control × BindingMemory (runtime setup) leaks),
      coupled.map (fun pair => some pair.1) =
        ((effective.information (initialLaw setup) horizon scheduler).runBehavioralFrom
          (Function.update target owner alternative) fuel
            (inclusion.history (initialLaw setup) horizon scheduler history)).map History.state ∧
      coupled.map (fun pair => some pair.2.1) =
        ((menu.information (initialLaw setup) horizon scheduler).runBehavioralFrom
          (Function.update source owner repair) fuel history).map History.state ∧
      ∀ pair ∈ coupled.support,
        Nonempty ((menu.protocol (initialLaw setup) horizon scheduler).Trace (some pair.2.1)) ∧
        pair.2.2.shadow.OwnBindings owner ∧
        ((∃ record ∈ app.executionTraffic pair.1.execution,
          record.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
          pair.1.execution.application.publicView.missedBindingBy owner = true ∨
          BindingMemory.Frame (runtime setup) leaks pair.2.2 owner pair.1.execution
            pair.2.1.execution) := by
  intro app menu effective horizon scheduler inclusion policy repair
  have covered := effective.decode_embedPolicy_covered (initialLaw setup) horizon scheduler
    owner alternative
  obtain ⟨joint, left, right, related⟩ := active_history_stopped_coupling setup leaks bounds
    values capacity rosters opportunities network source target agrees owner policy
    covered remaining execution (current ▸ history.trace)
  let coupled := joint.map (fun next =>
    ((⟨0, none, next.1⟩ : app.Control), (⟨0, none, next.2.1⟩ : app.Control), next.2.2))
  refine ⟨coupled, ?_, ?_, ?_⟩
  · rw [effective.run_eq_finish (initialLaw setup) horizon scheduler _ fuel _ (by
      change app.rank horizon history.state ≤ fuel
      rw [current]
      exact enough)]
    have decoded : effective.decodeProfile (initialLaw setup) horizon scheduler
        (Function.update target owner alternative) =
          Function.update (effective.decodeProfile (initialLaw setup) horizon scheduler target)
            owner policy := effective.decodeProfile_update (initialLaw setup) horizon scheduler
              target owner alternative
    rw [decoded]
    change _ = app.finish (initialLaw setup) horizon scheduler
      (Function.update (effective.decodeProfile (initialLaw setup) horizon scheduler target)
        owner policy) history.state
    rw [current, ReactiveApplication.finish, ReactiveApplication.resume]
    dsimp only [coupled]
    rw [PMF.map_comp]
    have mapped := congrArg (fun law => law.map app.finished) left
    rw [PMF.map_comp] at mapped
    exact mapped
  · have law := BindingMemory.retainedPolicy_runFrom (runtime setup) leaks menu effective inclusion
      (initialLaw setup) horizon scheduler source target agrees owner reference policy remaining
      fuel enough execution history current recalled
    rw [law]
    dsimp only [coupled]
    rw [PMF.map_comp]
    have mapped := congrArg (fun law => law.map (fun next => app.finished next.1)) right
    simp only [Function.update_self, recalled, PMF.map_comp] at mapped
    exact mapped
  · intro pair supported
    obtain ⟨next, member, rfl⟩ := PMF.support_map .. ▸ supported
    exact related next member

end Vegas
