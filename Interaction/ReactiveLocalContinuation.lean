/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseEvaluation
import Interaction.ReactiveOwnPlay
import GameTheoryExtensions.Analysis.Protocol.OneShotDeviation

/-! # A local behavioral deviation followed by the native continuation

Replacing one information site's law performs one physical response and then
uses the original profile's remaining execution. Existing native decision recall
ensures that the replaced site cannot be visited again. The equalities concern
the actual protocol and response menus, including arbitrary off-path histories.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- State projection also holds for prefixes shorter than the remaining horizon. -/
theorem run_map_controlSteps
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
        History.state =
      (fun law => law.bind (app.controlStep initial horizon scheduler
        (menu.decodeProfile initial horizon scheduler profile)))^[fuel]
          (FinDist.pure history.state) := by
  let players := menu.decodeProfile initial horizon scheduler profile
  have encoded : (fun who => app.encodePolicy (players who)) =
      fun who => menu.embedPolicy initial horizon scheduler who (profile who) := by
    funext who
    exact app.encode_decodePolicy _
  calc
    _ = (((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
        (menu.toRawHistory initial horizon scheduler)).map History.state := by
      rw [FinDist.map_comp]
      rfl
    _ = _ := by
      rw [menu.run_embed,
        ← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
          (app.information initial horizon scheduler) (app.singleMover initial horizon scheduler),
        ← encoded, app.run_map_state]
      rfl

theorem run_one_response
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Principal) (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile 1 history).map
        History.state =
      (menu.decodeProfile initial horizon scheduler profile who
        (execution.recall who) (execution.observe app who)).map fun response =>
          some ⟨remaining, none, execution.respond app who response⟩ := by
  rw [menu.run_map_controlSteps]
  simp only [Function.iterate_one, FinDist.pure_bind, current, controlStep,
    actor, Option.bind_some, transition, ↓reduceIte, Option.getD_some]
  exact (FinDist.map_eq_bind _ _).symm

/-- A lawful response in the local behavioral law has an actual next history. -/
theorem response_history_exists
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Principal) (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : app.Action)
    (supported : response ∈ (menu.decodeProfile initial horizon scheduler profile who
      (execution.recall who) (execution.observe app who)).support) :
    ∃ next ∈ ((menu.information initial horizon scheduler).runBehavioralFrom profile 1
      history).support, next.state =
        some ⟨remaining, none, execution.respond app who response⟩ := by
  have stateMember : some (Control.mk remaining none (execution.respond app who response)) ∈
      ((menu.decodeProfile initial horizon scheduler profile who
        (execution.recall who) (execution.observe app who)).map fun action =>
          some (Control.mk remaining none (execution.respond app who action))).support := by
    rw [FinDist.support_map]
    exact ⟨response, supported, rfl⟩
  rw [← menu.run_one_response initial horizon scheduler profile history who remaining
    execution current] at stateMember
  obtain ⟨next, reached, stateEq⟩ := FinDist.support_map .. ▸ stateMember
  exact ⟨next, reached, stateEq⟩

open Classical in
theorem run_local_law_finish
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Principal) (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (law : FinDist ((menu.information initial horizon scheduler).Choice who
      ((menu.information initial horizon scheduler).infoOf who history.trace)))
    (fuel : Nat) (enough : app.rank horizon history.state ≤ fuel + 1) :
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (Profile.update (sig := (menu.information initial horizon scheduler).behavioralSignature)
        profile who ((profile who).withLaw
          ((menu.information initial horizon scheduler).infoOf who history.trace) law))
      (fuel + 1) history).map History.state =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        app.finish initial horizon scheduler (menu.decodeProfile initial horizon scheduler profile)
          (some ⟨remaining, none, execution.respond app who response⟩) := by
  classical
  let model := menu.information initial horizon scheduler
  let alternative := (profile who).withLaw (model.infoOf who history.trace) law
  let updated := Profile.update (sig := model.behavioralSignature) profile who alternative
  have active : (menu.protocol initial horizon scheduler).active history.state who := by
    change app.actor history.state = some who
    rw [current]
    rfl
  have observed : model.infoOf who history.trace =
      some (execution.recall who, execution.observe app who) := by
    change (menu.signals initial horizon scheduler).infoOf who history.trace = _
    rw [menu.info, current]
    simp [observe]
  have decoded : menu.decodeProfile initial horizon scheduler updated who
      (execution.recall who) (execution.observe app who) =
        law.map (fun choice => choice.1.getD ⟨none⟩) := by
    simp only [decodeProfile, decodePolicy, embedPolicy, updated, Profile.update_same,
      FinDist.map_comp]
    rw [← observed]
    simp only [alternative, InformationModel.BehavioralPolicy.withLaw_self]
    rfl
  have firstLaw := menu.run_one_response initial horizon scheduler updated history who
    remaining execution current
  rw [decoded, FinDist.map_comp] at firstLaw
  have split := model.one_step_then_baseline_eq_local_law
    (menu.decisionRecall initial horizon scheduler).antichain
    profile who alternative history active fuel
  simp only [alternative, InformationModel.BehavioralPolicy.withLaw_self] at split
  rw [← split, FinDist.map_bind]
  calc
    _ = (model.runBehavioralFrom updated 1 history).bind (fun next =>
        app.finish initial horizon scheduler (menu.decodeProfile initial horizon scheduler profile)
          next.state) := by
      apply FinDist.bind_congr
      intro next supported
      apply menu.run_eq_finish
      have stateMember : next.state ∈
          ((model.runBehavioralFrom updated 1 history).map History.state).support := by
        rw [FinDist.support_map]
        exact ⟨next, supported, rfl⟩
      rw [firstLaw] at stateMember
      obtain ⟨choice, _, stateEq⟩ := FinDist.support_map .. ▸ stateMember
      rw [← stateEq]
      rw [current] at enough
      change 2 * remaining + 1 ≤ fuel + 1 at enough
      change 2 * remaining ≤ fuel
      omega
    _ = ((model.runBehavioralFrom updated 1 history).map History.state).bind
        (app.finish initial horizon scheduler
          (menu.decodeProfile initial horizon scheduler profile)) := by rw [FinDist.bind_map]
    _ = _ := by
      rw [firstLaw, FinDist.bind_map, FinDist.bind_map]
      rfl

open Classical in
/-- The standard remaining-depth continuation fuel is sufficient at every
actual menu decision history; callers need no separate scheduling estimate. -/
theorem run_local_law_remaining
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Principal) (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (law : FinDist ((menu.information initial horizon scheduler).Choice who
      ((menu.information initial horizon scheduler).infoOf who history.trace))) :
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (Profile.update (sig := (menu.information initial horizon scheduler).behavioralSignature)
        profile who ((profile who).withLaw
          ((menu.information initial horizon scheduler).infoOf who history.trace) law))
      (2 * horizon + 1 - history.trace.length) history).map History.state =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        app.finish initial horizon scheduler (menu.decodeProfile initial horizon scheduler profile)
          (some ⟨remaining, none, execution.respond app who response⟩) := by
  have bounded := app.trace_bound initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)
  rw [menu.toRawTrace_length] at bounded
  have positive : 0 < app.rank horizon history.state := by
    rw [current]
    change 0 < 2 * remaining + 1
    omega
  have enough : app.rank horizon history.state ≤
      (2 * horizon + 1 - history.trace.length - 1) + 1 := by omega
  have result := menu.run_local_law_finish initial horizon scheduler profile history who
    remaining execution current law (2 * horizon + 1 - history.trace.length - 1) enough
  have fuelEq : (2 * horizon + 1 - history.trace.length - 1) + 1 =
      2 * horizon + 1 - history.trace.length := by omega
  rw [fuelEq] at result
  exact result

end Interaction.ReactiveApplication.ResponseMenu
