/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveLocalContinuation

/-! # Physical continuations of an admissible finite response restriction

A local alternative is a finite-menu law, followed by the original physical
policy. Coverage is needed at actual legal histories only. The representation's
fallback at inconsistent private inputs is irrelevant to these laws.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

theorem run_restrict_eq_finish (players : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (enough : app.rank horizon history.state ≤ fuel) :
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (fun who => menu.restrictPolicy initial horizon scheduler who (players who))
      fuel history).map History.state =
      app.finish initial horizon scheduler players history.state := by
  rw [menu.run_restrict_control_steps initial horizon scheduler players covered]
  exact app.iterate_eq_finish initial horizon scheduler players fuel history.state enough

open Classical in
/-- A local lottery followed by an admissible physical baseline evaluates as
one actual response and the remaining physical execution. The statement holds
at every legal decision history, whether or not the baseline reaches it. -/
theorem run_local_law_restrict_finish (players : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Principal) (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (law : PMF ((menu.information initial horizon scheduler).Choice who
      ((menu.information initial horizon scheduler).infoOf who history.trace)))
    (fuel : Nat) (enough : app.rank horizon history.state ≤ fuel + 1) :
    let baseline := fun player => menu.restrictPolicy initial horizon scheduler player
      (players player)
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (Profile.update (sig := (menu.information initial horizon scheduler).behavioralSignature)
        baseline who ((baseline who).withLaw
          ((menu.information initial horizon scheduler).infoOf who history.trace) law))
      (fuel + 1) history).map History.state =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        app.finish initial horizon scheduler players
          (some ⟨remaining, none, execution.respond app who response⟩) := by
  intro baseline
  let model := menu.information initial horizon scheduler
  let alternative := (baseline who).withLaw (model.infoOf who history.trace) law
  let updated := Profile.update (sig := model.behavioralSignature) baseline who alternative
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
      PMF.map_comp]
    rw [← observed]
    simp only [alternative, InformationModel.BehavioralPolicy.withLaw_self]
    rfl
  have firstLaw := menu.run_one_response initial horizon scheduler updated history who
    remaining execution current
  rw [decoded, PMF.map_comp] at firstLaw
  have split := model.one_step_then_baseline_eq_local_law
    (menu.decisionRecall initial horizon scheduler).decisionInformationAntichain
    baseline who alternative history active fuel
  simp only [alternative, InformationModel.BehavioralPolicy.withLaw_self] at split
  rw [← split, PMF.map_bind]
  calc
    _ = (model.runBehavioralFrom updated 1 history).bind (fun next =>
        app.finish initial horizon scheduler players next.state) := by
      apply bind_congr_on_support _
      intro next supported
      apply menu.run_restrict_eq_finish initial horizon scheduler players covered
      have stateMember : next.state ∈
          ((model.runBehavioralFrom updated 1 history).map History.state).support := by
        rw [PMF.support_map]
        exact ⟨next, supported, rfl⟩
      rw [firstLaw] at stateMember
      obtain ⟨choice, _, stateEq⟩ := PMF.support_map .. ▸ stateMember
      rw [← stateEq]
      rw [current] at enough
      change 2 * remaining + 1 ≤ fuel + 1 at enough
      change 2 * remaining ≤ fuel
      omega
    _ = ((model.runBehavioralFrom updated 1 history).map History.state).bind
        (app.finish initial horizon scheduler players) := by rw [PMF.bind_map]
    _ = _ := by
      rw [firstLaw, PMF.bind_map, PMF.bind_map]
      rfl

open Classical in
/-- Remaining-depth assessment fuel suffices for the physical local-law
evaluation; no additional control-depth assumption is required. -/
theorem run_local_law_restrict_remaining (players : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Principal) (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (law : PMF ((menu.information initial horizon scheduler).Choice who
      ((menu.information initial horizon scheduler).infoOf who history.trace))) :
    let baseline := fun player => menu.restrictPolicy initial horizon scheduler player
      (players player)
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (Profile.update (sig := (menu.information initial horizon scheduler).behavioralSignature)
        baseline who ((baseline who).withLaw
          ((menu.information initial horizon scheduler).infoOf who history.trace) law))
      (2 * horizon + 1 - history.trace.length) history).map History.state =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        app.finish initial horizon scheduler players
          (some ⟨remaining, none, execution.respond app who response⟩) := by
  intro baseline
  have bounded := app.trace_bound initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)
  rw [menu.toRawTrace_length] at bounded
  have positive : 0 < app.rank horizon history.state := by
    rw [current]
    change 0 < 2 * remaining + 1
    omega
  have enough : app.rank horizon history.state ≤
      (2 * horizon + 1 - history.trace.length - 1) + 1 := by omega
  have result := menu.run_local_law_restrict_finish initial horizon scheduler players covered
    history who remaining execution current law (2 * horizon + 1 - history.trace.length - 1) enough
  have fuelEq : (2 * horizon + 1 - history.trace.length - 1) + 1 =
      2 * horizon + 1 - history.trace.length := by omega
  rw [fuelEq] at result
  exact result

end Interaction.ReactiveApplication.ResponseMenu
