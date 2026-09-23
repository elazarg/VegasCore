/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory
import GameTheory.Protocol.BehavioralAssessment

/-! # Reactive decision information supports assessment beliefs

An active observation contains the player's entire response recall. Each own
response strictly increases that record, and intervening service steps retain
it. A decision information fiber therefore never contains an ancestor and a
proper descendant. No finiteness or restriction on passive observations is used.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  [Inhabited app.Memory]

theorem control_of_active
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (history : (app.protocol initial horizon scheduler).History) (who : Principal)
    (active : (app.protocol initial horizon scheduler).active history.state who) :
    ∃ control, history.state = some control ∧ control.actor = some who := by
  cases stateEq : history.state with
  | none => simp [protocol, actor, stateEq] at active
  | some control =>
      exact ⟨control, rfl, by simpa [protocol, actor, stateEq] using active⟩

theorem informationSite_allNonterminal
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) (site : (app.information initial horizon scheduler).InformationSite who) :
    site.AllNonterminal := by
  intro history stopped
  obtain ⟨control, stateEq, active⟩ := app.control_of_active initial horizon scheduler
    history.1 who (InformationModel.InformationSite.active _ site history)
  change app.terminal history.1.state at stopped
  rw [stateEq] at stopped
  have impossible := active.symm.trans stopped.2
  cases impossible

theorem decisionInformationAntichain
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    (app.information initial horizon scheduler).DecisionInformationAntichain := by
  intro who site first second joint legal target realized fuel path
  obtain ⟨before, firstEq, firstActive⟩ := app.control_of_active initial horizon scheduler
    first.1 who (InformationModel.InformationSite.active _ site first)
  obtain ⟨after, lastEq, lastActive⟩ := app.control_of_active initial horizon scheduler
    second.1 who (InformationModel.InformationSite.active _ site second)
  have sameInfo := first.2.trans second.2.symm
  change (app.signals initial horizon scheduler).infoOf who first.1.trace =
    (app.signals initial horizon scheduler).infoOf who second.1.trace at sameInfo
  rw [app.info, app.info, firstEq, lastEq] at sameInfo
  simp only [observe, firstActive, lastActive, ↓reduceIte] at sameInfo
  have sameRecall := congrArg Prod.fst (Option.some.inj sameInfo)
  change before.execution.recall who = after.execution.recall who at sameRecall
  let action := (joint who).getD ⟨default, none⟩
  let middle : app.Control :=
    { before with
      actor := none
      execution := before.execution.respond app who action }
  have targetEq : target = some middle := by
    change target ∈ (app.transition initial horizon scheduler first.1.state joint).support
      at realized
    rw [firstEq] at realized
    simpa only [transition, firstActive, FinDist.mem_support_pure] using realized
  have retained := app.reaches_recall_prefix initial horizon scheduler path middle after
    targetEq lastEq who
  have grows := congrArg List.length (app.respond_actions before.execution who action)
  simp only [List.length_map, List.length_append, List.length_singleton] at grows
  have ordered := retained.length_le
  change ((before.execution.respond app who action).recall who).length ≤
    (after.execution.recall who).length at ordered
  rw [grows, sameRecall] at ordered
  omega

end Interaction.ReactiveApplication
