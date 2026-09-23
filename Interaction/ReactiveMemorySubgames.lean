/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMemory

/-! # Auxiliary private memory suppresses proper reactive subgames

When response memory has two distinct values, a proper canonical subgame
following any player's response can contain future decisions only by that
same player. A different player cannot distinguish a history that relabels
the earlier private memory. This holds for all schedulers and leak rules.

The theorem diagnoses the raw history representation. It is not an SPE
preservation theorem and does not change the action or observation semantics.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  [Inhabited app.Memory]

def mapMemoryHistory (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (owner : Principal) (change : app.Memory → app.Memory)
    (history : (app.protocol initial horizon scheduler).History) :
    (app.protocol initial horizon scheduler).History :=
  ⟨app.mapStateMemory owner change history.state,
    app.mapMemoryTrace initial horizon scheduler owner change history.trace⟩

theorem mapMemoryHistory_info_other (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (owner observer : Principal) (different : observer ≠ owner)
    (change : app.Memory → app.Memory)
    (history : (app.protocol initial horizon scheduler).History) :
    (app.information initial horizon scheduler).infoOf observer
      (app.mapMemoryHistory initial horizon scheduler owner change history).trace =
    (app.information initial horizon scheduler).infoOf observer history.trace := by
  change (app.signals initial horizon scheduler).infoOf observer _ =
    (app.signals initial horizon scheduler).infoOf observer _
  rw [app.info, app.info]
  exact app.observe_mapMemory_other owner observer different change history.state

/-- A future foreign decision has a twin outside the alleged subtree, differing
only in auxiliary memory of a player who has already responded. -/
theorem not_subgameRoot_of_memory_relabeling
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (root inside : (app.protocol initial horizon scheduler).History)
    (before : app.Control) (rootState : root.state = some before)
    (owner observer : Principal) (different : observer ≠ owner)
    (entry : app.PlayerEntry) (recalled : entry ∈ before.execution.recall owner)
    (change : app.Memory → app.Memory) (avoids : ∀ memory, change memory ≠ entry.action.memory)
    (reached : (app.protocol initial horizon scheduler).HistoryReaches root inside)
    (running : ¬ (app.protocol initial horizon scheduler).terminal inside.state)
    (active : (app.protocol initial horizon scheduler).active inside.state observer) :
    ¬ (app.information initial horizon scheduler).IsSubgameRoot root := by
  intro proper
  let twin := app.mapMemoryHistory initial horizon scheduler owner change inside
  have insideState : ∃ control, inside.state = some control := by
    cases stateEq : inside.state with
    | none => simp [protocol, actor, stateEq] at active
    | some control => exact ⟨control, rfl⟩
  obtain ⟨after, afterState⟩ := insideState
  have twinState : twin.state = some { after with
      execution := after.execution.mapMemory app owner change } := by
    simp only [twin, mapMemoryHistory, afterState, mapStateMemory, Option.map_some]
  have twinRunning : ¬ (app.protocol initial horizon scheduler).terminal twin.state := by
    rw [twinState]
    rw [afterState] at running
    exact running
  have twinActive : (app.protocol initial horizon scheduler).active twin.state observer := by
    rw [twinState]
    rw [afterState] at active
    exact active
  have same := app.mapMemoryHistory_info_other initial horizon scheduler owner observer
    different change inside
  obtain ⟨fuel, path⟩ := proper observer inside twin reached running active twinRunning
    twinActive same.symm
  have retained := app.reaches_recall_prefix initial horizon scheduler path before _
    rootState twinState owner
  have member : entry ∈ ((after.execution.recall owner).map
      (PlayerEntry.mapMemory app change)) := by
    have next := retained.subset recalled
    simpa only [Execution.mapMemory, ↓reduceIte] using next
  obtain ⟨original, _, equal⟩ := List.mem_map.mp member
  have memories := congrArg (fun entry : app.PlayerEntry => entry.action.memory) equal
  exact avoids original.action.memory memories

/-- Any nonempty foreign response recall supplies an excluded memory value. -/
theorem not_subgameRoot_of_foreign_recall [Nontrivial app.Memory]
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (root inside : (app.protocol initial horizon scheduler).History)
    (before : app.Control) (rootState : root.state = some before)
    (owner observer : Principal) (different : observer ≠ owner)
    (recalled : before.execution.recall owner ≠ [])
    (reached : (app.protocol initial horizon scheduler).HistoryReaches root inside)
    (running : ¬ (app.protocol initial horizon scheduler).terminal inside.state)
    (active : (app.protocol initial horizon scheduler).active inside.state observer) :
    ¬ (app.information initial horizon scheduler).IsSubgameRoot root := by
  obtain ⟨first, rest, prior⟩ := List.exists_cons_of_ne_nil recalled
  obtain ⟨other, unequal⟩ := exists_ne first.action.memory
  exact app.not_subgameRoot_of_memory_relabeling initial horizon scheduler root inside before
    rootState owner observer different first (by simp [prior]) (fun _ => other) (fun _ => unequal)
    reached running active

/-- After a response, any future decision inside a proper subgame must belong
to that response's author. Auxiliary memory alone enforces this restriction. -/
theorem subgameRoot_future_actor_eq [Nontrivial app.Memory]
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (root inside : (app.protocol initial horizon scheduler).History)
    (proper : (app.information initial horizon scheduler).IsSubgameRoot root)
    (before : app.Control) (rootState : root.state = some before)
    (owner observer : Principal) (recalled : before.execution.recall owner ≠ [])
    (reached : (app.protocol initial horizon scheduler).HistoryReaches root inside)
    (running : ¬ (app.protocol initial horizon scheduler).terminal inside.state)
    (active : (app.protocol initial horizon scheduler).active inside.state observer) :
    observer = owner := by
  by_contra different
  exact app.not_subgameRoot_of_foreign_recall initial horizon scheduler root inside before
    rootState owner observer different recalled reached running active proper

/-- Once two distinct players have responded, a proper subgame cannot contain
any further player decision. Remaining chance or service steps are allowed. -/
theorem subgameRoot_no_future_decision_of_two_responders [Nontrivial app.Memory]
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (root inside : (app.protocol initial horizon scheduler).History)
    (proper : (app.information initial horizon scheduler).IsSubgameRoot root)
    (before : app.Control) (rootState : root.state = some before)
    (first second : Principal) (different : first ≠ second)
    (firstRecall : before.execution.recall first ≠ [])
    (secondRecall : before.execution.recall second ≠ [])
    (reached : (app.protocol initial horizon scheduler).HistoryReaches root inside)
    (running : ¬ (app.protocol initial horizon scheduler).terminal inside.state)
    (observer : Principal) :
    ¬ (app.protocol initial horizon scheduler).active inside.state observer := by
  intro active
  have one := app.subgameRoot_future_actor_eq initial horizon scheduler root inside proper
    before rootState first observer firstRecall reached running active
  have two := app.subgameRoot_future_actor_eq initial horizon scheduler root inside proper
    before rootState second observer secondRecall reached running active
  exact different (one.symm.trans two)

end Interaction.ReactiveApplication
