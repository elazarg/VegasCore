/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedReplay
import Interaction.ReactiveTrafficState

/-! # Actual query inputs before an event's first own packet

Every queried emitted prefix is contained in the eventual actual authored
input prefix. An unsent event therefore has an empty emitted prefix at every
previous local query, including negative exhaustion queries.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {LocalSeed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks LocalSeed owner event)

local notation "app" => runtime.reactiveApplication leaks

private theorem respond_inputs_prefix (execution : (app).Execution) (actor : Player)
    (action : (app).Action) :
    execution.network.inputs <+: (execution.respond app actor action).network.inputs := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact List.prefix_refl _
  | some material => exact List.prefix_append _ _

private theorem dispatch_inputs_prefix (players : Player → (app).Policy)
    (execution next : (app).Execution) (command : (app).Command)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    execution.network.inputs <+: next.network.inputs := by
  obtain ⟨middle, moved, responded⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have inputEq := (app).environmentStep_inputs execution middle command moved
  cases acting : command.actor? app with
  | none =>
      simp only [acting, ReactiveApplication.resume] at responded
      cases (PMF.mem_support_pure_iff _ _).mp responded
      simpa only [inputEq] using List.prefix_refl execution.network.inputs
  | some actor =>
      simp only [acting, ReactiveApplication.resume, ReactiveApplication.invoke] at responded
      obtain ⟨action, chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp responded
      rw [← inputEq]
      exact respond_inputs_prefix middle actor action

private theorem dispatch_emitted_subset (players : Player → (app).Policy)
    (execution next : (app).Execution) (command : (app).Command)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    (runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app)).emitted ⊆
      (runtime.environmentSeedInput leaks owner event (next.observeEnvironment app)).emitted := by
  intro message member
  have inputPrefix := dispatch_inputs_prefix players execution next command reached
  obtain ⟨own, addressed⟩ := List.mem_filter.mp member
  obtain ⟨submitted, authored⟩ := List.mem_filter.mp own
  exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨inputPrefix.subset submitted, authored⟩,
    addressed⟩

private theorem step_log_emissions
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (recorded : ∀ entry ∈ memory.log, entry.query.input.emitted ⊆
      (runtime.environmentSeedInput leaks owner event view).emitted) :
    ∀ entry ∈ (controller.step remainder memory past view).2.log,
      entry.query.input.emitted ⊆
        (runtime.environmentSeedInput leaks owner event view).emitted := by
  classical
  dsimp only [step]
  split_ifs
  · exact recorded
  · intro entry member
    rw [finishReply_log] at member
    rcases List.mem_append.mp member with member | member
    · exact recorded entry member
    · have same := List.mem_singleton.mp member
      subst entry
      exact List.Subset.refl _
  · exact recorded
  · exact recorded

/-- Every actual queried emission is retained in the final actual selected-event input prefix. -/
theorem runJoint_log_emissions
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (players : Player → (app).Policy) (count : Nat) (execution : (app).Execution)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (next : (app).Execution)
    (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution memory).support)
    (recorded : ∀ entry ∈ memory.log, entry.query.input.emitted ⊆
      (runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app)).emitted) :
    ∀ entry ∈ after.log, entry.query.input.emitted ⊆
      (runtime.environmentSeedInput leaks owner event (next.observeEnvironment app)).emitted := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact recorded
  | succ count ih =>
      rw [controller.runJoint_succ] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have prior := controller.step_log_emissions remainder memory execution.environmentRecall
        (execution.observeEnvironment app) recorded
      have appended := dispatch_emitted_subset (owner := owner) (event := event)
        players execution middle _ moved
      exact ih middle _ later (fun entry member message submitted =>
        appended (prior entry member submitted))

/-- An initialized actual run with no own selected-event packet has an empty
emission input at every earlier local query, with no scheduler-domain assumption. -/
theorem runJoint_unsent_queryInputs
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (players : Player → (app).Policy) (count : Nat) (state : State graph)
    (localSeed : LocalSeed) (remainderSeed : RestSeed)
    (next : (app).Execution) (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        (ReactiveApplication.Execution.initial app state)
          (initialMemory localSeed remainderSeed)).support)
    (unsent : (runtime.environmentSeedInput leaks owner event
      (next.observeEnvironment app)).emitted = []) :
    ∀ entry ∈ after.log, entry.query.input.emitted = [] := by
  have retained := controller.runJoint_log_emissions localLaw remainderLaw remainder players count
    (ReactiveApplication.Execution.initial app state) (initialMemory localSeed remainderSeed)
      next after reached (by simp [initialMemory])
  intro entry member
  have subset := retained entry member
  cases emittedEq : entry.query.input.emitted with
  | nil => rfl
  | cons head rest =>
      have impossible := subset (by rw [emittedEq]; exact List.mem_cons_self)
      rw [unsent] at impossible
      cases impossible

end Vegas.EventGraphRuntime.LocalSeedController
