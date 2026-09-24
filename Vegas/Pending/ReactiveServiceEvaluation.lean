/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds
import Vegas.Pending.ReactiveService

/-! # The reserved service evaluates the canonical reactive game

The scheduler cursor is recovered from its actual command recall. Executing
one instruction advances that recall exactly once, including network-selected
activations. The complete epoch evaluator below is connected to canonical
behavioral play, with arbitrary player and network policies.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def interactionStep (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (instruction : ServiceInstruction graph)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    FinDist (runtime.reactiveApplication leaks).Execution :=
  (runtime.interactionInstruction leaks network execution.environmentRecall
    (execution.observeEnvironment (runtime.reactiveApplication leaks)) instruction).bind
      (fun command => (runtime.reactiveApplication leaks).dispatch players command execution)

def runInteractionPlan (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) :
    List (ServiceInstruction graph) → (runtime.reactiveApplication leaks).Execution →
      FinDist (runtime.reactiveApplication leaks).Execution
  | [], execution => FinDist.pure execution
  | instruction :: rest, execution => (runtime.interactionStep leaks players network instruction
      execution).bind (runInteractionPlan runtime leaks players network rest)

def runInteractionEpochs (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (chosen : ServiceOrder graph)
    (networkTurns : Nat) (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) :
    Nat → (runtime.reactiveApplication leaks).Execution → FinDist
      (runtime.reactiveApplication leaks).Execution
  | 0, execution => FinDist.pure execution
  | count + 1, execution =>
      (runtime.runInteractionPlan leaks players network (interactionEpoch chosen networkTurns)
        execution).bind
          (runInteractionEpochs runtime leaks chosen networkTurns players network count)

theorem interactionStep_recall (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (instruction : ServiceInstruction graph)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ (runtime.interactionStep leaks players network instruction
      execution).support) :
    next.environmentRecall.length = execution.environmentRecall.length + 1 := by
  obtain ⟨command, _, supported⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  rw [(runtime.reactiveApplication leaks).dispatch_environmentRecall
    players command execution next supported]
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem runInteractionPlan_recall (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (plan : List (ServiceInstruction graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ (runtime.runInteractionPlan leaks players network plan execution).support) :
    next.environmentRecall.length = execution.environmentRecall.length + plan.length := by
  induction plan generalizing execution with
  | nil => cases FinDist.mem_support_pure.mp reached; simp
  | cons instruction rest ih =>
      obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      rw [ih middle moved, runtime.interactionStep_recall leaks players network instruction
        execution middle supported, List.length_cons]
      omega

theorem runInteractionPlan_append (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (first second : List (ServiceInstruction graph))
    (execution : (runtime.reactiveApplication leaks).Execution) :
    runtime.runInteractionPlan leaks players network (first ++ second) execution =
      (runtime.runInteractionPlan leaks players network first execution).bind
        (runtime.runInteractionPlan leaks players network second) := by
  induction first generalizing execution with
  | nil => simp only [List.nil_append, runInteractionPlan, FinDist.pure_bind]
  | cons instruction rest ih =>
      simp only [List.cons_append, runInteractionPlan, FinDist.bind_bind]
      exact FinDist.bind_congr fun next _ => ih next

theorem interactionSuffix_rounds (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (chosen : ServiceOrder graph)
    (networkTurns : Nat) (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (before rest : List (ServiceInstruction graph))
    (split : interactionEpoch chosen networkTurns = before ++ rest)
    (epoch : Nat) (execution : (runtime.reactiveApplication leaks).Execution)
    (position : execution.environmentRecall.length =
      epoch * (interactionEpoch chosen networkTurns).length + before.length) :
    (runtime.reactiveApplication leaks).runRounds (runtime.interactionScheduler leaks
      chosen networkTurns network)
      players rest.length execution =
        runtime.runInteractionPlan leaks players network rest execution := by
  induction rest generalizing before execution with
  | nil => rfl
  | cons instruction rest ih =>
      have inside : before.length < (interactionEpoch chosen networkTurns).length := by
        rw [split, List.length_append, List.length_cons]
        omega
      have cursor : execution.environmentRecall.length %
          (interactionEpoch chosen networkTurns).length = before.length := by
        simp only [position, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt inside]
      have selected :
          (interactionEpoch chosen networkTurns)[before.length]? = some instruction := by
        rw [split, List.getElem?_append_right (by omega), Nat.sub_self]
        rfl
      have step : (runtime.reactiveApplication leaks).round
          (runtime.interactionScheduler leaks chosen networkTurns network) players execution =
            runtime.interactionStep leaks players network instruction execution := by
        simp only [ReactiveApplication.round, interactionScheduler, cursor, selected,
          interactionStep]
      rw [List.length_cons, ReactiveApplication.runRounds, step, runInteractionPlan]
      apply FinDist.bind_congr
      intro next supported
      apply ih (before ++ [instruction])
      · simpa only [List.append_assoc, List.singleton_append] using split
      · have advanced := runtime.interactionStep_recall leaks players network instruction
          execution next supported
        simp only [List.length_append, List.length_singleton]
        omega

theorem interactionEpochs_rounds (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (chosen : ServiceOrder graph)
    (networkTurns : Nat) (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (count epoch : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (position : execution.environmentRecall.length =
      epoch * (interactionEpoch chosen networkTurns).length) :
    (runtime.reactiveApplication leaks).runRounds (runtime.interactionScheduler leaks
      chosen networkTurns network)
      players (count * (interactionEpoch chosen networkTurns).length) execution =
        runtime.runInteractionEpochs leaks chosen networkTurns players network count
          execution := by
  induction count generalizing epoch execution with
  | zero => simp only [Nat.zero_mul, ReactiveApplication.runRounds, runInteractionEpochs]
  | succ count ih =>
      rw [Nat.succ_mul, Nat.add_comm, ReactiveApplication.runRounds_add]
      rw [runtime.interactionSuffix_rounds leaks chosen networkTurns players network [] _
        (List.nil_append _).symm epoch execution (by simpa using position)]
      change _ = (_ : FinDist (runtime.reactiveApplication leaks).Execution).bind _
      apply FinDist.bind_congr
      intro next supported
      apply ih (epoch + 1) next
      rw [runtime.runInteractionPlan_recall leaks players network _ execution next
        supported, position]
      simp only [Nat.add_mul, Nat.one_mul]

/-- Exact terminal-state law for the concrete reactive service. This theorem
quantifies over arbitrary deviations as well as prescribed player policies. -/
theorem canonical_interaction_service (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : FinDist (State graph)) (chosen : ServiceOrder graph) (networkTurns : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) :
    let scheduler := runtime.interactionScheduler leaks chosen networkTurns network
    let horizon := runtime.interactionHorizon chosen networkTurns
    (((runtime.reactiveApplication leaks).information
      initial horizon scheduler).runSingleMoverBehavioralFrom
      ((runtime.reactiveApplication leaks).singleMover initial horizon scheduler)
      (fun who => (runtime.reactiveApplication leaks).encodePolicy (players who)) (2 *
        horizon + 1)
      ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).initHistory).map
        ExecutionProtocol.History.state =
      initial.bind (fun state =>
        (runtime.runInteractionEpochs leaks chosen networkTurns players network
          runtime.serviceEpochs
          (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)).map
            (runtime.reactiveApplication leaks).finished) := by
  dsimp only
  rw [(runtime.reactiveApplication leaks).canonical_run_rounds]
  apply FinDist.bind_congr
  intro state _
  congr 1
  exact runtime.interactionEpochs_rounds leaks chosen networkTurns players network
    runtime.serviceEpochs 0 _ (by simp [ReactiveApplication.Execution.initial])

end Vegas.EventGraphRuntime
