module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.TurnClient
public import Interaction.ReactiveStoppedRecovery

@[expose] public section

/-! # On-path laws for recovered graph clients -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => (reactiveApplication timeouts) leaks

/-- From any initial state distribution, recovery preserves the complete native run law. -/
theorem clientPolicy_roundsFrom (initial : PMF (State graph)) (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat) (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile) (count : Nat) :
    (app).roundsFrom initial scheduler (clientPolicy timeouts leaks bound turns timing reference)
      count = (app).roundsFrom initial scheduler (turnPolicy timeouts leaks bound turns timing
        reference) count := by
  unfold ReactiveApplication.roundsFrom
  congr 1
  funext state
  have completed := ReactiveApplication.Policy.recoverWhere_runRounds
    (turnPolicy timeouts leaks bound turns timing reference) (fun _ => True)
    (fun _ => (app).silentPolicy) scheduler count
    (ReactiveApplication.Execution.initial (app) state) (fun _ _ => .nil)
  simp only [ite_true] at completed
  exact completed

/-- At every reached execution, the recovered clients preserve the full law stopped at
any predicate up to the horizon. -/
theorem clientPolicy_runUntilHorizon (initial : PMF (State graph)) (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat) (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile) (stop : (app).Execution → Prop) [DecidablePred stop]
    (horizon : Nat) (execution : (app).Execution)
    (reached : execution ∈ ((app).roundsFrom initial scheduler
      (clientPolicy timeouts leaks bound turns timing reference)
      execution.environmentRecall.length).support) :
    (app).runUntilHorizon scheduler (clientPolicy timeouts leaks bound turns timing reference)
      stop horizon execution =
      (app).runUntilHorizon scheduler (turnPolicy timeouts leaks bound turns timing reference)
        stop horizon execution := by
  rw [clientPolicy_roundsFrom] at reached
  obtain ⟨state, _, visited⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  apply ReactiveApplication.Policy.recover_runUntil
  exact (ReactiveApplication.consistentRecall_policyInvariant _).runRounds scheduler _ _ _
    (fun _ => .nil) visited

end Vegas.EventGraphRuntime
