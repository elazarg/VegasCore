/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionPublicRecord
import Interaction.ReactiveResponseEmbedding
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Actual environment prefixes at the first public exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (State graph)) (horizon : Nat)
  (scheduler : (runtime.reactiveApplication leaks).Scheduler)
  (menu : (runtime.reactiveApplication leaks).ResponseMenu)

local notation "nativeApp" => runtime.reactiveApplication leaks
local notation "protocol" => menu.protocol initial horizon scheduler
local notation "model" => menu.information initial horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := nativeApp) (fun state => PublicExclusionRecord (RecoveryState.mk state ∅))

/-- An actual idle clear prefix and its realized environment transition into
this complete history. The chosen command retains its true scheduler support. -/
def ClearEnvironmentBoundary (history : (protocol).History) : Prop :=
  ∃ (remaining : Nat) (execution : (nativeApp).Execution)
    (prior : (protocol).Trace (some ⟨remaining + 1, none, execution⟩))
    (command : (nativeApp).Command) (next : (nativeApp).Execution),
    PublicExclusionRecord (⟨execution.application, ∅⟩ : RecoveryState graph) ∧
      command ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment nativeApp)).support ∧
      next ∈ (execution.environmentStep nativeApp command).support ∧
      history.state = some ⟨remaining, command.actor? nativeApp, next⟩ ∧
      TracePrefix prior history.trace

omit [Fintype Player] in
private theorem record_respond (execution : (nativeApp).Execution) (who : Player)
    (response : (nativeApp).Action)
    (valid : PublicExclusionRecord (⟨execution.application, ∅⟩ : RecoveryState graph)) :
    PublicExclusionRecord
      (⟨(execution.respond nativeApp who response).application, ∅⟩ : RecoveryState graph) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact valid
  | some submission => exact valid.submit who submission

omit [Fintype Player] in
private theorem transition_clear_or_environment (current : (nativeApp).Control)
    (target : (nativeApp).ProtocolState) (joint : Player → Option (nativeApp).Action)
    (valid : PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph))
    (realized : target ∈ ((nativeApp).transition initial horizon scheduler
      (some current) joint).support) :
    (∃ next, target = some next ∧
      PublicExclusionRecord (⟨next.execution.application, ∅⟩ : RecoveryState graph)) ∨
    ∃ (remaining : Nat) (execution : (nativeApp).Execution),
      current = ⟨remaining + 1, none, execution⟩ ∧
      ∃ (command : (nativeApp).Command) (next : (nativeApp).Execution),
        command ∈ (scheduler execution.environmentRecall
          (execution.observeEnvironment nativeApp)).support ∧
        next ∈ (execution.environmentStep nativeApp command).support ∧
        target = some ⟨remaining, command.actor? nativeApp, next⟩ := by
  rcases current with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
    simp only [ReactiveApplication.transition, PMF.mem_support_pure_iff] at realized
    refine Or.inl ⟨_, realized, ?_⟩
    exact record_respond runtime leaks execution who _ valid
  | none =>
    cases remaining with
    | zero =>
      simp only [ReactiveApplication.transition, PMF.mem_support_pure_iff] at realized
      exact Or.inl ⟨_, realized, valid⟩
    | succ remaining =>
      simp only [ReactiveApplication.transition, PMF.mem_support_bind_iff] at realized
      obtain ⟨command, chosen, moved⟩ := realized
      rw [PMF.mem_support_map_iff] at moved
      obtain ⟨next, moved, same⟩ := moved
      exact Or.inr ⟨remaining, execution, rfl, command, next, chosen, moved, same.symm⟩

/-- At every stopped endpoint before any additional stopping condition, public
exclusion can arise only from one genuine environment move out of a clear
prefix of that very history. Player responses cannot create public exclusion. -/
theorem responseMenu_stopped_exclusion_boundary
    (certificate : (protocol).WellFoundedHistories)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (extraStop : (protocol).History → Prop)
    (start : (protocol).History) (current : (nativeApp).Control)
    (state : start.state = some current)
    (clear : PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph)) :
    ∀ final ∈ ((model).runBehavioralUntil certificate profile
      (fun history => ¬ Clear history.state ∨ extraStop history)
      start).support,
      Clear final.state ∨
      ClearEnvironmentBoundary runtime leaks initial horizon scheduler menu final := by
  classical
  let stopped := fun history : (protocol).History =>
    ¬ Clear history.state ∨ extraStop history
  let property := fun history : (protocol).History =>
    (∃ current, history.state = some current) ∧
      (Clear history.state ∨
        ClearEnvironmentBoundary runtime leaks initial horizon scheduler menu history)
  have initialProperty : property start := by
    refine ⟨⟨current, state⟩, Or.inl ?_⟩
    change Clear start.state
    rw [state]
    exact clear
  have preserved : ∀ history, ¬ stopped history → ¬ (protocol).terminal history.state →
      property history → ∀ next ∈ ((model).runBehavioralFrom profile 1 history).support,
        property next := by
    intro history going running valid next supported
    have currentClear : Clear history.state :=
      not_not.mp (fun failed => going (Or.inl failed))
    rw [(model).runBehavioralFrom_succ_of_not_terminal profile 0 running,
      PMF.mem_support_bind_iff] at supported
    obtain ⟨draw, _chosen, stepped⟩ := supported
    rw [PMF.mem_support_bindOnSupport_iff] at stepped
    obtain ⟨target, realized, reached⟩ := stepped
    change next ∈ (PMF.pure _).support at reached
    rw [PMF.mem_support_pure_iff] at reached
    subst reached
    obtain ⟨current, currentState⟩ := valid.1
    rcases history with ⟨before, trace⟩
    change before = some current at currentState
    cases currentState
    change target ∈ ((nativeApp).transition initial horizon scheduler
      (some current) draw.1).support at realized
    have record : PublicExclusionRecord
        (⟨current.execution.application, ∅⟩ : RecoveryState graph) := currentClear
    rcases transition_clear_or_environment runtime leaks initial horizon scheduler current target
      draw.1 record realized with ⟨next, same, nextRecord⟩ |
        ⟨remaining, execution, beforeEq, command, next, chosen, moved, same⟩
    · refine ⟨⟨next, same⟩, Or.inl ?_⟩
      change Clear target
      rw [same]
      exact nextRecord
    · cases beforeEq
      exact ⟨⟨_, same⟩, Or.inr ⟨remaining, execution, trace, command, next,
        record, chosen, moved, same, .extend .refl draw.1 draw.2 realized⟩⟩
  intro final member
  exact ((model).runBehavioralUntil_support_history_closed certificate profile stopped property
    preserved start initialProperty final member).2

end Vegas.EventGraphRuntime
