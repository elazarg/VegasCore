/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeEnvironmentExecution
import Vegas.Pending.PhaseNativeResponse

/-! # Genuine clear counted histories project to native protocol histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

def protocolState : (P).ProtocolState → (N).ProtocolState :=
  Option.map (control runtime leaks plan)

def jointActions (joint : Player → Option (P).Action) : Player → Option (N).Action :=
  fun who => (joint who).map (action runtime leaks plan)

omit [Fintype Player] in
theorem actor_protocolState (state : (P).ProtocolState) :
    (N).actor (protocolState runtime leaks plan state) = (P).actor state := by
  cases state <;> rfl

omit [Fintype Player] in
theorem terminal_protocolState (state : (P).ProtocolState) :
    (N).terminal (protocolState runtime leaks plan state) ↔ (P).terminal state := by
  cases state <;> rfl

/-- Native legality retains exactly the actual actor and response availability;
no phase response is replaced or resampled. -/
theorem jointActions_legal (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (P).Scheduler) (state : (P).ProtocolState)
    (joint : Player → Option (P).Action)
    (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal state joint) :
    ((N).protocol (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler)).Legal
      (protocolState runtime leaks plan state) (jointActions runtime leaks plan joint) := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).legal_raw _ horizon scheduler legal
  refine ⟨?_, fun who => ?_⟩
  · change ¬ (N).terminal (protocolState runtime leaks plan state)
    exact fun stopped => raw.1 ((terminal_protocolState runtime leaks plan state).mp stopped)
  · have localLegal := raw.2 who
    cases chosen : joint who with
    | none =>
        simp only [jointActions, chosen, Option.map_none]
        rw [chosen] at localLegal
        change ¬ ((N).actor (protocolState runtime leaks plan state) = some who)
        rw [actor_protocolState]
        exact localLegal
    | some response =>
        simp only [jointActions, chosen, Option.map_some]
        rw [chosen] at localLegal
        change (N).actor (protocolState runtime leaks plan state) = some who ∧ True
        rw [actor_protocolState]
        exact ⟨(show (P).actor state = some who from localLegal.1), trivial⟩

/-- Every actual clear physical environment outcome has its exact native outcome
in the support of the same recorded command law. -/
theorem environmentStep_support_of_clear (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (chosen : (P).Command)
    (next : (P).Execution) (reached : next ∈ (current.execution.environmentStep P chosen).support)
    (afterClear : next.application.current.excluded = ∅) :
    execution runtime leaks plan next ∈
      ((execution runtime leaks plan current.execution).environmentStep N
        (command runtime leaks plan chosen)).support := by
  obtain ⟨joint, first, second, agreement, _record⟩ := exists_paired_environmentStep runtime leaks
    plan bounds ordered maximal inputs horizon scheduler trace clear chosen
  rw [← second, PMF.mem_support_map_iff] at reached
  obtain ⟨pair, supported, rfl⟩ := reached
  rw [← first, PMF.mem_support_map_iff]
  exact ⟨pair, supported, agreement pair supported afterClear⟩

omit [Fintype Player] in
private theorem clear_before_transition
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    {before after : (P).ProtocolState} (joint : Player → Option (P).Action)
    (realized : after ∈ ((P).transition (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler before joint).support)
    (clear : ∀ current, after = some current → current.execution.application.current.excluded = ∅) :
    ∀ current, before = some current → current.execution.application.current.excluded = ∅ := by
  intro current same
  subst before
  obtain ⟨next, rfl, _⟩ :=
    (P).transition_recall_prefix _ horizon scheduler current after joint realized
  have monotone := (phaseApplication_exclusion_monotone runtime leaks).transition _ horizon
    scheduler current next joint realized
  exact Finset.subset_empty.mp (clear next rfl ▸ monotone)

/-- One actual counted protocol transition projects without changing callback
counts, the selected command, or any actual response. -/
theorem transition_support_of_clear (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    {before after : (P).ProtocolState}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace before)
    (joint : Player → Option (P).Action)
    (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal before joint)
    (realized : after ∈ ((P).transition (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler before joint).support)
    (clear : ∀ current, after = some current → current.execution.application.current.excluded = ∅) :
    protocolState runtime leaks plan after ∈ ((N).transition (inputs.map State.initial) horizon
      (nativeScheduler runtime leaks plan scheduler) (protocolState runtime leaks plan before)
      (jointActions runtime leaks plan joint)).support := by
  have previous := clear_before_transition runtime leaks plan inputs horizon scheduler
    joint realized clear
  cases before with
  | none =>
      obtain ⟨initial, supported, rfl⟩ := PMF.support_map .. ▸ realized
      obtain ⟨input, inputSupport, rfl⟩ := PMF.support_map .. ▸ supported
      have physical := (PhaseRuntimeState.settle_of_clear plan.phases 0
        (⟨State.initial input, ∅⟩ : RecoveryState graph) ⟨State.initial input, ∅⟩ [] rfl).1
      have same : execution runtime leaks plan
          (ReactiveApplication.Execution.initial P (PhaseRuntimeState.initial plan input)) =
          ReactiveApplication.Execution.initial N (State.initial input) := by
        simp only [execution, ReactiveApplication.Execution.initial, PhaseRuntimeState.initial,
          physical, MessageNetwork.mapPayload_empty, List.map_nil]
      change _ ∈ ((inputs.map State.initial).map fun state =>
        some (⟨horizon, none, ReactiveApplication.Execution.initial N state⟩ : (N).Control)).support
      rw [PMF.mem_support_map_iff]
      refine ⟨State.initial input, ?_, ?_⟩
      · exact (PMF.mem_support_map_iff _ _ _).mpr ⟨input, inputSupport, rfl⟩
      · change some (⟨horizon, none, ReactiveApplication.Execution.initial N
            (State.initial input)⟩ : (N).Control) =
          some (⟨horizon, none, execution runtime leaks plan
            (ReactiveApplication.Execution.initial P
              (PhaseRuntimeState.initial plan input))⟩ : (N).Control)
        rw [same]
  | some current =>
      rcases current with ⟨remaining, actor, current⟩
      have beforeClear := previous ⟨remaining, actor, current⟩ rfl
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp realized
          have localLegal := legal.2 who
          cases chosen : joint who with
          | none =>
              rw [chosen] at localLegal
              have impossible : ¬ (P).actor (some ⟨remaining, some who, current⟩) = some who :=
                localLegal
              exact (impossible rfl).elim
          | some response =>
              rw [chosen] at localLegal
              have permitted : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
                  (current.recall who) (current.observe P who) :=
                localLegal.2
              have same := respond_of_onePacket runtime leaks plan bounds current
                (PhaseCount.countRecall_history runtime leaks
                  ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon
                    scheduler trace)) who response permitted
              simp only [ReactiveApplication.transition, protocolState, Option.map_some,
                control, jointActions, chosen, Option.map_some, Option.getD_some,
                PMF.mem_support_pure_iff]
              erw [same]
      | none =>
          cases remaining with
          | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
          | succ remaining =>
              obtain ⟨chosen, selected, moved⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              have nextClear := clear ⟨remaining, chosen.actor? P, next⟩ rfl
              have nativeSupported := environmentStep_support_of_clear runtime leaks plan bounds
                ordered maximal inputs horizon scheduler trace beforeClear chosen next supported
                nextClear
              have selectedNative : command runtime leaks plan chosen ∈
                  (nativeScheduler runtime leaks plan scheduler
                    (execution runtime leaks plan current).environmentRecall
                    ((execution runtime leaks plan current).observeEnvironment N)).support := by
                rw [nativeScheduler_at_clear runtime leaks plan bounds inputs horizon scheduler
                  trace
                  beforeClear, PMF.mem_support_map_iff]
                exact ⟨chosen, selected, rfl⟩
              change _ ∈ ((nativeScheduler runtime leaks plan scheduler
                (execution runtime leaks plan current).environmentRecall
                ((execution runtime leaks plan current).observeEnvironment N)).bind fun selected =>
                  ((execution runtime leaks plan current).environmentStep N selected).map
                    fun next =>
                    some (⟨remaining, selected.actor? N, next⟩ : (N).Control)).support
              rw [PMF.support_bind]
              refine Set.mem_iUnion₂.mpr ⟨command runtime leaks plan chosen, selectedNative, ?_⟩
              rw [PMF.mem_support_map_iff]
              refine ⟨execution runtime leaks plan next, nativeSupported, ?_⟩
              cases chosen <;> rfl

/-- The whole genuine clear counted trace has a native trace with exactly the
same number of callback and command transitions. -/
def nativeTrace (bounds : MessageBounds graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) :
    ∀ {state} (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state),
      (∀ current, state = some current → current.execution.application.current.excluded = ∅) →
      ((N).protocol (inputs.map State.initial) horizon
        (nativeScheduler runtime leaks plan scheduler)).Trace
          (protocolState runtime leaks plan state)
  | _, .start, _clear => .start
  | _, .extend before joint legal realized, clear =>
      .extend (nativeTrace bounds ordered maximal inputs horizon scheduler before
          (clear_before_transition runtime leaks plan inputs horizon scheduler joint realized
            clear))
        (jointActions runtime leaks plan joint)
        (jointActions_legal runtime leaks plan bounds inputs horizon scheduler _ joint legal)
        (transition_support_of_clear runtime leaks plan bounds ordered maximal inputs horizon
          scheduler before joint legal realized clear)

theorem nativeTrace_length (bounds : MessageBounds graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) :
    ∀ {state} (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state)
      (clear : ∀ current, state = some current →
        current.execution.application.current.excluded = ∅),
      (nativeTrace runtime leaks plan bounds ordered maximal inputs horizon scheduler
        trace clear).length = trace.length
  | _, .start, _ => rfl
  | _, .extend before joint legal realized, clear => by
      simp only [nativeTrace, Trace.length]
      rw [nativeTrace_length]

end Vegas.EventGraphRuntime.PhaseNativeProjection
