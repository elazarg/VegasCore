/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ValueSwapPairs
import Vegas.Pending.PhaseClearNativeProgress
import Vegas.Pending.OnePacketValueSwap
import Vegas.Pending.PhaseCountMenu
import Vegas.EventGraph.PrivateInputs
import Interaction.ReactiveRecordedResponse
import Vegas.Pending.PhaseSwapInformation
import Interaction.ReactiveRoundTrace
import Vegas.Pending.PhaseBindingAcceptance
import Interaction.ReactiveStopping
import Interaction.ReactiveOwnPlay
import Interaction.ReactiveEnvironmentMass
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay

/-! # Actual transitions after replacing a lost private preparation

Only the designated sender's inert private alias is projected away. Both
endpoints remain genuine executions; the physical network, scheduler recall
and every other player's complete input are retained.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

local notation "app" => phaseApplication runtime leaks

/-- Actual counted traces read their complete own-action word from literal recall. -/
theorem phase_trace_ownPlay [Fintype Player]
    (bounds : MessageBounds graph) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some control)) (who : Player) :
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon scheduler).ownPlay
        who trace = (app).recallOwnPlay (control.execution.recall who) := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  change (menu.signals initial horizon scheduler).ownPlay who trace = _
  rw [← menu.ownPlay_toRawTrace initial horizon scheduler who trace, (app).trace_ownPlay]
  rfl

/-- Retain the literal target prefix when extending by its genuine response.
This is the original protocol constructor, with its extension evidence. -/
theorem phase_respond_trace_prefix [Fintype Player]
    (bounds : MessageBounds graph) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (execution : (app).Execution)
    (actor : Player) (response : (app).Action)
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some ⟨remaining, some actor, execution⟩))
    (offered : response ∈ PhaseCount.onePacketActions runtime leaks bounds actor
      (execution.recall actor) (execution.observe app actor)) :
    ∃ trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some ⟨remaining, none, execution.respond app actor response⟩),
      TracePrefix prior trace ∧ trace.transitionMass = prior.transitionMass ∧
      ∀ who,
        ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
          scheduler).ownPlay who trace =
          if who = actor then
            (some (execution.recall actor, execution.observe app actor), response) ::
              ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
                scheduler).ownPlay who prior
          else ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
            scheduler).ownPlay who prior := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let joint : Player → Option (app).Action :=
    fun who => if who = actor then some response else none
  have legal : (menu.protocol initial horizon scheduler).Legal
      (some ⟨remaining, some actor, execution⟩) joint := by
    constructor
    · simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal]
    · intro who
      by_cases same : who = actor
      · subst who
        simpa [menu, PhaseCount.onePacketMenu, joint,
          ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
          ReactiveApplication.ResponseMenu.available] using offered
      · simp [joint, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
          same, Ne.symm same]
  have moved : some (⟨remaining, none, execution.respond app actor response⟩ : (app).Control) ∈
      ((menu.protocol initial horizon scheduler).step
        (some ⟨remaining, some actor, execution⟩) ⟨joint, legal⟩).support := by
    change _ ∈ (PMF.pure _).support
    simp only [joint, ↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff]
  refine ⟨prior.extend joint legal moved, ?_⟩
  refine ⟨TracePrefix.extend (prefixTrace := prior) TracePrefix.refl joint legal moved, ?_, ?_⟩
  · rw [Trace.transitionMass_extend]
    change prior.transitionMass * ((PMF.pure _ : PMF (app).ProtocolState) _).toReal = _
    simp only [joint, ↓reduceIte, Option.getD_some, PMF.pure_apply_self,
      ENNReal.toReal_one, mul_one]
  · intro who
    rw [phase_trace_ownPlay bounds initial horizon scheduler _ _ who,
      phase_trace_ownPlay bounds initial horizon scheduler _ prior who]
    by_cases same : who = actor
    · subst who
      simp only [↓reduceIte]
      exact (app).respond_ownPlay execution actor response
    · simp only [same, ↓reduceIte]
      rw [(app).respond_recall_other execution actor who same response]

/-- Retain the literal target prefix and original supported Nature atom when
extending by its selected environment command. -/
theorem phase_environment_trace_prefix [Fintype Player]
    (bounds : MessageBounds graph) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (execution next : (app).Execution)
    (command : (app).Command)
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (selected : command ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment app)).support)
    (moved : next ∈ (execution.environmentStep app command).support) :
    ∃ trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some ⟨remaining, command.actor? app, next⟩),
      TracePrefix prior trace ∧ trace.transitionMass = prior.transitionMass *
        ((scheduler execution.environmentRecall (execution.observeEnvironment app) command) *
          (execution.environmentStep app command) next).toReal ∧
      ∀ who,
        ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
          scheduler).ownPlay who trace =
          ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
            scheduler).ownPlay who prior := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have legal : (menu.protocol initial horizon scheduler).Legal
      (some ⟨remaining + 1, none, execution⟩) (fun _ => none) := by
    constructor
    · simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal]
    · intro who
      simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor]
  have realized : some (⟨remaining, command.actor? app, next⟩ : (app).Control) ∈
      ((menu.protocol initial horizon scheduler).step
        (some ⟨remaining + 1, none, execution⟩) ⟨fun _ => none, legal⟩).support := by
    change _ ∈ ((scheduler execution.environmentRecall
      (execution.observeEnvironment app)).bind _).support
    rw [PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨command, selected, ?_⟩
    rw [PMF.support_map]
    exact ⟨next, moved, rfl⟩
  refine ⟨prior.extend (fun _ => none) legal realized,
    TracePrefix.extend TracePrefix.refl (fun _ => none) legal realized, ?_, ?_⟩
  · rw [Trace.transitionMass_extend]
    change prior.transitionMass * ((app).transition initial horizon scheduler
      (some ⟨remaining + 1, none, execution⟩) (fun _ => none)
        (some ⟨remaining, command.actor? app, next⟩)).toReal = _
    rw [(app).transition_environment_apply initial horizon scheduler remaining execution next
      command moved]
  · intro who
    rw [phase_trace_ownPlay bounds initial horizon scheduler _ _ who,
      phase_trace_ownPlay bounds initial horizon scheduler _ prior who,
      ← (app).environmentStep_recall execution next command moved]


end Vegas.EventGraphRuntime.HiddenSwap
