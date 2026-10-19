/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalLostCandidateReplay
import Interaction.ReactiveInactiveRecall
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

private theorem eraseRecall_wait (execution : (app).Execution) (owner : Player) :
    (execution.respond app owner ⟨none⟩).eraseRecall app owner =
      execution.eraseRecall app owner := by
  classical
  simp only [ReactiveApplication.Execution.respond, ReactiveApplication.Execution.eraseRecall]
  congr 1
  funext who
  by_cases same : who = owner <;> simp only [same, ↓reduceIte]

/-- A foreign callback retains its literal raw response, not a normalized
representative. Its entire input is recovered from the actual original trace. -/
theorem preparationOnly_foreign_respond_erased [Fintype Player]
    (owner actor : Player) (different : actor ≠ owner) (slot : CandidateSlot graph)
    (first second : Raw L) (bounds : MessageBounds graph)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (original image : (app).Execution)
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some ⟨remaining, some actor, original⟩))
    (paired : image.eraseRecall app owner =
      ((preparationOnly (owner, slot) first second).phaseExecution original).eraseRecall app owner)
    (response : (app).Action)
    (offered : response ∈ PhaseCount.onePacketActions runtime leaks bounds actor
      (original.recall actor) (original.observe app actor)) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds actor
        (image.recall actor) (image.observe app actor) ∧
      (image.respond app actor response).eraseRecall app owner =
        ((preparationOnly (owner, slot) first second).phaseExecution
          (original.respond app actor response)).eraseRecall app owner := by
  let swap := preparationOnly (owner, slot) first second
  have handles (query : CandidateSlot graph) : swap.raw (actor, query) = id := by
    apply preparationOnly_raw_of_ne
    exact fun same => different (congrArg Prod.fst same)
  have input := swap.phaseInput_eq_of_fixed bounds initial horizon scheduler
    ⟨remaining, some actor, original⟩ prior actor (fun _ _ => rfl) (fun _ _ => rfl) handles
  change ((swap.phaseExecution original).recall actor,
    (swap.phaseExecution original).observe app actor) =
      (original.recall actor, original.observe app actor) at input
  have recalled : image.recall actor = (swap.phaseExecution original).recall actor := by
    have remembered := congrArg (fun execution : (app).Execution => execution.recall actor) paired
    simpa only [ReactiveApplication.eraseRecall_recall_other app _ _ _ different] using remembered
  have observed : image.observe app actor = (swap.phaseExecution original).observe app actor :=
    by simpa only [ReactiveApplication.eraseRecall_observe] using
      congrArg (fun execution : (app).Execution => execution.observe app actor) paired
  have stored : (swap.phaseExecution original).recall actor = original.recall actor :=
    congrArg Prod.fst input
  have viewed : (swap.phaseExecution original).observe app actor = original.observe app actor :=
    congrArg Prod.snd input
  constructor
  · rw [recalled, observed, stored, viewed]
    exact offered
  · rw [ReactiveApplication.eraseRecall_respond_other app image owner actor different response,
      paired, ← ReactiveApplication.eraseRecall_respond_other app
        (swap.phaseExecution original) owner actor different response,
      swap.respond_phaseExecution_of_onePacket bounds original actor response handles offered]

/-- A later forced WAIT adds no physical effect. The target WAIT is always
in the actual counted menu, independently of its changed private recall. -/
theorem preparationOnly_wait_erased
    (owner : Player) (slot : CandidateSlot graph) (first second : Raw L)
    (original image : (app).Execution)
    (paired : image.eraseRecall app owner =
      ((preparationOnly (owner, slot) first second).phaseExecution original).eraseRecall
        app owner) :
    (image.respond app owner ⟨none⟩).eraseRecall app owner =
      ((preparationOnly (owner, slot) first second).phaseExecution
        (original.respond app owner ⟨none⟩)).eraseRecall app owner := by
  let swap := preparationOnly (owner, slot) first second
  have wait := swap.respond_phaseExecution original owner ⟨none⟩
    (by intro submission impossible; cases impossible)
  change (image.respond app owner ⟨none⟩).eraseRecall app owner =
    (swap.phaseExecution (original.respond app owner ⟨none⟩)).eraseRecall app owner
  rw [← wait]
  exact (eraseRecall_wait image owner).trans
    (paired.trans (eraseRecall_wait (swap.phaseExecution original) owner).symm)

/-- The actual original environment atom has an actual image atom with the
same physical projection. This includes the primitive closing command and
its normalization; no normalized target outcome is supplied. -/
theorem preparationOnly_environment_erased
    (owner : Player) (slot : CandidateSlot graph) (first second : Raw L)
    (original image : (app).Execution)
    (paired : image.eraseRecall app owner =
      ((preparationOnly (owner, slot) first second).phaseExecution original).eraseRecall app owner)
    (command : (app).Command) (next : (app).Execution)
    (moved : next ∈ (original.environmentStep app command).support)
    (unused : original.application.current.native.HandleUnused (owner, slot))
    (rejected : ∀ id message event, command = .include id →
      original.network.lookup id = some message →
      message.payload.packet.call = .commitment event (owner, slot) →
        original.application.handle runtime message = none) :
    ∃ target ∈ (image.environmentStep app command).support,
      target.eraseRecall app owner =
        ((preparationOnly (owner, slot) first second).phaseExecution next).eraseRecall
      app owner := by
  let swap := preparationOnly (owner, slot) first second
  have sameLaw : (image.environmentStep app command).map (fun target =>
        target.eraseRecall app owner) =
      ((original.environmentStep app command).map swap.phaseExecution).map (fun target =>
        target.eraseRecall app owner) := by
    rw [ReactiveApplication.eraseRecall_environmentStep, paired,
      ← ReactiveApplication.eraseRecall_environmentStep,
      environmentStep_preparationOnly (owner, slot) first second original command unused rejected]
  have supported : (swap.phaseExecution next).eraseRecall app owner ∈
      ((image.environmentStep app command).map (fun target =>
        target.eraseRecall app owner)).support := by
    rw [sameLaw, PMF.map_comp, PMF.support_map]
    exact ⟨next, moved, rfl⟩
  rw [PMF.support_map] at supported
  exact supported

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
