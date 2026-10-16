/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapGuard
import Interaction.ReactiveRecordedResponse

/-! # Actual phased transition replay under primitive native guards -/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open EventGraph Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {allowed : Set graph.Inputs} (swap : HiddenSwap graph)

def phaseControl (control : (phaseApplication runtime leaks).Control) :
    (phaseApplication runtime leaks).Control :=
  ⟨control.remaining, control.actor, swap.phaseExecution control.execution⟩

def phaseProtocolState : (phaseApplication runtime leaks).ProtocolState →
    (phaseApplication runtime leaks).ProtocolState := Option.map swap.phaseControl

def phaseJoint (joint : Player → Option (phaseApplication runtime leaks).Action) :
    Player → Option (phaseApplication runtime leaks).Action :=
  fun who => (joint who).map swap.phaseAction

theorem getD_phaseJoint (joint : Player → Option (phaseApplication runtime leaks).Action)
    (who : Player) : (swap.phaseJoint joint who).getD ⟨none⟩ =
      swap.phaseAction ((joint who).getD ⟨none⟩) := by
  simp only [phaseJoint]
  cases joint who <;> rfl

/-- A newly remembered response inherits the primitive request guard from its
actual post-response execution. -/
theorem phaseRequestFixed_of_respond (current : (phaseApplication runtime leaks).Execution)
    (who : Player) (response : (phaseApplication runtime leaks).Action)
    (guarded : PhaseSwapGuard runtime leaks swap allowed
      (current.respond (phaseApplication runtime leaks) who response)) :
    ∀ submission, response.transmission = some submission → submission.evidence.FixedBy swap := by
  obtain ⟨emitted, remembered⟩ :=
    (phaseApplication runtime leaks).respond_recall_entry current who response
  have member : (⟨current.observe (phaseApplication runtime leaks) who, response, emitted⟩ :
      (phaseApplication runtime leaks).PlayerEntry) ∈
        (current.respond (phaseApplication runtime leaks) who response).recall who := by
    rw [remembered]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  exact guarded.requests who _ member

/-- An actually admitted include reads only guarded current-phase revelations.
Any new binding association is checked at the actual clear included result. -/
theorem phaseInclusionFixed_of_guards (current : (phaseApplication runtime leaks).Execution)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : current.network.lookup id = some message)
    (admitted : (message.payload.tokenValid current.application.attempt &&
      current.application.allows message.payload.packet.call &&
      !current.application.current.excludedCall message.payload.packet.call) = true)
    (beforeGuard : PhaseSwapGuard runtime leaks swap allowed current)
    (afterGuard : PhaseSwapGuard runtime leaks swap allowed
      (current.includePending (phaseApplication runtime leaks) id)) :
    InclusionFixed runtime swap current.application.current.native
      ⟨message.id, message.payload.packet.call⟩ := by
  constructor
  · intro native event candidate handled callEq
    change message.payload.packet.call = .commitment event candidate at callEq
    let raw : PhaseRuntimeState graph := { current.application with
      current := current.application.current.inclusionResult message.payload.packet.call native }
    have phaseHandled : current.application.handle runtime message = some raw.normalize := by
      simp only [PhaseRuntimeState.handle, admitted, ↓reduceIte, handled, Option.map_some]
      rfl
    have appEq : (current.includePending (phaseApplication runtime leaks) id).application =
        raw.normalize := by
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      simp only [found]
      change (current.application.handle runtime message).getD current.application = _
      rw [phaseHandled]
      rfl
    have clear : raw.normalize.current.excluded = ∅ := appEq ▸ afterGuard.clear
    have sameNative : RecoveryState.native (current.includePending
        (phaseApplication runtime leaks) id).application.current = native := by
      rw [appEq, (PhaseRuntimeState.normalize_of_clear raw clear).1]
      rfl
    apply afterGuard.compatible event candidate
    rw [sameNative]
    have accepted : handle runtime current.application.current.native
        ⟨message.id, .commitment event candidate⟩ = some native := by
      simpa only [callEq] using handled
    rw [(handle_commitment_tables runtime _ native message.id event candidate accepted).2.1,
      Function.update_self]
  · intro event named ready
    obtain ⟨candidate, raw, callEq⟩ := named
    change message.payload.packet.call = .opening event candidate raw at callEq
    have allowed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).2
    cases installed : current.application.phases with
    | nil =>
        simp only [PhaseRuntimeState.allows, installed, List.head?_nil, Bool.false_eq_true]
          at allowed
    | cons phase remaining =>
        have inside : event ∈ phase.events := by
          apply of_decide_eq_true
          simpa only [PhaseRuntimeState.allows, installed, List.head?_cons, callEq,
            Payload.event?] using allowed
        exact beforeGuard.active phase remaining installed event inside ready

/-- Full physical environment replay uses the phase gate before its native
read guards. Scheduler observation and recall remain identical. -/
theorem environmentStep_phaseExecution_of_admitted
    (current : (phaseApplication runtime leaks).Execution)
    (command : (phaseApplication runtime leaks).Command)
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (fixed : ∀ id envelope, command = .include id → current.network.lookup id = some envelope →
      (envelope.payload.tokenValid current.application.attempt &&
        current.application.allows envelope.payload.packet.call &&
        !current.application.current.excludedCall envelope.payload.packet.call) = true →
      InclusionFixed runtime swap current.application.current.native
        ⟨envelope.id, envelope.payload.packet.call⟩) :
    (swap.phaseExecution current).environmentStep (phaseApplication runtime leaks) command =
      (current.environmentStep (phaseApplication runtime leaks) command).map
        swap.phaseExecution := by
  unfold ReactiveApplication.Execution.environmentStep
  rw [observeEnvironment_phaseExecution, PMF.map_comp]
  cases command with
  | activate who => simp only [phaseExecution_network, PMF.map_comp]; rfl
  | wait => simp only [PMF.pure_map]; rfl
  | «include» id =>
      simp only [PMF.pure_map]
      rw [swap.includePending_phaseExecution_of_admitted current id expiry
        (fun envelope found => fixed id envelope rfl found)]
      rfl
  | application command =>
      change PMF.map _ (PMF.map _ ((current.application.swap swap).environment runtime command)) = _
      rw [PhaseRuntimeState.environment_swap runtime swap current.application command expiry,
        PMF.map_comp, PMF.map_comp, PMF.map_comp]
      rfl

/-- Every realized transition into a clear primitive guard replays under the
same scheduler. Setup support is required only at the guarded original input
tuple, rather than at every other tuple in the prior. -/
theorem phaseTransition_swap
    (initial : PMF (phaseApplication runtime leaks).State)
    (initialClosed : ∀ state ∈ initial.support,
      state.current.native.config.inputs ∈ allowed → state.swap swap ∈ initial.support)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (source target : (phaseApplication runtime leaks).ProtocolState)
    (joint : Player → Option (phaseApplication runtime leaks).Action)
    (reached : target ∈ ((phaseApplication runtime leaks).transition initial horizon scheduler
      source joint).support)
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (native : ∀ control, source = some control →
      ∃ draw, control.execution.application.Invariant draw)
    (guarded : ∀ control, target = some control →
      PhaseSwapGuard runtime leaks swap allowed control.execution) :
    swap.phaseProtocolState target ∈ ((phaseApplication runtime leaks).transition initial horizon
      scheduler (swap.phaseProtocolState source) (swap.phaseJoint joint)).support := by
  let app := phaseApplication runtime leaks
  cases source with
  | none =>
      rw [ReactiveApplication.transition, PMF.support_map] at reached
      obtain ⟨state, member, rfl⟩ := reached
      change some (swap.phaseControl
        ⟨horizon, none, ReactiveApplication.Execution.initial _ state⟩) ∈
        (app.transition initial horizon scheduler none _).support
      rw [ReactiveApplication.transition, PMF.support_map]
      have allowedInputs := (guarded _ rfl).inputs
      exact ⟨state.swap swap, initialClosed state member allowedInputs, rfl⟩
  | some before =>
      obtain ⟨after, rfl, _⟩ := app.transition_recall_prefix initial horizon scheduler
        before target joint reached
      have afterGuard := guarded after rfl
      have beforeGuard := phaseSwapGuard_of_transition runtime leaks swap allowed initial horizon
        scheduler before after joint reached (native before rfl) afterGuard
      rcases before with ⟨remaining, actor, current⟩
      cases actor with
      | some who =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          change some (swap.phaseControl ⟨remaining, none, current.respond app who _⟩) ∈
            (app.transition initial horizon scheduler
              (some ⟨remaining, some who, swap.phaseExecution current⟩) _).support
          rw [ReactiveApplication.transition, PMF.mem_support_pure_iff]
          change _ = some (⟨remaining, none, (swap.phaseExecution current).respond app who
            ((swap.phaseJoint joint who).getD ⟨none⟩)⟩ : app.Control)
          rw [swap.getD_phaseJoint, swap.respond_phaseExecution current who _
            (swap.phaseRequestFixed_of_respond current who _ afterGuard)]
          rfl
      | none =>
          cases remaining with
          | zero =>
              cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
              exact (PMF.mem_support_pure_iff _ _).mpr rfl
          | succ remaining =>
              rw [ReactiveApplication.transition, PMF.mem_support_bind_iff] at reached
              obtain ⟨command, scheduled, moved⟩ := reached
              rw [PMF.support_map] at moved
              obtain ⟨next, stepped, nextEq⟩ := moved
              cases Option.some.inj nextEq
              change some (swap.phaseControl ⟨remaining, _, next⟩) ∈
                (app.transition initial horizon scheduler
                  (some ⟨remaining + 1, none, swap.phaseExecution current⟩) _).support
              rw [ReactiveApplication.transition, PMF.mem_support_bind_iff]
              refine ⟨command, ?_, ?_⟩
              · change command ∈ (scheduler current.environmentRecall
                  ((swap.phaseExecution current).observeEnvironment app)).support
                rw [swap.observeEnvironment_phaseExecution]
                exact scheduled
              · rw [swap.environmentStep_phaseExecution_of_admitted current command expiry,
                  PMF.map_comp, PMF.support_map]
                · exact ⟨next, stepped, rfl⟩
                · intro id envelope commandEq found admitted
                  subst commandEq
                  have included : PhaseSwapGuard runtime leaks swap allowed
                      (current.includePending app id) := by
                    unfold ReactiveApplication.Execution.environmentStep at stepped
                    rw [PMF.support_map] at stepped
                    obtain ⟨included, supported, rfl⟩ := stepped
                    rw [PMF.mem_support_pure_iff] at supported
                    subst included
                    exact ⟨afterGuard.clear, afterGuard.inputs, afterGuard.compatible,
                      afterGuard.completed, afterGuard.active, afterGuard.requests⟩
                  exact swap.phaseInclusionFixed_of_guards current id envelope found admitted
                    beforeGuard included

end Vegas.EventGraphRuntime.HiddenSwap
