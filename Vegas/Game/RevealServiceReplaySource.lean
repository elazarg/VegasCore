/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceWatcherSupport
import Vegas.Game.RevealServiceTraffic
import Vegas.Game.RevealServiceReplayRelation
import Vegas.Pending.ReactiveServicePublication

/-! # Clean source prefixes used by replay continuation comparison

The facts concern every legal history of the retained service, including
histories outside equilibrium support. In particular, activation cannot sample
a newly transmitted unpublished packet in this source restriction.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)

include reveals observer openable in
theorem active_history_clean (history : (protocol setup leaks bounds watcher).History)
    (control : (application setup leaks).Control) (state : history.state = some control)
    (who : Player) (active : control.actor = some who) :
    control.execution.network.leaked = (fun _ => []) ∧
      (∀ message ∈ control.execution.network.pending,
        message.id ∈ control.execution.network.ledger.map Message.id) ∧
      (∀ input ∈ control.execution.network.inputs,
        input.envelope.id ∈ control.execution.network.ledger.map Message.id) := by
  by_cases watches : who = watcher
  · subst who
    exact watcher_history_clean setup leaks bounds watcher reveals observer openable
      history control state active
  · let responses := menu setup leaks bounds watcher
    let reference := responses.uniformPolicy (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)
    have acts : (protocol setup leaks bounds watcher).active history.state who := by
      change (application setup leaks).actor history.state = some who
      rw [state]
      exact active
    obtain ⟨event, owned, _depth, supported⟩ := owner_history_supported setup leaks bounds
      watcher who reveals watches history acts
    obtain ⟨boundary, _boundarySupport, current, initial, _initialSupport, source,
        _before, related, _decoded⟩ := owner_supported setup leaks bounds watcher who reveals
      observer openable reference event owned history supported
    have same : control =
        ⟨horizon setup watcher - blockOffset event.val - 1, some who,
          ownerOpportunity setup leaks who boundary⟩ :=
      Option.some.inj (state.symm.trans current)
    subst control
    exact PrefixCheckpoint.runtime_fact (fun execution =>
      execution.network.leaked = (fun _ => []) ∧
        (∀ message ∈ execution.network.pending,
          message.id ∈ execution.network.ledger.map Message.id) ∧
        (∀ input ∈ execution.network.inputs,
          input.envelope.id ∈ execution.network.ledger.map Message.id))
      (fun _ _ _ _ checkpoint => ⟨checkpoint.leaked, checkpoint.pending, checkpoint.inputs⟩)
      _ _ _ _ _ _ _ _ related

include reveals observer openable in
/-- Cleanliness before activation follows from the actual reachable active
history. No assumption about the passive sampler is needed. -/
theorem before_activation_published
    (history : (protocol setup leaks bounds watcher).History)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (state : history.state = some ⟨remaining + 1, none, execution⟩) (who : Player)
    (scheduled : (.activate who) ∈
      (scheduler setup leaks watcher execution.environmentRecall
        (execution.observeEnvironment (application setup leaks))).support) :
    ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id := by
  let app := application setup leaks
  let selected := (app.observePending who execution.network.pending).support_nonempty.choose
  have selectedSupport : selected ∈ (app.observePending who execution.network.pending).support :=
    (app.observePending who execution.network.pending).support_nonempty.choose_spec
  let learned := { execution with network := execution.network.learn who selected }
  let next : app.Execution := { learned with environmentRecall := execution.environmentRecall ++
    [⟨execution.observeEnvironment app, .activate who⟩] }
  have nextSupport : next ∈ (execution.environmentStep app (.activate who)).support := by
    rw [ReactiveApplication.Execution.environmentStep, PMF.support_map]
    refine ⟨learned, ?_, rfl⟩
    rw [PMF.support_map]
    exact ⟨selected, selectedSupport, rfl⟩
  have legal : (protocol setup leaks bounds watcher).Legal history.state (fun _ => none) := by
    rw [state]
    refine ⟨?_, ?_⟩
    · change ¬ app.terminal (some ⟨remaining + 1, none, execution⟩)
      simp [ReactiveApplication.terminal]
    · intro player
      change ¬ app.actor (some ⟨remaining + 1, none, execution⟩) = some player
      simp [ReactiveApplication.actor]
  have transition : some ⟨remaining, some who, next⟩ ∈
      ((protocol setup leaks bounds watcher).step history.state
        ⟨fun _ => none, legal⟩).support := by
    change _ ∈ (app.transition (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) history.state (fun _ => none)).support
    rw [state, ReactiveApplication.transition, PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨.activate who, scheduled, ?_⟩
    rw [PMF.support_map]
    exact ⟨next, nextSupport, rfl⟩
  let after := history.extend legal transition
  have clean := active_history_clean setup leaks bounds watcher reveals observer openable
    after ⟨remaining, some who, next⟩ rfl who rfl
  exact clean.2.1

omit [Fintype Player] in
/-- The fixed service makes the same scheduler choice after watcher aliases.
Its network slot idles. -/
theorem replay_scheduler_eq
    (control : (application setup leaks).Control)
    (second : (application setup leaks).Execution)
    (same : ReplayAgreement setup leaks watcher control.execution second) :
    scheduler setup leaks watcher control.execution.environmentRecall
        (control.execution.observeEnvironment (application setup leaks)) =
      scheduler setup leaks watcher second.environmentRecall
        (second.observeEnvironment (application setup leaks)) := by
  unfold scheduler
  rw [same.position]
  cases current : (plan setup watcher)[second.environmentRecall.length]? with
  | none => rfl
  | some instruction =>
      cases instruction with
      | player who | sample event | tick | expire event => rfl
      | includeLatest event owner =>
          exact congrArg PMF.pure (same.reserved_selection event owner)
      | wire =>
          dsimp only
          rw [(runtime setup).idleNetwork_instruction,
            (runtime setup).idleNetwork_instruction]

omit [Fintype Player] in
theorem scheduler_inclusion_fresh
    (past : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView) (id : MessageId Player)
    (selected : (.include id) ∈ (scheduler setup leaks watcher past view).support) :
    id ∉ view.network.ledger.map Message.id := by
  unfold scheduler at selected
  split at selected
  · cases (PMF.mem_support_pure_iff _ _).mp selected
  · exact (runtime setup).interactionInstruction_fresh leaks
      ((runtime setup).idleNetwork leaks) past view _ id selected

end Vegas
