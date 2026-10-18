/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperOriginalObservation
import Vegas.Pending.PhaseBindingOpaqueClock
import Vegas.Pending.PhaseBindingClearCommandLaw
import Vegas.Examples.CommitSeedBroadcastOriginalCompletion
import Interaction.ReactiveRawRoundTrace

/-! # Actual original commands for the helper-prefix comparison -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem pending_not_application (identifier : MessageId Player)
    (view : app.EnvironmentView) (operation : EnvironmentCommand graph) :
    pendingCommand identifier view ≠ .application operation := by
  cases selected : view.network.pending.any (fun message => message.id = identifier) <;>
    simp [pendingCommand, selected]

private theorem ready_not_application (owner : Player) (event : graph.EventId)
    (view : app.EnvironmentView) (operation : EnvironmentCommand graph) :
    activateReady owner event view ≠ .application operation := by
  cases selected : ready owner event view <;> simp [activateReady, selected]

private theorem poll_not_application (owner : Player) (good wanted : Bool)
    (view : app.EnvironmentView) (operation : EnvironmentCommand graph) :
    pollCommand owner good wanted view ≠ .application operation := by
  by_cases equal : good = wanted
  · rw [pollCommand, ite_eq_left equal]
    exact ready_not_application owner (bindingEvent owner) view operation
  · simp [pollCommand, equal]

private theorem early_not_application (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (operation : EnvironmentCommand graph) :
    earlyCommand owner past view ≠ .application operation := by
  unfold earlyCommand
  split
  · intro impossible; cases impossible
  · split
    · intro impossible; cases impossible
    · exact pending_not_application _ view operation

private theorem late_not_application (owner : Player) (good : Bool) (clock : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (operation : EnvironmentCommand graph) :
    lateCommand owner good clock past view ≠ .application operation := by
  by_cases eligible : ready owner (bindingEvent owner) view ∧ (if good then 2 else 3) = clock
  · rw [lateCommand, ite_eq_left eligible]
    cases found : (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        past view).emissions.find? (fun emitted => emitted.1 = clock) with
    | none =>
        change (ReactiveApplication.Command.wait : app.Command) ≠ .application operation
        intro impossible
        cases impossible
    | some emitted =>
        change pendingCommand emitted.2.id view ≠ .application operation
        exact pending_not_application emitted.2.id view operation
  · rw [lateCommand, ite_eq_right eligible]
    intro impossible
    cases impossible

/-- Every application command through the original late inclusions is a clock
advance. There is no expiry or hidden sample in this actual prefix. -/
theorem original_helper_application_command (seed : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (operation : EnvironmentCommand graph) (lower : 5 ≤ position) (upper : position ≤ 23)
    (selected : originalCommand seed position past view = .application operation) :
    operation = .advanceClock := by
  interval_cases position
  · exact (poll_not_application _ _ _ view operation selected).elim
  · exact (poll_not_application _ _ _ view operation selected).elim
  · exact (poll_not_application _ _ _ view operation selected).elim
  · exact (early_not_application _ past view operation selected).elim
  · exact (early_not_application _ past view operation selected).elim
  · exact (early_not_application _ past view operation selected).elim
  · exact (poll_not_application _ _ _ view operation selected).elim
  · exact (poll_not_application _ _ _ view operation selected).elim
  · exact (poll_not_application _ _ _ view operation selected).elim
  · exact (late_not_application _ _ _ past view operation selected).elim
  · exact (late_not_application _ _ _ past view operation selected).elim
  · exact (late_not_application _ _ _ past view operation selected).elim
  · exact (ReactiveApplication.Command.application.inj selected).symm
  · exact (ready_not_application _ _ view operation selected).elim
  · exact (ready_not_application _ _ view operation selected).elim
  · exact (ready_not_application _ _ view operation selected).elim
  · exact (late_not_application _ _ _ past view operation selected).elim
  · exact (late_not_application _ _ _ past view operation selected).elim
  · exact (late_not_application _ _ _ past view operation selected).elim

/-- Genuine original traces supply the metadata for opaque native steps. -/
theorem original_helper_metadata (seed : Seeds) (remaining : Nat)
    (left right : app.Execution)
    (leftTrace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, left⟩))
    (rightTrace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, right⟩))
    (hidden : Player)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right)
    (leftOriginal : left.application.attempt = originalAttempt)
    (rightOriginal : right.application.attempt = originalAttempt) :
    left.application.phases = right.application.phases ∧
      left.application.generation = right.application.generation ∧
      left.application.retired.map (fun prior => (prior.attempt, prior.state.publicView)) =
        right.application.retired.map (fun prior => (prior.attempt, prior.state.publicView)) ∧
      (∀ phase ∈ left.application.phases.head?, phase.kind = .commitment) := by
  have leftPhases := original_phases (family seed) ⟨remaining, none, left⟩ leftTrace leftOriginal
  have rightPhases := original_phases (family seed) ⟨remaining, none, right⟩
    rightTrace rightOriginal
  have publicView : left.application.publicView = right.application.publicView :=
    congrArg (fun data => data.2.2.2.1.application) same
  refine ⟨leftPhases.trans rightPhases.symm, ?_, congrArg PhasePublicView.retired publicView, ?_⟩
  · exact congrArg (fun view => view.attempt.generation) publicView
  · intro phase member
    rw [leftPhases] at member
    have equal : commitmentPhase = phase := by simpa using member
    subst phase
    rfl

/-- Equal actual builder logs can replace the log field in the same external
readout without changing its native, traffic or player-input components. -/
theorem helper_external_append (hidden : Player) (left right : app.Execution)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right)
    (first second : List app.EnvironmentEntry) (equal : first = second) :
    phaseExternalObservation runtime leaks hidden { left with environmentRecall := first } =
      phaseExternalObservation runtime leaks hidden { right with environmentRecall := second } := by
  subst second
  exact congrArg (fun data =>
    (data.1, data.2.1, first, data.2.2.2.1, data.2.2.2.2)) same

end Vegas.Examples.CommitSeedBroadcast
