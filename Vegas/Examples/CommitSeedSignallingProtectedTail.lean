/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingTail
import Interaction.ReactiveAllocation
import Interaction.ReactiveReceipts

/-! # Exact protected receipt turns after actual continuation callbacks -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem pending_not_activation (identifier : MessageId Player)
    (view : app.EnvironmentView) (owner : Player) :
    pendingCommand identifier view ≠ .activate owner := by
  unfold pendingCommand
  split <;> intro impossible <;> cases impossible

private theorem response_not_activation (source : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (owner : Player) :
    responseCommand source past view ≠ .activate owner := by
  unfold responseCommand
  split
  · intro impossible
    cases impossible
  · split
    · exact pending_not_activation _ _ _
    · intro impossible
      cases impossible

theorem retry_activation (position : Nat) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (owner : Player)
    (selected : retryCommand position past view = .activate owner) :
    position = 0 ∧ survivor view = owner := by
  match position with
  | 0 =>
      change activateReady (survivor view) (bindingEvent (survivor view)) view =
        .activate owner at selected
      unfold activateReady at selected
      split at selected
      · cases selected
        exact ⟨rfl, rfl⟩
      · cases selected
  | 1 => exact (response_not_activation _ _ _ _ selected).elim
  | 2 | 3 | 4 | 5 | 6 | 7 | 8 => cases selected
  | position + 9 => cases selected

theorem reveal_activation (position : Nat) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (owner : Player)
    (selected : revealCommand position past view = .activate owner) :
    (position = 0 ∧ owner = alice) ∨ (position = 2 ∧ owner = bob) := by
  match position with
  | 0 =>
      change activateReady alice aliceReveal view = .activate owner at selected
      unfold activateReady at selected
      split at selected
      · cases selected
        exact Or.inl ⟨rfl, rfl⟩
      · cases selected
  | 1 => exact (response_not_activation _ _ _ _ selected).elim
  | 2 =>
      change activateReady bob bobReveal view = .activate owner at selected
      unfold activateReady at selected
      split at selected
      · cases selected
        exact Or.inr ⟨rfl, rfl⟩
      · cases selected
  | 3 => exact (response_not_activation _ _ _ _ selected).elim
  | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => cases selected
  | position + 12 => cases selected

private theorem response_next_choice (seeds : Seeds) (before observed : app.Execution)
    (owner : Player) (action : app.Action)
    (retired : before.application.attempt ≠ originalAttempt)
    (selected : choose seeds before.environmentRecall (before.observeEnvironment app) =
      .activate owner)
    (moved : observed ∈ (before.environmentStep app (.activate owner)).support) :
    choose seeds (observed.respond app owner action).environmentRecall
        ((observed.respond app owner action).observeEnvironment app) =
      responseCommand owner (observed.respond app owner action).environmentRecall
        ((observed.respond app owner action).observeEnvironment app) := by
  have application : observed.application = before.application := by
    unfold ReactiveApplication.Execution.environmentStep at moved
    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
    obtain ⟨seen, _support, rfl⟩ := PMF.support_map .. ▸ supported
    rfl
  have same : observed.application.attempt = before.application.attempt :=
    congrArg PhaseRuntimeState.attempt application
  have nextIndex := tailIndex_after_same_attempt before observed (.activate owner) moved same
  have respondedAttempt : (observed.respond app owner action).application.attempt =
      observed.application.attempt := by
    rcases action with ⟨transmission⟩
    cases transmission <;> rfl
  have respondedPhases : (observed.respond app owner action).application.phases =
      observed.application.phases := by
    rcases action with ⟨transmission⟩
    cases transmission <;> rfl
  have afterIndex : tailIndex (observed.respond app owner action).environmentRecall
      ((observed.respond app owner action).observeEnvironment app) =
      tailIndex before.environmentRecall (before.observeEnvironment app) + 1 := by
    rw [app.respond_environmentRecall]
    rw [tailIndex_congr_attempt _ _ (observed.observeEnvironment app) respondedAttempt]
    exact nextIndex
  have retiredView : (before.observeEnvironment app).application.attempt ≠ originalAttempt :=
    retired
  have afterRetired :
      ((observed.respond app owner action).observeEnvironment app).application.attempt ≠
        originalAttempt := by
    change (observed.respond app owner action).application.attempt ≠ originalAttempt
    rw [respondedAttempt, same]
    exact retired
  have phaseEq : ((observed.respond app owner action).observeEnvironment app).application.phase =
      (before.observeEnvironment app).application.phase := by
    change (observed.respond app owner action).application.phases.head?.map
      (fun phase => (phase.kind, phase.low, phase.high)) =
        before.application.phases.head?.map (fun phase => (phase.kind, phase.low, phase.high))
    rw [respondedPhases, application]
  rw [choose, ite_eq_right retiredView] at selected
  rw [choose, ite_eq_right afterRetired, phaseEq, afterIndex]
  cases phaseEq : (before.observeEnvironment app).application.phase with
  | none => rw [phaseEq] at selected; cases selected
  | some triple =>
      rcases triple with ⟨kind, low, high⟩
      rw [phaseEq] at selected
      cases kind with
      | sample => cases selected
      | commitment =>
          obtain ⟨index, sameOwner⟩ := retry_activation _ _ _ _ selected
          rw [index]
          change responseCommand
              (survivor ((observed.respond app owner action).observeEnvironment app))
              (observed.respond app owner action).environmentRecall
              ((observed.respond app owner action).observeEnvironment app) = _
          have excluded : (observed.respond app owner action).application.current.excluded =
              observed.application.current.excluded := by
            rcases action with ⟨transmission⟩
            cases transmission <;> rfl
          have afterSurvivor :
              survivor ((observed.respond app owner action).observeEnvironment app) = owner := by
            unfold survivor
            change (if alice ∈ (observed.respond app owner action).application.current.excluded
              then bob else alice) = owner
            rw [excluded, application]
            exact sameOwner
          rw [afterSurvivor]
      | reveal =>
          rcases reveal_activation _ _ _ _ selected with ⟨index, rfl⟩ | ⟨index, rfl⟩
          · rw [index]
            rfl
          · rw [index]
            rfl

/-- A genuine tail callback is followed by the exact response selector.
The response may be an arbitrary raw declaration or a silent action. -/
theorem tail_response_command (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => ∀ owner, current.actor = some owner →
        current.execution.application.attempt ≠ originalAttempt → ∀ action : app.Action,
        choose seeds (current.execution.respond app owner action).environmentRecall
            ((current.execution.respond app owner action).observeEnvironment app) =
          responseCommand owner (current.execution.respond app owner action).environmentRecall
            ((current.execution.respond app owner action).observeEnvironment app) ∧
        ∃ past view, current.execution.environmentRecall = past ++ [⟨view, .activate owner⟩] ∧
          view.network.nextSerial owner = current.execution.network.nextSerial owner) := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached _ih =>
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, _supported, rfl⟩ := PMF.support_map .. ▸ reached
          intro owner active
          cases active
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          cases active with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              intro owner active
              cases active
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨observed, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro owner active retired action
                  have commandEq : command = .activate owner := by
                    cases command with
                    | activate who =>
                        change some who = some owner at active
                        exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
                    | «include» identifier => cases active
                    | wait => cases active
                    | application command => cases active
                  have appEq : observed.application = execution.application := by
                    rw [commandEq] at supported
                    unfold ReactiveApplication.Execution.environmentStep at supported
                    obtain ⟨next, learned, rfl⟩ := PMF.support_map .. ▸ supported
                    obtain ⟨seen, _support, rfl⟩ := PMF.support_map .. ▸ learned
                    rfl
                  have retiredBefore : execution.application.attempt ≠ originalAttempt := by
                    rw [← appEq]
                    exact retired
                  have chosen : choose seeds execution.environmentRecall
                      (execution.observeEnvironment app) = .activate owner := by
                    change command ∈ (family seeds execution.environmentRecall
                      (execution.observeEnvironment app)).support at selected
                    rw [family_apply, PMF.mem_support_pure_iff] at selected
                    exact selected.symm.trans commandEq
                  refine ⟨response_next_choice seeds execution observed owner action retiredBefore
                    chosen (commandEq ▸ supported), execution.environmentRecall,
                    execution.observeEnvironment app, ?_, ?_⟩
                  · exact app.environmentStep_environmentRecall execution observed (.activate owner)
                      (commandEq ▸ supported)
                  · change execution.network.nextSerial owner = observed.network.nextSerial owner
                    have unchanged := app.environmentStep_nextSerial execution observed command
                      supported
                    exact congrFun unchanged.symm owner

/-- The actual next scheduler decision receipts a tail submission, even if
its native call is malformed, stale or rejected. -/
theorem tail_submission_receipt (seeds : Seeds) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (submission : app.Submission)
    (trace : (app.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt) (next : app.Execution)
    (reached : next ∈ ((execution.respond app owner ⟨some submission⟩).environmentStep app
      (choose seeds (execution.respond app owner ⟨some submission⟩).environmentRecall
        ((execution.respond app owner ⟨some submission⟩).observeEnvironment app))).support) :
    ∃ accepted, ((owner, execution.network.nextSerial owner), accepted) ∈ next.receipts := by
  obtain ⟨chosen, past, view, recalled, serial⟩ :=
    tail_response_command seeds trace owner rfl retired ⟨some submission⟩
  rw [chosen, app.respond_environmentRecall, recalled,
    responseCommand_transmission execution owner past ⟨view, .activate owner⟩ rfl serial submission]
    at reached
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  have serials := app.serialsBeforeNext_history (family seeds) initial horizon trace
  have lookup := serials.lookup_submit owner
    (app.packet (app.submit execution.application owner submission) owner
      (execution.network.known owner) submission)
  change (execution.respond app owner ⟨some submission⟩).network.lookup
    (owner, execution.network.nextSerial owner) = some _ at lookup
  unfold ReactiveApplication.Execution.includePending
  simp only [MessageNetwork.includePending, lookup]
  exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩

end Vegas.Examples.CommitSeedSignalling
