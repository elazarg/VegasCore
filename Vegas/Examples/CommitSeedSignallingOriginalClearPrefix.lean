/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingContract
import Vegas.Pending.PhaseCommitmentExclusionOrigin
import Vegas.Pending.PhaseSeedFreshness

/-! # The actual original prefix stays clear before its expiry commands -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem pending_not_expiry (identifier : MessageId Player) (view : app.EnvironmentView)
    (event : graph.EventId) :
    pendingCommand identifier view ≠ (.application (.expire event) : app.Command) := by
  unfold pendingCommand
  split <;> intro impossible <;> cases impossible

private theorem activate_not_expiry (owner : Player) (binding event : graph.EventId)
    (view : app.EnvironmentView) :
    activateReady owner binding view ≠ (.application (.expire event) : app.Command) := by
  unfold activateReady
  split <;> intro impossible <;> cases impossible

private theorem poll_not_expiry (owner : Player) (bit wanted : Bool)
    (view : app.EnvironmentView) (event : graph.EventId) :
    pollCommand owner bit wanted view ≠ (.application (.expire event) : app.Command) := by
  unfold pollCommand
  split
  · exact activate_not_expiry owner _ event view
  · intro impossible
    cases impossible

private theorem early_not_expiry (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (event : graph.EventId) :
    earlyCommand owner past view ≠ (.application (.expire event) : app.Command) := by
  unfold earlyCommand
  split
  · intro impossible; cases impossible
  · split
    · intro impossible; cases impossible
    · exact pending_not_expiry _ view event

private theorem late_not_expiry (owner : Player) (bit : Bool) (clock : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) (event : graph.EventId) :
    lateCommand owner bit clock past view ≠ (.application (.expire event) : app.Command) := by
  unfold lateCommand
  split
  · split
    · intro impossible; cases impossible
    · exact pending_not_expiry _ view event
  · intro impossible
    cases impossible

private theorem original_command_before_expiry (seed : Seeds) (position : Nat)
    (early : position < 20) (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (event : graph.EventId) :
    originalCommand seed position past view ≠ (.application (.expire event) : app.Command) := by
  have clockNotExpiry : (.application .advanceClock : app.Command) ≠
      .application (.expire event) := by
    intro impossible
    have same := ReactiveApplication.Command.application.inj impossible
    cases same
  interval_cases position
  · exact activate_not_expiry alice aliceBinding event view
  · exact activate_not_expiry bob bobBinding event view
  · exact clockNotExpiry
  · exact clockNotExpiry
  · exact poll_not_expiry alice _ false view event
  · exact early_not_expiry bob past view event
  · exact poll_not_expiry alice _ true view event
  · exact late_not_expiry alice _ 2 past view event
  · exact clockNotExpiry
  · exact activate_not_expiry alice aliceBinding event view
  · exact late_not_expiry alice _ 3 past view event
  · exact clockNotExpiry
  · exact poll_not_expiry bob _ false view event
  · exact early_not_expiry alice past view event
  · exact poll_not_expiry bob _ true view event
  · exact late_not_expiry bob _ 4 past view event
  · exact clockNotExpiry
  · exact activate_not_expiry bob bobBinding event view
  · exact late_not_expiry bob _ 5 past view event
  · exact clockNotExpiry

private theorem commitment_environment_keeps_clear (execution next : app.Execution)
    (installed : commitmentPhase ∈ execution.application.phases.head?)
    (command : app.Command)
    (noExpiry : ∀ event, command ≠ .application (.expire event))
    (moved : next ∈ (execution.environmentStep app command).support)
    (clear : execution.application.current.excluded = ∅) :
    next.application.current.excluded = ∅ := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact clear
  | activate owner =>
      obtain ⟨updated, sampled, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨_observed, _supported, rfl⟩ := PMF.support_map .. ▸ sampled
      exact clear
  | «include» identifier =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      change (execution.includePending app identifier).application.current.excluded = ∅
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup identifier with
      | none => simpa only [found] using clear
      | some message =>
          cases handled : app.handle execution.application message with
          | none => simpa only [found, handled, Option.getD_none] using clear
          | some state =>
              have same := PhaseRuntimeState.handle_commitment_phase_excluded runtime
                execution.application state commitmentPhase installed rfl message handled
              simpa only [found, handled, Option.getD_some] using same.trans clear
  | application operation =>
      obtain ⟨updated, stepped, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, selected, rfl⟩ := PMF.support_map .. ▸ stepped
      apply Finset.Subset.antisymm ?_ (Finset.empty_subset _)
      intro owner excluded
      have active : owner ∉ execution.application.current.excluded := by
        rw [clear]
        exact Finset.notMem_empty owner
      obtain ⟨event, _native, expiry, _inside, _request, _selected, _completed, _normalized⟩ :=
        PhaseRuntimeState.environment_new_exclusion_request runtime execution.application state
          commitmentPhase installed operation selected owner active excluded
      exact (noExpiry event (congrArg ReactiveApplication.Command.application expiry)).elim

/-- Every initialized raw prefix still in the original attempt is clear
before command twenty. Arbitrary preparations, malformed calls, evidence
requests and passive observation samples remain part of the actual trace. -/
theorem original_prefix_before_expiry_clear (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (early : current.execution.environmentRecall.length ≤ 20) :
    current.execution.application.current.excluded = ∅ := by
  have invariant : ∀ {state}
      (history : (app.protocol initial horizon (family seed)).Trace state),
      state.elim True (fun control => control.execution.application.attempt = originalAttempt →
        control.execution.environmentRecall.length ≤ 20 →
          control.execution.application.current.excluded = ∅) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint _legal reached induction =>
        change target ∈ (app.transition initial horizon (family seed) source joint).support
          at reached
        cases source with
        | none =>
            obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
            rw [initial_eq_pure] at supported
            cases (PMF.mem_support_pure_iff _ _).mp supported
            intro _original _early
            exact (PhaseRuntimeState.settle_physical plan.phases 0
              ⟨State.initial (encodeInputs (Env.empty (CellVal simpleExpr))), ∅⟩
              ⟨State.initial (encodeInputs (Env.empty (CellVal simpleExpr))), ∅⟩ []).1
        | some before =>
            obtain ⟨after, rfl, _kept⟩ := app.transition_recall_prefix initial horizon (family seed)
              before target joint reached
            intro afterOriginal afterEarly
            have ordered := (PhaseSeedFreshness.namespacePast_history runtime leaks plan
              (setup.initialLaw.map encodeInputs) horizon (family seed) before prior).ordered
            have progress := (phaseApplication_namespace_progress runtime leaks).transition
              initial horizon (family seed) before after joint reached ordered
            have beforeOriginal : before.execution.application.attempt = originalAttempt := by
              rw [afterOriginal] at progress
              cases address : before.execution.application.attempt with
              | mk phase generation =>
                  simp only [address, originalAttempt] at progress
                  have phases : phase = 0 := by omega
                  have generations : generation = 0 := by omega
                  simp only [phases, generations, originalAttempt]
            rcases before with ⟨remaining, actor, execution⟩
            cases actor with
            | some owner =>
                cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
                change (execution.respond app owner
                  ((joint owner).getD ⟨none⟩)).environmentRecall.length ≤ 20 at afterEarly
                have beforeEarly : execution.environmentRecall.length ≤ 20 := by
                  rwa [app.respond_environmentRecall] at afterEarly
                have clear := induction beforeOriginal beforeEarly
                change (execution.respond app owner
                  ((joint owner).getD ⟨none⟩)).application.current.excluded = ∅
                generalize _chosen : (joint owner).getD (⟨none⟩ : app.Action) = response
                rcases response with ⟨transmission⟩
                cases transmission <;> exact clear
            | none =>
                cases remaining with
                | zero =>
                    cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
                    exact induction beforeOriginal afterEarly
                | succ remaining =>
                    obtain ⟨command, selected, supported⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, moved, same⟩ := PMF.support_map .. ▸ supported
                    cases Option.some.inj same
                    change next.environmentRecall.length ≤ 20 at afterEarly
                    have length : next.environmentRecall.length =
                        execution.environmentRecall.length + 1 := by
                      rw [app.environmentStep_environmentRecall execution next command moved,
                        List.length_append, List.length_singleton]
                    have beforeEarly : execution.environmentRecall.length ≤ 20 := by omega
                    have position : execution.environmentRecall.length < 20 := by omega
                    have clear := induction beforeOriginal beforeEarly
                    have phases := original_phases (family seed)
                      ⟨remaining + 1, none, execution⟩ prior beforeOriginal
                    have installed : commitmentPhase ∈ execution.application.phases.head? := by
                      rw [phases]
                      rfl
                    have commandEq : command = originalCommand seed
                        execution.environmentRecall.length execution.environmentRecall
                          (execution.observeEnvironment app) := by
                      rw [family_apply, choose_original seed _ _ beforeOriginal] at selected
                      exact (PMF.mem_support_pure_iff _ _).mp selected
                    exact commitment_environment_keeps_clear execution next installed command
                      (fun event => commandEq ▸ original_command_before_expiry seed _ position
                        execution.environmentRecall (execution.observeEnvironment app) event)
                      moved clear
  exact invariant trace original early

end Vegas.Examples.CommitSeedSignalling
