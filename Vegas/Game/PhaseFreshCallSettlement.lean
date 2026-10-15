/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceProjection
import Vegas.Game.SourceFreshCallDeadline

/-! # Protected fresh calls on actual clear physical histories -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "R" => serviceRuntime setup mode deadline
local notation "P" => phaseApplication R leaks
local notation "NL" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "N" => serviceApplication setup mode deadline NL
local notation "I" => setup.initialLaw.map setup.eventInputs

omit [Fintype Player] in
private theorem settlement_transition
    (horizon : Nat) (scheduler : (N).Scheduler)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (bound : (serviceGraph setup mode).EventId → Nat)
    {before after : (N).ProtocolState}
    (prior : ((N).protocol (serviceInitialLaw setup mode) horizon scheduler).Trace before)
    (valid : ReactiveApplication.serviceInvariant (SettlesFreshCalls setup NL owner event bound)
      before)
    (included : ReactiveApplication.serviceInvariant
      (ProtectedInclusionAt R NL · bound) before)
    (joint : Player → Option (N).Action)
    (reached : after ∈ ((N).transition (serviceInitialLaw setup mode) horizon scheduler before
      joint).support) :
    ReactiveApplication.serviceInvariant (SettlesFreshCalls setup NL owner event bound) after := by
  cases before with
  | none =>
      obtain ⟨initial, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      intro earlier entry later message split
      simp [ReactiveApplication.Execution.initial] at split
  | some current =>
      rcases current with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact settlesFreshCalls_respond setup NL owner event bound execution
            (legalFacts setup NL horizon scheduler _ prior) who _ valid
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
          | succ remaining =>
              obtain ⟨chosen, _selected, moved⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              exact settlesFreshCalls_environment setup NL owner event owned remaining execution
                included prior valid chosen next supported

/-- Actual clear physical prefixes inherit settlement of every original
acceptable sole fresh call. The physical service contract is restricted at each
actual prefix; no global reconstructed-native contract is assumed. -/
theorem phase_settlesFreshCalls_history
    (bounds : MessageBounds (serviceGraph setup mode))
    (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (P).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (inclusion : PhaseService.ProtectedInclusion R leaks
      ((I).map (PhaseRuntimeState.initial plan)) horizon scheduler bound)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner) :
    ∀ {state} (_trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol
      ((I).map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state),
      (∀ current, state = some current → current.execution.application.current.excluded = ∅) →
      ReactiveApplication.serviceInvariant (SettlesFreshCalls setup NL owner event bound)
        (PhaseNativeProjection.protocolState R leaks plan state) := by
  have initialEq : (I).map (State.initial (graph := serviceGraph setup mode)) =
      serviceInitialLaw setup mode := by
    rw [PMF.map_comp]
    rfl
  intro state trace
  induction trace with
  | start => intro _clear; trivial
  | @extend before after prior joint legal realized ih =>
      intro clear
      have rawRealized : after ∈ ((P).transition ((I).map (PhaseRuntimeState.initial plan)) horizon
          scheduler before joint).support := realized
      have beforeClear : ∀ current, before = some current →
          current.execution.application.current.excluded = ∅ := by
        intro current same
        subst before
        obtain ⟨next, rfl, _recalled⟩ := (P).transition_recall_prefix _ horizon scheduler current
          after joint rawRealized
        have monotone := (phaseApplication_exclusion_monotone R leaks).transition _ horizon
          scheduler current next joint rawRealized
        exact Finset.subset_empty.mp (clear next rfl ▸ monotone)
      have nativePrior := PhaseNativeProjection.nativeTrace R leaks plan bounds ordered maximal I
        horizon scheduler prior beforeClear
      rw [initialEq] at nativePrior
      have nativeMoved := PhaseNativeProjection.transition_support_of_clear R leaks plan bounds
        ordered maximal I horizon scheduler prior joint legal realized clear
      rw [initialEq] at nativeMoved
      have included : ReactiveApplication.serviceInvariant (ProtectedInclusionAt R NL · bound)
          (PhaseNativeProjection.protocolState R leaks plan before) := by
        cases before with
        | none => trivial
        | some current =>
            exact PhaseNativeProjection.protectedInclusion_projection R leaks plan bounds ordered
              maximal I horizon scheduler bound inclusion prior (beforeClear current rfl)
      exact settlement_transition setup mode deadline leaks plan horizon
        (PhaseNativeProjection.nativeScheduler R leaks plan scheduler) owner event owned bound
        nativePrior (ih beforeClear) included
        (PhaseNativeProjection.jointActions R leaks plan joint)
        nativeMoved

/-- A still-ready original fresh call cannot reach its deadline along an
actual clear physical history satisfying the original physical inclusion
contract. Its settlement invariant is derived from that same history. -/
theorem phase_freshCall_within_deadline_of_ready
    (bounds : MessageBounds (serviceGraph setup mode))
    (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (P).Scheduler) (control : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol
      ((I).map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (inclusion : PhaseService.ProtectedInclusion R leaks
      ((I).map (PhaseRuntimeState.initial plan)) horizon scheduler bound)
    (earlier later : List (N).PlayerEntry) (entry : (N).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (recorded : (PhaseNativeProjection.execution R leaks plan control.execution).recall owner =
      earlier ++ entry :: later)
    (call : FreshCall setup NL owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later, ¬ EmitsOtherFor R NL other event message.id)
    (ready : control.execution.application.current.native.config.cut.Ready event) :
    control.execution.application.current.native.WithinDeadline R event := by
  have nativePrior := PhaseNativeProjection.nativeTrace R leaks plan bounds ordered maximal I
    horizon scheduler trace (fun _ same => by cases same; exact clear)
  have initialEq : (I).map (State.initial (graph := serviceGraph setup mode)) =
      serviceInitialLaw setup mode := by
    rw [PMF.map_comp]
    rfl
  rw [initialEq] at nativePrior
  have facts := legalFacts setup NL horizon
    (PhaseNativeProjection.nativeScheduler R leaks plan scheduler) _ nativePrior
  have settles := phase_settlesFreshCalls_history setup mode deadline leaks plan bounds ordered
    maximal horizon scheduler bound inclusion owner event owned trace
      (fun _ same => by cases same; exact clear)
  have included := PhaseNativeProjection.protectedInclusion_projection R leaks plan bounds ordered
    maximal I horizon scheduler bound inclusion trace clear
  have member : entry ∈ (PhaseNativeProjection.execution R leaks plan control.execution).recall
      owner := by
    rw [recorded]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨entered, activated, fitting⟩ := call.fits.exists
  obtain ⟨_extra, _order, _together, keeps, _accepted⟩ :=
    facts.eventStable owner entry member event call.ready ready.1
  have stamp := keeps owner owned entered activated
  change control.execution.application.current.native.activatedAt event = some entered at stamp
  by_contra due
  simp only [EventGraphRuntime.State.WithinDeadline, stamp] at due
  have passed : entry.beforeView.application.publicView.clock + bound event <
      control.execution.application.current.native.clock := by omega
  obtain ⟨accepted, receipt⟩ := included event owner owned earlier later entry message recorded
    call.emitted call.authored call.addressed call.ready sole ready.1 passed
  have settled := settles earlier entry later message recorded call sole
  exact ready.1 (settled.2.2 (settled.2.1 accepted receipt))

end Vegas
