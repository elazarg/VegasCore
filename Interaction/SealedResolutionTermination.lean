/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionRounds
import Interaction.SealedResolutionProgress

/-! # Completion under the resolving runtime's clock

Round execution retains the actual native policies and wire traffic. Its clock
boundary is mandatory. Termination through defaults is distinct from service
of honest messages before their deadlines.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

private theorem runPolicies_public_invariant (runtime : SealedResolution Principal Value)
    (invariant : PublicState Principal Value → Prop)
    (hrecord : ∀ state event, invariant state →
      invariant { state with events := state.events ++ [event] })
    (hrefresh : ∀ resolve state, invariant state → invariant (runtime.refresh resolve state))
    (hclock : ∀ state, invariant state → invariant { state with clock := state.clock + 1 })
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : invariant execution.native.application.visible)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) : invariant next.native.application.visible := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (fun state => invariant state.visible) ?_ ?_ ?_ players environment schedule execution next
    hinitial hnext
  · intro state who command hstate
    exact hstate
  · intro state message final hstate hfinal
    change runtime.handle state message = some final at hfinal
    unfold handle at hfinal
    cases hvalid : runtime.validateMessage? state message with
    | none => simp only [hvalid, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hfinal
    | some event =>
        simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hfinal
        subst final
        exact hrefresh false _ (hrecord state.visible event hstate)
  · intro state command final hstate hfinal
    change final ∈ (FinDist.pure (runtime.tick state)).support at hfinal
    rw [FinDist.mem_support_pure] at hfinal
    subst final
    exact hrefresh true _ (hclock state.visible hstate)

private theorem round_public_invariant (runtime : SealedResolution Principal Value)
    (invariant : PublicState Principal Value → Prop)
    (hrecord : ∀ state event, invariant state →
      invariant { state with events := state.events ++ [event] })
    (hrefresh : ∀ resolve state, invariant state → invariant (runtime.refresh resolve state))
    (hclock : ∀ state, invariant state → invariant { state with clock := state.clock + 1 })
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : invariant execution.native.application.visible)
    (hnext : next ∈ (runtime.round principals serviceSlots players environment execution).support) :
    invariant next.native.application.visible := by
  simp only [round, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hmiddleInvariant := runtime.runPolicies_public_invariant invariant hrecord hrefresh hclock
    players (runtime.messageApplication.wireEnvironment environment) _ execution middle
    hinitial hmiddle
  rw [runtime.clockStep_native middle next hnext]
  exact hrefresh true _ (hclock _ hmiddleInvariant)

private theorem runRounds_public_invariant (runtime : SealedResolution Principal Value)
    (invariant : PublicState Principal Value → Prop)
    (hrecord : ∀ state event, invariant state →
      invariant { state with events := state.events ++ [event] })
    (hrefresh : ∀ resolve state, invariant state → invariant (runtime.refresh resolve state))
    (hclock : ∀ state, invariant state → invariant { state with clock := state.clock + 1 })
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : invariant execution.native.application.visible)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment
      count execution).support) : invariant next.native.application.visible := by
  induction count generalizing execution with
  | zero =>
      simp only [runRounds, FinDist.mem_support_pure] at hnext
      subst next
      exact hinitial
  | succ count ih =>
      simp only [runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hinitial
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        exact ih middle (runtime.round_public_invariant invariant hrecord hrefresh hclock
          principals serviceSlots players environment execution middle hinitial hmiddle) hnext

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem record_completed (state : PublicState Principal Value)
    (event : SealedProgram.Event Principal Value) (node : Nat)
    (hcompleted : state.completed node = true) :
    ({ state with events := state.events ++ [event] }).completed node = true := by
  simp only [PublicState.completed, SealedProgram.done, List.any_append, Bool.or_eq_true]
    at hcompleted ⊢
  exact hcompleted.elim (fun h => Or.inl (Or.inl h)) Or.inr

/-- Completion of a node persists through arbitrary subsequent traffic and rounds. -/
theorem runRounds_completed (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution) (node : Nat)
    (hinitial : execution.native.application.visible.completed node = true)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment
      count execution).support) : next.native.application.visible.completed node = true := by
  apply runtime.runRounds_public_invariant (fun state => state.completed node = true)
    (fun state event hstate => record_completed state event node hstate)
    (fun resolve state hstate => runtime.refresh_completed resolve state node hstate)
    (fun _ hstate => hstate) principals serviceSlots players environment count execution next
    hinitial hnext

/-- First-readiness timestamps cannot be postponed by traffic or clock ticks. -/
theorem runRounds_firstReady?_of_some (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (node timestamp : Nat)
    (hinitial : execution.native.application.visible.firstReady? node = some timestamp)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment
      count execution).support) :
    next.native.application.visible.firstReady? node = some timestamp := by
  apply runtime.runRounds_public_invariant (fun state => state.firstReady? node = some timestamp)
    (fun _ _ hstate => hstate)
    (fun resolve state hstate => runtime.refresh_firstReady?_of_some resolve state node timestamp
      hstate)
    (fun _ hstate => hstate) principals serviceSlots players environment count execution next
    hinitial hnext

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem clockBounded_advance (state : PublicState Principal Value)
    (hstate : state.ClockBounded) :
    ({ state with clock := state.clock + 1 }).ClockBounded := by
  intro node timestamp hready
  exact Nat.le_trans (hstate node timestamp hready) (Nat.le_succ state.clock)

/-- Reachable readiness timestamps never lie in the future. -/
theorem runRounds_clockBounded (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : execution.native.application.visible.ClockBounded)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment
      count execution).support) : next.native.application.visible.ClockBounded := by
  apply runtime.runRounds_public_invariant PublicState.ClockBounded
    (fun _ _ hstate => hstate) (fun resolve _ hstate => hstate.refresh resolve)
    clockBounded_advance principals serviceSlots players environment count execution next
    hinitial hnext

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem complete_node (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (node : Nat)
    (hcomplete : runtime.complete state = true) (hnode : node < runtime.program.rules.length) :
    state.completed node = true :=
  List.all_eq_true.mp hcomplete node (List.mem_range.mpr hnode)

private theorem round_requires (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (execution next : runtime.messageApplication.PolicyExecution) (requires : List Nat)
    (hinitial : requires.all execution.native.application.visible.completed = true)
    (hnext : next ∈ (runtime.round principals serviceSlots players environment execution).support) :
    requires.all next.native.application.visible.completed = true := by
  apply List.all_eq_true.mpr
  intro node hnode
  exact runtime.round_public_invariant (fun state => state.completed node = true)
    (fun state event hstate => record_completed state event node hstate)
    (fun resolve state hstate => runtime.refresh_completed resolve state node hstate)
    (fun _ hstate => hstate) principals serviceSlots players environment execution next
    (List.all_eq_true.mp hinitial node hnode) hnext

private theorem round_progress (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (execution next : runtime.messageApplication.PolicyExecution) (node : Nat)
    (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule) (hkind : rule.kind ≠ .disabled)
    (hrequires : rule.requires.all execution.native.application.visible.completed = true)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnode : node < runtime.program.rules.length)
    (hnext : next ∈ (runtime.round principals serviceSlots players environment execution).support) :
    next.native.application.visible.completed node = true ∨
      ∃ timestamp, next.native.application.visible.firstReady? node = some timestamp ∧
        timestamp ≤ next.native.application.visible.clock ∧
        next.native.application.visible.clock < timestamp + runtime.window := by
  simp only [round, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hmiddleBounded := runtime.runPolicies_public_invariant PublicState.ClockBounded
    (fun _ _ hstate => hstate) (fun resolve _ hstate => hstate.refresh resolve)
    clockBounded_advance players (runtime.messageApplication.wireEnvironment environment)
    _ execution middle hbounded hmiddle
  have hmiddleRequires : rule.requires.all middle.native.application.visible.completed = true := by
    apply List.all_eq_true.mpr
    intro prerequisite hprerequisite
    exact runtime.runPolicies_public_invariant
      (fun state => state.completed prerequisite = true)
      (fun state event hstate => record_completed state event prerequisite hstate)
      (fun resolve state hstate => runtime.refresh_completed resolve state prerequisite hstate)
      (fun _ hstate => hstate) players (runtime.messageApplication.wireEnvironment environment)
      _ execution middle (List.all_eq_true.mp hrequires prerequisite hprerequisite) hmiddle
  rw [runtime.clockStep_native middle next hnext]
  exact runtime.refresh_progress _ node rule hrule hkind hmiddleRequires
    (clockBounded_advance _ hmiddleBounded) hnode

private theorem runRounds_ready_progress (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution) (node : Nat)
    (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule) (hkind : rule.kind ≠ .disabled)
    (hrequires : rule.requires.all execution.native.application.visible.completed = true)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnode : node < runtime.program.rules.length) (hcount : 0 < count)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment
      count execution).support) :
    next.native.application.visible.completed node = true ∨
      ∃ timestamp, next.native.application.visible.firstReady? node = some timestamp ∧
        timestamp ≤ next.native.application.visible.clock ∧
        next.native.application.visible.clock < timestamp + runtime.window := by
  induction count generalizing execution with
  | zero => omega
  | succ count ih =>
      simp only [runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact Or.inl (runtime.complete_node execution.native.application.visible node ‹_› hnode)
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        cases count with
        | zero =>
            simp only [runRounds, FinDist.mem_support_pure] at hnext
            subst next
            exact runtime.round_progress principals serviceSlots players environment execution
              middle node rule hrule hkind hrequires hbounded hnode hmiddle
        | succ count =>
            exact ih middle
              (runtime.round_requires principals serviceSlots players environment execution middle
                rule.requires hrequires hmiddle)
              (runtime.round_public_invariant PublicState.ClockBounded
                (fun _ _ hstate => hstate) (fun resolve _ hstate => hstate.refresh resolve)
                clockBounded_advance principals serviceSlots players environment execution middle
                hbounded hmiddle) (by omega) hnext

/-- A ready enabled node completes within one timeout window plus its first
round boundary. This permits arbitrary randomized policies and even zero wire
service: completion may be a timeout, not delivery of a valid message. -/
theorem runRounds_ready_complete (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (execution next : runtime.messageApplication.PolicyExecution) (node : Nat)
    (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule) (hkind : rule.kind ≠ .disabled)
    (hrequires : rule.requires.all execution.native.application.visible.completed = true)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnode : node < runtime.program.rules.length)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment
      (runtime.window + 1) execution).support) :
    next.native.application.visible.completed node = true := by
  have hprogress := runtime.runRounds_ready_progress principals serviceSlots players environment
    (runtime.window + 1) execution next node rule hrule hkind hrequires hbounded hnode
    (by omega) hnext
  rcases hprogress with hcomplete | ⟨finalTime, hfinalTime, _, hfinalUnexpired⟩
  · exact hcomplete
  by_contra hnotComplete
  have hincomplete : runtime.complete next.native.application.visible = false := by
    apply Bool.eq_false_of_not_eq_true
    exact fun h => hnotComplete (runtime.complete_node _ node h hnode)
  simp only [runRounds] at hnext
  split at hnext
  · simp only [FinDist.mem_support_pure] at hnext
    subst next
    exact hnotComplete (runtime.complete_node _ node ‹_› hnode)
  · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
    obtain ⟨middle, hmiddle, hnext⟩ := hnext
    rcases runtime.round_progress principals serviceSlots players environment execution middle
        node rule hrule hkind hrequires hbounded hnode hmiddle with
      hcomplete | ⟨timestamp, htimestamp, htimeBounded, _⟩
    · exact hnotComplete (runtime.runRounds_completed principals serviceSlots players environment
        runtime.window middle next node hcomplete hnext)
    · have hpersist := runtime.runRounds_firstReady?_of_some principals serviceSlots players
        environment runtime.window middle next node timestamp htimestamp hnext
      have hclock := runtime.runRounds_clock_of_incomplete principals serviceSlots players
        environment runtime.window middle next hnext hincomplete
      rw [hfinalTime] at hpersist
      have htime := Option.some.inj hpersist
      omega

private theorem runRounds_prefix_completed (runtime : SealedResolution Principal Value)
    (henabled : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule → rule.kind ≠ .disabled)
    (hbackward : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (hcount : count ≤ runtime.program.rules.length)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment
      (count * (runtime.window + 1)) execution).support) :
    ∀ node < count, next.native.application.visible.completed node = true := by
  induction count generalizing next with
  | zero => intro node hnode; omega
  | succ count ih =>
      rw [Nat.succ_mul, runtime.runRounds_add] at hnext
      simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hprefix := ih middle (by omega) hmiddle
      intro node hnode
      by_cases hprior : node < count
      · exact runtime.runRounds_completed principals serviceSlots players environment
          (runtime.window + 1) middle next node (hprefix node hprior) hnext
      · have hnodeEq : node = count := by omega
        subst node
        have hindex : count < runtime.program.rules.length := by omega
        let rule := runtime.program.rules[count]
        have hrule : runtime.program.rules[count]? = some rule :=
          List.getElem?_eq_getElem hindex
        apply runtime.runRounds_ready_complete principals serviceSlots players environment
          middle next count rule hrule (henabled count rule hrule) ?_ ?_ hindex hnext
        · apply List.all_eq_true.mpr
          intro prerequisite hprerequisite
          exact hprefix prerequisite (hbackward count rule hrule prerequisite hprerequisite)
        · exact runtime.runRounds_clockBounded principals serviceSlots players environment
            (count * (runtime.window + 1)) execution middle hbounded hmiddle

/-- Every enabled backward-dependency program completes within

`number of rules * (timeout window + 1)` rounds.

No roster coverage or message-service premise is required: the mandatory
clock may complete nodes by timeout. This theorem establishes termination,
not honest success, source settlement, or an incentive bound. -/
theorem runRounds_complete (runtime : SealedResolution Principal Value)
    (henabled : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule → rule.kind ≠ .disabled)
    (hbackward : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (execution next : runtime.messageApplication.PolicyExecution)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment
      (runtime.program.rules.length * (runtime.window + 1)) execution).support) :
    runtime.complete next.native.application.visible = true := by
  apply List.all_eq_true.mpr
  intro node hnode
  exact runtime.runRounds_prefix_completed henabled hbackward principals serviceSlots players
    environment runtime.program.rules.length execution next (Nat.le_refl _) hbounded hnext
    node (List.mem_range.mp hnode)

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runRounds_complete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runRounds_complete
