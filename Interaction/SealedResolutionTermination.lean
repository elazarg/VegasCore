/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionRounds
import Interaction.SealedResolutionProgress

/-! # Completion under the resolving runtime's clock

Round execution retains the actual native policies and wire traffic. Its clock
boundary is mandatory. The proof applies to every hosted commitment service
whose handler records a public event and refreshes readiness. Private preparation
and catalog updates are unrestricted. Termination through defaults is distinct
from service of honest messages before their deadlines.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal]
variable {Service : Type (max uPrincipal uValue)}
variable {prepare : Service → Principal → Nat → Value → Service}
variable {applyMessage : ApplicationState Principal Value Service →
  Message Principal (SealedProgram.Payload Principal Value) →
  Option (ApplicationState Principal Value Service)}

private theorem runPolicies_public_invariant (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (invariant : PublicState Principal Value → Prop)
    (hrecord : ∀ state event, invariant state →
      invariant { state with events := state.events ++ [event] })
    (hrefresh : ∀ resolve state, invariant state → invariant (runtime.refresh resolve state))
    (hclock : ∀ state, invariant state → invariant { state with clock := state.clock + 1 })
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hinitial : invariant execution.native.application.visible)
    (hnext : next ∈ ((runtime.host prepare applyMessage).runPolicies players environment
      schedule execution).support) : invariant next.native.application.visible := by
  apply (runtime.host prepare applyMessage).runPolicies_application_invariant
    (fun state => invariant state.visible) ?_ ?_ ?_ players environment schedule execution next
    hinitial hnext
  · intro state who command hstate
    exact hstate
  · intro state message final hstate hfinal
    obtain ⟨event, hvisible⟩ := hhandler state message final hfinal
    rw [hvisible]
    exact hrefresh false _ (hrecord state.visible event hstate)
  · intro state command final hstate hfinal
    change final ∈ (FinDist.pure (runtime.tick state)).support at hfinal
    rw [FinDist.mem_support_pure] at hfinal
    subst final
    exact hrefresh true _ (hclock state.visible hstate)

private theorem host_clockStep_native (runtime : SealedResolution Principal Value)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hnext : next ∈ ((runtime.host prepare applyMessage).environmentPolicyStep execution
      (.application ⟨()⟩)).support) :
    next.native =
      { execution.native with application := runtime.tick execution.native.application } := by
  have hnative : next.native ∈
      (((runtime.host prepare applyMessage).environmentPolicyStep execution
        (.application ⟨()⟩)).map MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  simpa only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    host, FinDist.map_pure, FinDist.mem_support_pure] using hnative

private theorem round_clock_ge (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).round
      principals serviceSlots players environment execution).support) :
    execution.native.application.visible.clock + 1 ≤ next.native.application.visible.clock := by
  simp only [MessageApplication.RoundDriver.round, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hclock := runtime.runPolicies_public_invariant hhandler
    (fun state => execution.native.application.visible.clock ≤ state.clock)
    (fun _ _ h => h)
    (fun resolve state h => by rw [runtime.refresh_clock]; exact h)
    (fun state h => Nat.le_trans h (Nat.le_succ state.clock))
    players ((runtime.host prepare applyMessage).wireEnvironment environment)
    _ execution middle (Nat.le_refl _) hmiddle
  rw [runtime.host_clockStep_native middle next hnext]
  change execution.native.application.visible.clock + 1 ≤
    (runtime.refresh true { middle.native.application.visible with
      clock := middle.native.application.visible.clock + 1 }).clock
  rw [runtime.refresh_clock]
  exact Nat.succ_le_succ hclock

private theorem runRounds_clock_ge_of_incomplete (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (count : Nat) (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).runRounds
      principals serviceSlots players environment count execution).support)
    (hincomplete : runtime.complete next.native.application.visible = false) :
    execution.native.application.visible.clock + count ≤ next.native.application.visible.clock := by
  induction count generalizing execution with
  | zero =>
      simp only [MessageApplication.RoundDriver.runRounds, FinDist.mem_support_pure] at hnext
      subst next
      omega
  | succ count ih =>
      simp only [MessageApplication.RoundDriver.runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        simp_all
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        have htail := ih middle hnext
        have hround := runtime.round_clock_ge hhandler principals serviceSlots
          players environment execution middle hmiddle
        omega

private theorem round_public_invariant (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (invariant : PublicState Principal Value → Prop)
    (hrecord : ∀ state event, invariant state →
      invariant { state with events := state.events ++ [event] })
    (hrefresh : ∀ resolve state, invariant state → invariant (runtime.refresh resolve state))
    (hclock : ∀ state, invariant state → invariant { state with clock := state.clock + 1 })
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hinitial : invariant execution.native.application.visible)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).round
      principals serviceSlots players environment execution).support) :
    invariant next.native.application.visible := by
  simp only [MessageApplication.RoundDriver.round, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hmiddleInvariant := runtime.runPolicies_public_invariant hhandler invariant
    hrecord hrefresh hclock players
    ((runtime.host prepare applyMessage).wireEnvironment environment) _ execution middle
    hinitial hmiddle
  rw [runtime.host_clockStep_native middle next hnext]
  exact hrefresh true _ (hclock _ hmiddleInvariant)

private theorem runRounds_public_invariant (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (invariant : PublicState Principal Value → Prop)
    (hrecord : ∀ state event, invariant state →
      invariant { state with events := state.events ++ [event] })
    (hrefresh : ∀ resolve state, invariant state → invariant (runtime.refresh resolve state))
    (hclock : ∀ state, invariant state → invariant { state with clock := state.clock + 1 })
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (count : Nat) (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hinitial : invariant execution.native.application.visible)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).runRounds principals
      serviceSlots players environment
      count execution).support) : invariant next.native.application.visible := by
  induction count generalizing execution with
  | zero =>
      simp only [MessageApplication.RoundDriver.runRounds, FinDist.mem_support_pure] at hnext
      subst next
      exact hinitial
  | succ count ih =>
      simp only [MessageApplication.RoundDriver.runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hinitial
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        exact ih middle (runtime.round_public_invariant hhandler invariant hrecord hrefresh hclock
          principals serviceSlots players environment execution middle hinitial hmiddle) hnext

omit [DecidableEq Principal] in
private theorem record_completed (state : PublicState Principal Value)
    (event : SealedProgram.Event Principal Value) (node : Nat)
    (hcompleted : state.completed node = true) :
    ({ state with events := state.events ++ [event] }).completed node = true := by
  simp only [PublicState.completed, SealedProgram.done, List.any_append, Bool.or_eq_true]
    at hcompleted ⊢
  exact hcompleted.elim (fun h => Or.inl (Or.inl h)) Or.inr

/-- Completion of a node persists through arbitrary subsequent traffic and rounds. -/
theorem runRounds_completed (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (count : Nat) (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (node : Nat)
    (hinitial : execution.native.application.visible.completed node = true)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).runRounds principals
      serviceSlots players environment
      count execution).support) : next.native.application.visible.completed node = true := by
  apply runtime.runRounds_public_invariant hhandler (fun state => state.completed node = true)
    (fun state event hstate => record_completed state event node hstate)
    (fun resolve state hstate => runtime.refresh_completed resolve state node hstate)
    (fun _ hstate => hstate) principals serviceSlots players environment count execution next
    hinitial hnext

/-- First-readiness timestamps cannot be postponed by traffic or clock ticks. -/
theorem runRounds_firstReady?_of_some (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (count : Nat) (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (node timestamp : Nat)
    (hinitial : execution.native.application.visible.firstReady? node = some timestamp)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).runRounds principals
      serviceSlots players environment
      count execution).support) :
    next.native.application.visible.firstReady? node = some timestamp := by
  apply runtime.runRounds_public_invariant hhandler
    (fun state => state.firstReady? node = some timestamp)
    (fun _ _ hstate => hstate)
    (fun resolve state hstate => runtime.refresh_firstReady?_of_some resolve state node timestamp
      hstate)
    (fun _ hstate => hstate) principals serviceSlots players environment count execution next
    hinitial hnext

omit [DecidableEq Principal] in
private theorem clockBounded_advance (state : PublicState Principal Value)
    (hstate : state.ClockBounded) :
    ({ state with clock := state.clock + 1 }).ClockBounded := by
  intro node timestamp hready
  exact Nat.le_trans (hstate node timestamp hready) (Nat.le_succ state.clock)

/-- Reachable readiness timestamps never lie in the future. -/
theorem runRounds_clockBounded (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (count : Nat) (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hinitial : execution.native.application.visible.ClockBounded)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).runRounds principals
      serviceSlots players environment
      count execution).support) : next.native.application.visible.ClockBounded := by
  apply runtime.runRounds_public_invariant hhandler PublicState.ClockBounded
    (fun _ _ hstate => hstate) (fun resolve _ hstate => hstate.refresh resolve)
    clockBounded_advance principals serviceSlots players environment count execution next
    hinitial hnext

omit [DecidableEq Principal] in
private theorem complete_node (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (node : Nat)
    (hcomplete : runtime.complete state = true) (hnode : node < runtime.program.rules.length) :
    state.completed node = true :=
  List.all_eq_true.mp hcomplete node (List.mem_range.mpr hnode)

private theorem round_requires (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution) (requires : List Nat)
    (hinitial : requires.all execution.native.application.visible.completed = true)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).round
      principals serviceSlots players environment execution).support) :
    requires.all next.native.application.visible.completed = true := by
  apply List.all_eq_true.mpr
  intro node hnode
  exact runtime.round_public_invariant hhandler (fun state => state.completed node = true)
    (fun state event hstate => record_completed state event node hstate)
    (fun resolve state hstate => runtime.refresh_completed resolve state node hstate)
    (fun _ hstate => hstate) principals serviceSlots players environment execution next
    (List.all_eq_true.mp hinitial node hnode) hnext

private theorem round_progress (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution) (node : Nat)
    (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule) (hkind : rule.kind ≠ .disabled)
    (hrequires : rule.requires.all execution.native.application.visible.completed = true)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnode : node < runtime.program.rules.length)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).round
      principals serviceSlots players environment execution).support) :
    next.native.application.visible.completed node = true ∨
      ∃ timestamp, next.native.application.visible.firstReady? node = some timestamp ∧
        timestamp ≤ next.native.application.visible.clock ∧
        next.native.application.visible.clock < timestamp + runtime.window := by
  simp only [MessageApplication.RoundDriver.round, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hmiddleBounded := runtime.runPolicies_public_invariant hhandler PublicState.ClockBounded
    (fun _ _ hstate => hstate) (fun resolve _ hstate => hstate.refresh resolve)
    clockBounded_advance players ((runtime.host prepare applyMessage).wireEnvironment environment)
    _ execution middle hbounded hmiddle
  have hmiddleRequires : rule.requires.all middle.native.application.visible.completed = true := by
    apply List.all_eq_true.mpr
    intro prerequisite hprerequisite
    exact runtime.runPolicies_public_invariant hhandler
      (fun state => state.completed prerequisite = true)
      (fun state event hstate => record_completed state event prerequisite hstate)
      (fun resolve state hstate => runtime.refresh_completed resolve state prerequisite hstate)
      (fun _ hstate => hstate) players
      ((runtime.host prepare applyMessage).wireEnvironment environment)
      _ execution middle (List.all_eq_true.mp hrequires prerequisite hprerequisite) hmiddle
  rw [runtime.host_clockStep_native middle next hnext]
  exact runtime.refresh_progress _ node rule hrule hkind hmiddleRequires
    (clockBounded_advance _ hmiddleBounded) hnode

private theorem runRounds_ready_progress (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (count : Nat) (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (node : Nat)
    (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule) (hkind : rule.kind ≠ .disabled)
    (hrequires : rule.requires.all execution.native.application.visible.completed = true)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnode : node < runtime.program.rules.length) (hcount : 0 < count)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).runRounds principals
      serviceSlots players environment
      count execution).support) :
    next.native.application.visible.completed node = true ∨
      ∃ timestamp, next.native.application.visible.firstReady? node = some timestamp ∧
        timestamp ≤ next.native.application.visible.clock ∧
        next.native.application.visible.clock < timestamp + runtime.window := by
  induction count generalizing execution with
  | zero => omega
  | succ count ih =>
      simp only [MessageApplication.RoundDriver.runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact Or.inl (runtime.complete_node execution.native.application.visible node ‹_› hnode)
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        cases count with
        | zero =>
            simp only [MessageApplication.RoundDriver.runRounds, FinDist.mem_support_pure] at hnext
            subst next
            exact runtime.round_progress hhandler principals serviceSlots players environment
              execution middle node rule hrule hkind hrequires hbounded hnode hmiddle
        | succ count =>
            exact ih middle
              (runtime.round_requires hhandler principals serviceSlots players environment
                execution middle rule.requires hrequires hmiddle)
              (runtime.round_public_invariant hhandler PublicState.ClockBounded
                (fun _ _ hstate => hstate) (fun resolve _ hstate => hstate.refresh resolve)
                clockBounded_advance principals serviceSlots players environment execution middle
                hbounded hmiddle) (by omega) hnext

/-- A ready enabled node completes within one timeout window plus its first
round boundary. This permits arbitrary randomized policies and even zero wire
service: completion may be a timeout, not delivery of a valid message. -/
theorem runRounds_ready_complete (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution) (node : Nat)
    (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule) (hkind : rule.kind ≠ .disabled)
    (hrequires : rule.requires.all execution.native.application.visible.completed = true)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnode : node < runtime.program.rules.length)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).runRounds principals
      serviceSlots players environment
      (runtime.window + 1) execution).support) :
    next.native.application.visible.completed node = true := by
  have hprogress := runtime.runRounds_ready_progress hhandler principals serviceSlots
    players environment (runtime.window + 1) execution next node rule hrule hkind
    hrequires hbounded hnode (by omega) hnext
  rcases hprogress with hcomplete | ⟨finalTime, hfinalTime, _, hfinalUnexpired⟩
  · exact hcomplete
  by_contra hnotComplete
  have hincomplete : runtime.complete next.native.application.visible = false := by
    apply Bool.eq_false_of_not_eq_true
    exact fun h => hnotComplete (runtime.complete_node _ node h hnode)
  simp only [MessageApplication.RoundDriver.runRounds] at hnext
  split at hnext
  · simp only [FinDist.mem_support_pure] at hnext
    subst next
    exact hnotComplete (runtime.complete_node _ node ‹_› hnode)
  · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
    obtain ⟨middle, hmiddle, hnext⟩ := hnext
    rcases runtime.round_progress hhandler principals serviceSlots players environment
        execution middle node rule hrule hkind hrequires hbounded hnode hmiddle with
      hcomplete | ⟨timestamp, htimestamp, htimeBounded, _⟩
    · exact hnotComplete (runtime.runRounds_completed hhandler principals serviceSlots
        players environment runtime.window middle next node hcomplete hnext)
    · have hpersist := runtime.runRounds_firstReady?_of_some hhandler principals serviceSlots
        players environment runtime.window middle next node timestamp htimestamp hnext
      have hclock := runtime.runRounds_clock_ge_of_incomplete hhandler principals serviceSlots
        players environment runtime.window middle next hnext hincomplete
      rw [hfinalTime] at hpersist
      have htime := Option.some.inj hpersist
      omega

private theorem runRounds_prefix_completed (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (henabled : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule → rule.kind ≠ .disabled)
    (hbackward : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (count : Nat) (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hcount : count ≤ runtime.program.rules.length)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).runRounds principals
      serviceSlots players environment
      (count * (runtime.window + 1)) execution).support) :
    ∀ node < count, next.native.application.visible.completed node = true := by
  induction count generalizing next with
  | zero => intro node hnode; omega
  | succ count ih =>
      rw [Nat.succ_mul, (runtime.hostRoundDriver prepare applyMessage).runRounds_add] at hnext
      simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hprefix := ih middle (by omega) hmiddle
      intro node hnode
      by_cases hprior : node < count
      · exact runtime.runRounds_completed hhandler principals serviceSlots players environment
          (runtime.window + 1) middle next node (hprefix node hprior) hnext
      · have hnodeEq : node = count := by omega
        subst node
        have hindex : count < runtime.program.rules.length := by omega
        let rule := runtime.program.rules[count]
        have hrule : runtime.program.rules[count]? = some rule :=
          List.getElem?_eq_getElem hindex
        apply runtime.runRounds_ready_complete hhandler principals serviceSlots players environment
          middle next count rule hrule (henabled count rule hrule) ?_ ?_ hindex hnext
        · apply List.all_eq_true.mpr
          intro prerequisite hprerequisite
          exact hprefix prerequisite (hbackward count rule hrule prerequisite hprerequisite)
        · exact runtime.runRounds_clockBounded hhandler principals serviceSlots players environment
            (count * (runtime.window + 1)) execution middle hbounded hmiddle

/-- Every enabled backward-dependency program completes within

`number of rules * (timeout window + 1)` rounds.

No roster coverage or message-service premise is required: the mandatory
clock may complete nodes by timeout. This theorem establishes termination,
not honest success, source settlement, or an incentive bound. -/
theorem runRounds_complete (runtime : SealedResolution Principal Value)
    (hhandler : runtime.HandlerRecords applyMessage)
    (henabled : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule → rule.kind ≠ .disabled)
    (hbackward : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (total : Nat) (hbound : runtime.program.rules.length * (runtime.window + 1) ≤ total)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).runRounds principals
      serviceSlots players environment total execution).support) :
    runtime.complete next.native.application.visible = true := by
  let bound := runtime.program.rules.length * (runtime.window + 1)
  have hsplit : total = bound + (total - bound) := by omega
  rw [hsplit, (runtime.hostRoundDriver prepare applyMessage).runRounds_add] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hcomplete : runtime.complete middle.native.application.visible = true := by
    apply List.all_eq_true.mpr
    intro node hnode
    exact runtime.runRounds_prefix_completed hhandler henabled hbackward principals serviceSlots
      players environment runtime.program.rules.length execution middle (Nat.le_refl _)
      hbounded hmiddle node (List.mem_range.mp hnode)
  rw [(runtime.hostRoundDriver prepare applyMessage).runRounds_of_complete principals serviceSlots
    players environment _ middle hcomplete, FinDist.mem_support_pure] at hnext
  simpa only [hnext] using hcomplete

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runRounds_complete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runRounds_complete
