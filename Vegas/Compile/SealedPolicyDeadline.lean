/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPhaseCount
import Interaction.SealedResolutionDeadline

/-! # Timely polling excludes compiled-player timeouts

An actual readiness timestamp supplies the target's native prerequisites.
Enough compiled-player polls and bounded queue service complete that target.
If their endpoint precedes the timestamp's deadline, completion is not a
timeout; no later native action can turn that completed site into a timeout.

The polling and service conditions concern the actual shared execution trace.
Instantiating them uniformly from a round roster, clock window, and reserved
inclusion capacity is a separate scheduling obligation.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Timely service of enough actual compiled-player polls rules out this
source site's timeout at every later checkpoint, under arbitrary intervening
player and environment policies. The original timestamp is never postponed. -/
theorem no_timeout_of_poll_service (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
        players environment schedule (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support)
    (who : Player) (policy : CommitPolicy G who)
    (hpolicy : players who = supported.resolvingPolicy nullValue window who policy)
    (target : Fin G.nodeCount)
    (howned :
      (∃ guard, (G.nodeRow target).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow target).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard)
    (position : Nat → Nat) (hposition : StrictMono position)
    (delay count : Nat) (hcount : (target.val + 1) * (delay + 2) < count)
    (hcall : ∀ round < count, schedule[position round]? = some (.player who))
    (timestamp : Nat)
    (hstamp : (trace.drop (position 0)).first.native.application.visible.firstReady?
      target.val = some timestamp)
    (hdeadline : (trace.drop (position (count - 1))).first.native.application.visible.clock <
      timestamp + window)
    (hservice : ∀ round < count, ∃ checkpoint,
      position round + 1 ≤ checkpoint ∧ checkpoint ≤ position (round + delay + 1) ∧
      ((supported.resolvingRuntime nullValue window).complete
          (trace.drop checkpoint).first.native.application.visible = true ∨
        (trace.drop checkpoint).first.native.pool.pending = []))
    (later : Nat) (hlater : position (count - 1) ≤ later) :
    target.val ∉ (trace.drop later).first.native.application.visible.timeouts := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  let before := (trace.drop (position 0)).first
  let serviced := (trace.drop (position (count - 1))).first
  have hprefix := (runtime.messageApplication.tracePolicies_drop_support players environment
    schedule initial trace htrace (position 0)).1
  have hreadySound := runtime.runPolicies_readySound players environment
    (schedule.take (position 0)) initial before
    (SealedResolution.PublicState.ReadySound.initial runtime) hprefix
  obtain ⟨rule, hrule, hready⟩ := hreadySound target.val timestamp hstamp
  change supported.compile.rules[target.val]? = some rule at hrule
  rw [supported.compile_rule] at hrule
  have hruleEq := Option.some.inj hrule
  subst rule
  have hcompleted := supported.completed_by_poll nullValue window players environment schedule
    trace htrace who policy hpolicy target howned position hposition delay count hcount hcall
    hready hservice
  have hbetween := runtime.messageApplication.tracePolicies_between players environment
    schedule initial trace htrace (position 0) (position (count - 1) - position 0)
  rw [Nat.add_sub_of_le (hposition.monotone (Nat.zero_le (count - 1)))] at hbetween
  have hstampServiced := runtime.runPolicies_firstReady?_of_some players environment
    ((schedule.drop (position 0)).take (position (count - 1) - position 0)) before serviced
    target.val timestamp hstamp hbetween
  have hservicedPrefix := (runtime.messageApplication.tracePolicies_drop_support players environment
    schedule initial trace htrace (position (count - 1))).1
  have hdeadlineSound := runtime.runPolicies_deadlineSound players environment
    (schedule.take (position (count - 1))) initial serviced
    (SealedResolution.PublicState.DeadlineSound.initial runtime) hservicedPrefix
  have hnoTimeout : target.val ∉ serviced.native.application.visible.timeouts := by
    intro htimeout
    obtain ⟨rule, recorded, hrule, hrecorded, hexpired, hready⟩ :=
      hdeadlineSound target.val htimeout
    have heq : timestamp = recorded := Option.some.inj (hstampServiced.symm.trans hrecorded)
    subst recorded
    change timestamp + window ≤
      (trace.drop (position (count - 1))).first.native.application.visible.clock at hexpired
    omega
  have hremaining := runtime.messageApplication.tracePolicies_between players environment
    schedule initial trace htrace (position (count - 1)) (later - position (count - 1))
  rw [Nat.add_sub_of_le hlater] at hremaining
  exact runtime.runPolicies_no_timeout_of_completed players environment
    ((schedule.drop (position (count - 1))).take (later - position (count - 1))) serviced
    (trace.drop later).first target.val hcompleted hnoTimeout hremaining

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.no_timeout_of_poll_service' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.no_timeout_of_poll_service
