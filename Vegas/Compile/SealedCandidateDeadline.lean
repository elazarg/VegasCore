/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateCount
import Interaction.SealedResolutionPolling

/-! # Timely polling excludes candidate-player timeouts

An actual readiness timestamp supplies the target's native prerequisites.
Enough compiled-player polls and bounded queue service complete that target.
If their endpoint precedes the timestamp's deadline, completion is not a
timeout; no later native action can turn that completed site into a timeout.

Polling and service are conditions on actual native checkpoints. Player
traffic, candidate identities, and all intervening environment choices remain
unrestricted. The periodic-service theorem derives the checkpoint conditions from the
actual roster, reserved inclusion capacity, and deadline window.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Timely service of enough actual compiled-player polls rules out this
graph site's timeout at every later checkpoint, under arbitrary intervening
player and environment policies. The original timestamp is never postponed. -/
theorem candidate_no_timeout_of_poll_service (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (trace : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.tracePolicies
        players environment schedule (PolicyExecution.initial _
          (State.initial _
            (supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (who : Player) (policy : CommitPolicy G who)
    (hpolicy : players who = (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who policy))
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
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial runtime.candidateApplication runtime.candidateInitial)
  let before := (trace.drop (position 0)).first
  have hprefix := (runtime.candidateApplication.tracePolicies_drop_support players environment
    schedule initial trace htrace (position 0)).1
  have hreadySound := runtime.runPolicies_readySound
    (fun (service : CommitmentCandidates Player Nat (L.Val ty)) owner slot value =>
      service.prepare owner slot value) runtime.candidateHandle runtime.candidateHandle_records
    players environment
    (schedule.take (position 0)) initial before
    (SealedResolution.PublicState.ReadySound.initial runtime) hprefix
  obtain ⟨rule, hrule, hready⟩ := hreadySound target.val timestamp hstamp
  change supported.compile.rules[target.val]? = some rule at hrule
  rw [supported.compile_rule] at hrule
  have hruleEq := Option.some.inj hrule
  subst rule
  have hcompleted := supported.candidate_completed_by_poll nullValue window players environment
    schedule trace htrace who policy hpolicy target howned position hposition delay count
    hcount hcall
    hready hservice
  exact runtime.tracePolicies_no_timeout_of_timely_completion
    (fun (service : CommitmentCandidates Player Nat (L.Val ty)) owner slot value =>
      service.prepare owner slot value)
    runtime.candidateHandle runtime.candidateHandle_records players environment schedule
    initial trace
    (SealedResolution.PublicState.DeadlineSound.initial runtime) htrace target.val
    (position 0) (position (count - 1)) later (hposition.monotone (Nat.zero_le (count - 1)))
    hlater timestamp hstamp hcompleted hdeadline

section PeriodicService

variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (wire : (supported.resolvingRuntime nullValue window).candidateApplication.WirePolicy)
    (reserved : Nat → Bool)
    (hservice : (supported.resolvingRuntime nullValue window).candidateApplication.InclusionService
      (fun turn => reserved turn = true)
      ((supported.resolvingRuntime nullValue window).candidateApplication.wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (((block + 1) * period - 1) * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (who : Player) (policy : CommitPolicy G who)
    (hpolicy : players who = (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who policy))
    (target : Fin G.nodeCount)
    (howned :
      (∃ guard, (G.nodeRow target).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow target).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard)
    (slot : Nat) (hslot : principals[slot]? = some who)
    (hwindow : (target.val + 1) * (period + 1) + 2 ≤ window)

include hservice hperiod hcapacity hpolicy howned hslot hwindow

/-- A compiled player's owned site never times out under periodic reserved
capacity and a sufficiently large clock window. This is uniform over all
supported traces and all other native player policies, including arbitrary
pending-message reactions. No execution-specific service witness is assumed. -/
theorem candidate_tracePolicies_no_timeout (total : Nat) (hperiods : period ∣ total)
    (trace : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.tracePolicies players
        ((supported.resolvingRuntime nullValue window).candidateRoundDriver.environmentPolicy
          serviceSlots wire)
        (MessageApplication.roundSchedule principals serviceSlots total)
        (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue
            window).candidateInitial))).support) :
    target.val ∉ trace.last.native.application.visible.timeouts := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial runtime.candidateApplication runtime.candidateInitial)
  apply runtime.tracePolicies_no_timeout_of_periodic_service
    (fun (service : CommitmentCandidates Player Nat (L.Val ty)) owner slot value =>
      service.prepare owner slot value) runtime.candidateHandle runtime.candidateHandle_records
    principals serviceSlots players wire reserved hservice period hperiod hcapacity
    total hperiods initial trace htrace (runtime.refresh_clock false {}) rfl rfl
    (SealedResolution.PublicState.ReadySound.initial runtime)
    (SealedResolution.PublicState.DeadlineSound.initial runtime)
    who target.val slot ((target.val + 1) * (period + 1)) hslot hwindow
  intro position hposition hcall hready hpollService
  obtain ⟨rule, hrule, hrequires⟩ := hready
  change supported.compile.rules[target.val]? = some rule at hrule
  rw [supported.compile_rule] at hrule
  have hruleEq := Option.some.inj hrule
  subst rule
  have hcount : (target.val + 1) * (period - 1 + 2) <
      (target.val + 1) * (period + 1) + 1 := by
    rw [show period - 1 + 2 = period + 1 by omega]
    omega
  have hcompleted := supported.candidate_completed_by_poll nullValue window players
    (runtime.candidateRoundDriver.environmentPolicy serviceSlots wire)
    (roundSchedule principals serviceSlots total) trace htrace who policy hpolicy target howned
    position hposition (period - 1) ((target.val + 1) * (period + 1) + 1) hcount hcall
    hrequires (fun round hround => by
      have heq : round + (period - 1) + 1 = round + period := by omega
      simpa only [heq] using hpollService round hround)
  simpa only [Nat.add_sub_cancel_right] using hcompleted

/-- The same timeout exclusion holds at the actual early-stopping round
readout. Later auxiliary trace execution cannot erase a recorded timeout. -/
theorem candidate_runRounds_no_timeout (total : Nat) (hperiods : period ∣ total)
    (next : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hnext : next ∈ ((supported.resolvingRuntime nullValue window).candidateRoundDriver.runRounds
      principals serviceSlots players wire total (PolicyExecution.initial _
        (State.initial _ (supported.resolvingRuntime nullValue
          window).candidateInitial))).support) :
    target.val ∉ next.native.application.visible.timeouts := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial runtime.candidateApplication runtime.candidateInitial)
  let environment := runtime.candidateRoundDriver.environmentPolicy serviceSlots wire
  let schedule := MessageApplication.roundSchedule principals serviceSlots total
  let width := (MessageApplication.roundInvocations principals serviceSlots).length
  rw [runtime.candidateRoundDriver.runRounds_eq_tracePolicies principals serviceSlots players wire
    total initial
    (by rfl), FinDist.support_map] at hnext
  obtain ⟨trace, htrace, rfl⟩ := hnext
  have hclear := supported.candidate_tracePolicies_no_timeout nullValue window principals
    serviceSlots
    players wire reserved hservice period hperiod hcapacity who policy hpolicy target howned
    slot hslot hwindow total hperiods trace htrace
  obtain ⟨front, suffix, hsplit, hfront, hsuffix⟩ :=
    runtime.candidateApplication.tracePolicies_firstReleaseEvery_split players environment width
      total (fun state => runtime.complete state.native.application.visible)
      (by simp [width, MessageApplication.roundInvocations]) schedule initial trace
      (by rw [MessageApplication.roundSchedule_length]) htrace
  intro htimeout
  exact hclear (runtime.runPolicies_timeout_mem
    (fun (service : CommitmentCandidates Player Nat (L.Val ty)) owner slot value =>
      service.prepare owner slot value) runtime.candidateHandle runtime.candidateHandle_records
    players environment suffix _ trace.last
    target.val htimeout hsuffix)

end PeriodicService

/-- Every recorded failure belongs to an owner outside the protected set.
Protected players use compiled policies and occur in the roster; all other
players remain unrestricted. This operational statement makes no coalition
equilibrium claim. -/
theorem candidate_runRounds_timeout_owner (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (principals : List Player) (serviceSlots : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (wire : (supported.resolvingRuntime nullValue window).candidateApplication.WirePolicy)
    (reserved : Nat → Bool)
    (hservice : (supported.resolvingRuntime nullValue window).candidateApplication.InclusionService
      (fun turn => reserved turn = true)
      ((supported.resolvingRuntime nullValue window).candidateApplication.wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (((block + 1) * period - 1) * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (profile : ∀ who, CommitPolicy G who) (honest : Player → Prop)
    (hplayers : ∀ who, honest who →
      players who = (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
        (supported.resolvingPolicy nullValue window who (profile who)))
    (hroster : ∀ who, honest who → who ∈ principals)
    (hwindow : G.nodeCount * (period + 1) + 2 ≤ window)
    (total : Nat) (hperiods : period ∣ total)
    (next : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hnext : next ∈ ((supported.resolvingRuntime nullValue window).candidateRoundDriver.runRounds
      principals serviceSlots players wire total (PolicyExecution.initial _
        (State.initial _ (supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (index : Nat) (htimeout : index ∈ next.native.application.visible.timeouts) :
    ∃ (node : Fin G.nodeCount) (owner : Player), node.val = index ∧ ¬ honest owner ∧
      ((∃ guard, (G.nodeRow node).sem = .commit owner guard) ∨
        ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
          (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
          (G.nodeRow producer).sem = .commit owner guard) := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial runtime.candidateApplication runtime.candidateInitial)
  have hsound := runtime.runRounds_deadlineSound
    (fun (service : CommitmentCandidates Player Nat (L.Val ty)) owner slot value =>
      service.prepare owner slot value) runtime.candidateHandle runtime.candidateHandle_records
    principals serviceSlots players wire total
    initial next (by rfl) (SealedResolution.PublicState.DeadlineSound.initial runtime) hnext
  obtain ⟨rule, timestamp, hrule, hstamp, hdeadline, hready⟩ := hsound index htimeout
  obtain ⟨node, hindex, _⟩ := supported.ruleAt_exists_node hrule
  obtain ⟨owner, howned⟩ := supported.node_owner node
  refine ⟨node, owner, hindex, ?_, howned⟩
  intro hprotected
  obtain ⟨slot, hslot⟩ := List.mem_iff_getElem?.mp (hroster owner hprotected)
  have hnodeWindow : (node.val + 1) * (period + 1) + 2 ≤ window := by
    have hbound := Nat.mul_le_mul_right (period + 1) node.isLt
    change (node.val + 1) * (period + 1) ≤ G.nodeCount * (period + 1) at hbound
    omega
  have hclear := supported.candidate_runRounds_no_timeout nullValue window principals serviceSlots
    players wire reserved hservice period hperiod hcapacity owner (profile owner)
    (hplayers owner hprotected) node howned slot hslot hnodeWindow total hperiods next hnext
  exact hclear (by simpa only [hindex] using htimeout)

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidate_no_timeout_of_poll_service'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidate_no_timeout_of_poll_service


/-- info: 'Vegas.EventGraph.SealedFragment.candidate_tracePolicies_no_timeout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidate_tracePolicies_no_timeout

/-- info: 'Vegas.EventGraph.SealedFragment.candidate_runRounds_no_timeout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidate_runRounds_no_timeout

/-- info: 'Vegas.EventGraph.SealedFragment.candidate_runRounds_timeout_owner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidate_runRounds_timeout_owner
