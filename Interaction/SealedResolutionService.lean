/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionDriver
import Interaction.MessageApplicationService
import Interaction.SealedResolutionSubmission
import Interaction.SealedResolutionCompletion

/-! # Inclusion capacity and ready-packet progress in the resolving round driver

Reserved service calls consume pending envelopes regardless of their validity.
Other wire calls can deliver, include, or wait adaptively. An adequate number
of reserved calls drains the round's arrivals even under arbitrary player
traffic. Persistent ready canonical packets then complete their nodes. These
operational results do not assume acceptance of arbitrary payloads and do not
yet prove that compiled players meet their deadlines.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- Arrival and service accounting for one round, including an initial backlog,
arbitrary replays, and malformed submissions. This bound permits traffic to
remain pending across player polls when a round has fewer reserved slots. -/
theorem round_pending_bound (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (reserved : Nat → Bool)
    (hservice : runtime.messageApplication.InclusionService
      (fun turn => reserved turn = true) (runtime.messageApplication.wireEnvironment wire))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.roundDriver.round
      principals serviceSlots players wire execution).support) :
    next.native.pool.pending.length ≤ execution.native.pool.pending.length + principals.length -
      (List.range' execution.environmentHistory.length serviceSlots).countP reserved := by
  simp only [MessageApplication.RoundDriver.round, runPolicies_append, FinDist.support_bind,
    Set.mem_iUnion] at hnext
  obtain ⟨serviced, ⟨middle, hmiddle, hserviced⟩, hnext⟩ := hnext
  have harrivals := runtime.messageApplication.runPolicies_pending_bound players
    (runtime.messageApplication.wireEnvironment wire) (principals.map Invocation.player)
    execution middle hmiddle
  simp [Function.comp_def, Invocation.isEnvironment] at harrivals
  have hhistory : middle.environmentHistory.length = execution.environmentHistory.length := by
    simpa [Function.comp_def, Invocation.isEnvironment] using
      runtime.messageApplication.runPolicies_environmentHistory_length players
        (runtime.messageApplication.wireEnvironment wire) (principals.map Invocation.player)
        execution middle hmiddle
  have hremaining := runtime.messageApplication.inclusion_phase_pending_bound players
    reserved (runtime.messageApplication.wireEnvironment wire) hservice serviceSlots
    middle serviced hserviced
  rw [hhistory] at hremaining
  rw [runtime.clockStep_native serviced next hnext]
  dsimp only
  omega

/-- Arrival and invocation accounting, with early stopping retained. -/
private theorem runRounds_resource_bound (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (count : Nat)
    (execution next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈
      (runtime.roundDriver.runRounds
        principals serviceSlots players wire count execution).support) :
    next.native.pool.pending.length ≤ execution.native.pool.pending.length +
      count * principals.length ∧
    (runtime.complete next.native.application.visible = false →
      next.environmentHistory.length = execution.environmentHistory.length +
        count * (serviceSlots + 1)) := by
  induction count generalizing execution with
  | zero =>
      simp only [MessageApplication.RoundDriver.runRounds, FinDist.mem_support_pure] at hnext
      subst next
      simp
  | succ count ih =>
      simp only [MessageApplication.RoundDriver.runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        simp_all
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        have htail := ih middle hnext
        have hround : middle.native.pool.pending.length ≤
            execution.native.pool.pending.length + principals.length := by
          simpa using runtime.round_pending_bound principals serviceSlots players wire
            (fun _ => false) (by intro _ _ _ h; cases h) execution middle hmiddle
        have hhistory := runtime.round_environmentHistory_length principals serviceSlots
          players wire execution middle hmiddle
        constructor
        · simp only [Nat.succ_mul]
          omega
        · intro hincomplete
          rw [htail.2 hincomplete, hhistory, Nat.succ_mul]
          omega

/-- Service may be delayed across an entire block of rounds. Sufficient
reserved capacity in its final wire phase drains every arrival since the
block began, unless the driver has already stopped at application completion.
All earlier wire opportunities remain unrestricted. -/
theorem runRounds_complete_or_pending_empty (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (reserved : Nat → Bool)
    (hservice : runtime.messageApplication.InclusionService
      (fun turn => reserved turn = true) (runtime.messageApplication.wireEnvironment wire))
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (hcapacity : execution.native.pool.pending.length + (count + 1) * principals.length ≤
      (List.range' (execution.environmentHistory.length + count * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (hnext : next ∈
      (runtime.roundDriver.runRounds
        principals serviceSlots players wire (count + 1) execution).support) :
    runtime.complete next.native.application.visible = true ∨ next.native.pool.pending = [] := by
  rw [runtime.roundDriver.runRounds_add principals serviceSlots players wire count 1 execution]
    at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  cases hcomplete : runtime.complete middle.native.application.visible with
  | true =>
      rw [runtime.roundDriver.runRounds_of_complete
        principals serviceSlots players wire 1 middle hcomplete,
        FinDist.mem_support_pure] at hnext
      subst next
      exact Or.inl hcomplete
  | false =>
      have hresources := runtime.runRounds_resource_bound principals serviceSlots players wire
        count execution middle hmiddle
      have hlast : next ∈ (runtime.roundDriver.round
        principals serviceSlots players wire middle).support := by
        simpa only [MessageApplication.RoundDriver.runRounds, hcomplete,
          Bool.false_eq_true, ↓reduceIte,
          FinDist.bind_pure] using hnext
      have hremaining := runtime.round_pending_bound principals serviceSlots players wire
        reserved hservice middle next hlast
      rw [hresources.2 hcomplete] at hremaining
      have hzero : next.native.pool.pending.length = 0 := by
        simp only [Nat.add_mul, Nat.one_mul] at hcapacity
        omega
      exact Or.inr (by simpa using hzero)

/-- With per-round capacity, the queue is empty at every stopping boundary.
Service may depend on the full public pool and its actual environment history;
no restriction is placed on player policies. -/
theorem runRounds_pending_empty (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (reserved : Nat → Bool)
    (hservice : runtime.messageApplication.InclusionService
      (fun turn => reserved turn = true) (runtime.messageApplication.wireEnvironment wire))
    (hcapacity : ∀ turn, turn % (serviceSlots + 1) = 0 →
      principals.length ≤ (List.range' turn serviceSlots).countP reserved)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (hempty : execution.native.pool.pending = [])
    (hnext : next ∈
      (runtime.roundDriver.runRounds
        principals serviceSlots players wire count execution).support) :
    next.native.pool.pending = [] := by
  induction count generalizing execution with
  | zero =>
      simp only [MessageApplication.RoundDriver.runRounds, FinDist.mem_support_pure] at hnext
      subst next
      exact hempty
  | succ count ih =>
      simp only [MessageApplication.RoundDriver.runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hempty
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        apply ih middle ?_ ?_ hnext
        · rw [runtime.round_environmentHistory_length principals serviceSlots players wire
            execution middle hmiddle, Nat.add_mod, hphase]
          simp
        · have hbound := runtime.round_pending_bound principals serviceSlots players wire reserved
            hservice execution middle hmiddle
          rw [hempty, List.length_nil, Nat.zero_add] at hbound
          have hcap := hcapacity execution.environmentHistory.length hphase
          have hzero : middle.native.pool.pending.length = 0 := by omega
          simpa using hzero

private theorem runRounds_policy_prefix (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (count : Nat)
    (execution next : runtime.messageApplication.PolicyExecution)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (hnext : next ∈
      (runtime.roundDriver.runRounds
        principals serviceSlots players wire count execution).support) :
    ∃ schedule, next ∈ (runtime.messageApplication.runPolicies players
      (runtime.roundEnvironment serviceSlots wire) schedule execution).support := by
  rw [runtime.runRounds_eq_tracePolicies principals serviceSlots players wire count
    execution hphase, FinDist.support_map] at hnext
  obtain ⟨trace, htrace, rfl⟩ := hnext
  obtain ⟨front, suffix, _, hfront, _⟩ :=
    runtime.messageApplication.tracePolicies_firstReleaseEvery_split players
      (runtime.roundEnvironment serviceSlots wire)
      (roundInvocations principals serviceSlots).length count
      (fun state => runtime.complete state.native.application.visible)
      (by simp [roundInvocations]) (roundSchedule principals serviceSlots count) execution trace
      (by rw [roundSchedule_length]) htrace
  exact ⟨front, hfront⟩

/-- Delayed reserved capacity completes an already-ready pending commitment.
All earlier service opportunities and all player policies remain unrestricted;
the conclusion follows from native packet persistence, not an acceptance premise. -/
theorem runRounds_ready_commitment_completed (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (reserved : Nat → Bool)
    (hservice : runtime.messageApplication.InclusionService
      (fun turn => reserved turn = true) (runtime.messageApplication.wireEnvironment wire))
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (hcapacity : execution.native.pool.pending.length + (count + 1) * principals.length ≤
      (List.range' (execution.environmentHistory.length + count * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (owner : Principal) (serial node : Nat) (requires : List Nat) (value : Value)
    (hrule : runtime.program.rules[node]? = some { kind := .commit owner, requires })
    (hpending : (⟨(owner, serial), .commitment node (owner, node)⟩ :
      Message Principal (SealedProgram.Payload Principal Value)) ∈ execution.native.pool.pending)
    (hstored : execution.native.application.service.lookup (owner, node) = some value)
    (hrequires : requires.all execution.native.application.visible.completed = true)
    (hnext : next ∈
      (runtime.roundDriver.runRounds
        principals serviceSlots players wire (count + 1) execution).support) :
    next.native.application.visible.completed node = true := by
  rcases runtime.runRounds_complete_or_pending_empty principals serviceSlots players wire
      reserved hservice count execution next hcapacity hnext with hcomplete | hempty
  · exact runtime.complete_node _ node hcomplete (List.getElem?_eq_some_iff.mp hrule).1
  · obtain ⟨schedule, hprefix⟩ := runtime.runRounds_policy_prefix principals serviceSlots
      players wire (count + 1) execution next hphase hnext
    have hretained := runtime.runPolicies_commitment_pendingOrCompleted players
      (runtime.roundEnvironment serviceSlots wire) schedule execution next owner serial node
      requires value hrule hpending hstored hrequires hprefix
    rcases hretained with hdone | hpending
    · exact hdone
    · simp only [hempty, List.not_mem_nil, false_and] at hpending

/-- Delayed reserved capacity also completes a ready pending opening, retaining
its accepted source and private value across arbitrary intervening traffic. -/
theorem runRounds_ready_opening_completed (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (reserved : Nat → Bool)
    (hservice : runtime.messageApplication.InclusionService
      (fun turn => reserved turn = true) (runtime.messageApplication.wireEnvironment wire))
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (hcapacity : execution.native.pool.pending.length + (count + 1) * principals.length ≤
      (List.range' (execution.environmentHistory.length + count * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (owner : Principal) (serial node source : Nat)
    (requires sourceRequires : List Nat) (value : Value)
    (hrule : runtime.program.rules[node]? =
      some { kind := .reveal owner source, requires })
    (hsourceRule : runtime.program.rules[source]? =
      some { kind := .commit owner, requires := sourceRequires })
    (hinvariant : EventInvariant runtime execution.native.application)
    (hpending : (⟨(owner, serial), .opening node (owner, source) value⟩ :
      Message Principal (SealedProgram.Payload Principal Value)) ∈ execution.native.pool.pending)
    (haccepted : SealedProgram.accepted? execution.native.application.visible.events source =
      some (owner, source))
    (hstored : execution.native.application.service.lookup (owner, source) = some value)
    (hrequires : requires.all execution.native.application.visible.completed = true)
    (hnext : next ∈
      (runtime.roundDriver.runRounds
        principals serviceSlots players wire (count + 1) execution).support) :
    next.native.application.visible.completed node = true := by
  rcases runtime.runRounds_complete_or_pending_empty principals serviceSlots players wire
      reserved hservice count execution next hcapacity hnext with hcomplete | hempty
  · exact runtime.complete_node _ node hcomplete (List.getElem?_eq_some_iff.mp hrule).1
  · obtain ⟨schedule, hprefix⟩ := runtime.runRounds_policy_prefix principals serviceSlots
      players wire (count + 1) execution next hphase hnext
    have hretained := runtime.runPolicies_opening_pendingOrCompleted players
      (runtime.roundEnvironment serviceSlots wire) schedule execution next owner serial node source
      requires sourceRequires value hrule hsourceRule hinvariant hpending haccepted hstored
      hrequires hprefix
    rcases hretained with hdone | hpending
    · exact hdone
    · simp only [hempty, List.not_mem_nil, false_and] at hpending

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runRounds_pending_empty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runRounds_pending_empty

/-- info: 'Interaction.SealedResolution.runRounds_complete_or_pending_empty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runRounds_complete_or_pending_empty

/-- info: 'Interaction.SealedResolution.runRounds_ready_opening_completed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runRounds_ready_opening_completed
