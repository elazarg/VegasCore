/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPhaseCount
import Interaction.SealedResolutionDeadline
import Interaction.SealedResolutionPeriodicService

/-! # Timely polling excludes compiled-player timeouts

An actual readiness timestamp supplies the target's native prerequisites.
Enough compiled-player polls and bounded queue service complete that target.
If their endpoint precedes the timestamp's deadline, completion is not a
timeout; no later native action can turn that completed site into a timeout.

The periodic-service theorem derives the polling and service conditions from
the actual round roster, clock window, and reserved inclusion capacity. All
other players and all unreserved wire choices remain arbitrary.
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

section PeriodicService

variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (wire : (supported.resolvingRuntime nullValue window).messageApplication.WirePolicy)
    (reserved : Nat → Bool)
    (hservice : (supported.resolvingRuntime nullValue window).messageApplication.InclusionService
      (fun turn => reserved turn = true)
      ((supported.resolvingRuntime nullValue window).messageApplication.wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (((block + 1) * period - 1) * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (who : Player) (policy : CommitPolicy G who)
    (hpolicy : players who = supported.resolvingPolicy nullValue window who policy)
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
theorem tracePolicies_no_timeout (total : Nat) (hperiods : period ∣ total)
    (trace : (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (htrace : trace ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.tracePolicies players
        ((supported.resolvingRuntime nullValue window).roundDriver.environmentPolicy
          serviceSlots wire)
        (MessageApplication.roundSchedule principals serviceSlots total)
        (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support) :
    target.val ∉ trace.last.native.application.visible.timeouts := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  let environment := runtime.roundDriver.environmentPolicy serviceSlots wire
  let schedule := MessageApplication.roundSchedule principals serviceSlots total
  let width := (MessageApplication.roundInvocations principals serviceSlots).length
  have hinitialClock : initial.native.application.visible.clock = 0 :=
    runtime.refresh_clock false {}
  have hlast : (trace.drop (total * width)).first = trace.last := by
    have hlength := runtime.messageApplication.tracePolicies_length players environment schedule
      initial trace htrace
    rw [MessageApplication.roundSchedule_length] at hlength
    rw [← hlength, PolicyTrace.drop_length]
    rfl
  have hrun := (runtime.messageApplication.tracePolicies_drop_support players environment schedule
    initial trace htrace (total * width)).1
  rw [hlast] at hrun
  have hsound := runtime.runPolicies_deadlineSound players environment
    (schedule.take (total * width)) initial trace.last
    (SealedResolution.PublicState.DeadlineSound.initial runtime) hrun
  have hfinalClock := (runtime.tracePolicies_round_clock principals serviceSlots players wire
    total total initial trace (by rfl) htrace le_rfl).1
  rw [hlast, hinitialClock, Nat.zero_add] at hfinalClock
  intro htimeout
  obtain ⟨rule, timestamp, hrule, hstampFinal, hexpired, hrequires⟩ := hsound target.val htimeout
  change timestamp + window ≤ trace.last.native.application.visible.clock at hexpired
  rw [hfinalClock] at hexpired
  let budget := (target.val + 1) * (period + 1)
  let position := fun round => (timestamp + 1 + round) * width + slot
  have hslotLength : slot < principals.length := (List.getElem?_eq_some_iff.mp hslot).1
  have hwidth : 0 < width := by simp [width, MessageApplication.roundInvocations]
  have hslotWidth : slot < width := by
    dsimp [width, MessageApplication.roundInvocations]
    simp only [List.length_append, List.length_map, List.length_replicate, List.length_singleton]
    omega
  have hposition : StrictMono position := by
    intro left right hlt
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right (by omega) hwidth) slot
  have hwithin : ∀ round < budget + 1, timestamp + 1 + round < total := by
    intro round hround
    dsimp [budget] at hround
    omega
  have hpollClock : ∀ round < budget + 1,
      (trace.drop (position round)).first.native.application.visible.clock =
        timestamp + 1 + round := by
    intro round hround
    have hclock := (runtime.tracePolicies_poll_clock principals serviceSlots players wire total
      (timestamp + 1 + round) slot initial trace (by rfl) htrace
      (hwithin round hround) hslotLength).1
    simpa only [hinitialClock, Nat.zero_add] using hclock
  have hfirstLe : position 0 ≤ total * width := by
    have hbound := Nat.mul_le_mul_right width (hwithin 0 (by omega))
    rw [Nat.succ_mul] at hbound
    dsimp [position]
    omega
  have hsuffix := runtime.messageApplication.tracePolicies_between players environment schedule
    initial trace htrace (position 0) (total * width - position 0)
  rw [Nat.add_sub_of_le hfirstLe, hlast] at hsuffix
  have hstamp := runtime.runPolicies_firstReady?_of_lt_clock players environment
    ((schedule.drop (position 0)).take (total * width - position 0))
    (trace.drop (position 0)).first trace.last target.val timestamp hsuffix hstampFinal
    (by rw [hpollClock 0 (by omega)]; omega)
  have hclear := supported.no_timeout_of_poll_service nullValue window players environment
    schedule trace htrace who policy hpolicy target howned position hposition (period - 1)
    (budget + 1) (by
      have heq : period - 1 + 2 = period + 1 := by omega
      rw [heq]
      exact Nat.lt_succ_self budget)
    (fun round hround => MessageApplication.roundSchedule_player principals serviceSlots total
      (timestamp + 1 + round) slot who (hwithin round hround) hslot)
    timestamp hstamp (by
      rw [Nat.add_sub_cancel_right, hpollClock budget (Nat.lt_succ_self budget)]
      dsimp [budget]
      omega)
    (fun round hround => by
      obtain ⟨checkpoint, hafter, hbefore, hempty⟩ := runtime.tracePolicies_periodic_service
        principals serviceSlots players wire total initial trace (by rfl) htrace reserved hservice
        period hperiod (by
          simpa only [initial, PolicyExecution.initial, List.length_nil, Nat.zero_add]
            using hcapacity) rfl hperiods (timestamp + 1 + round) slot
        (hwithin round hround) hslotLength
      refine ⟨checkpoint, hafter, ?_, Or.inr hempty⟩
      convert hbefore using 1
      dsimp [position]
      congr 2
      omega)
    (total * width) (by
      rw [Nat.add_sub_cancel_right]
      have hbound := Nat.mul_le_mul_right width (hwithin budget (Nat.lt_succ_self budget))
      rw [Nat.succ_mul] at hbound
      dsimp [position]
      omega)
  rw [hlast] at hclear
  exact hclear htimeout

/-- The same timeout exclusion holds at the actual early-stopping round
readout. Later auxiliary trace execution cannot erase a recorded timeout. -/
theorem runRounds_no_timeout (total : Nat) (hperiods : period ∣ total)
    (next : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hnext : next ∈ ((supported.resolvingRuntime nullValue window).roundDriver.runRounds
      principals serviceSlots players wire total (PolicyExecution.initial _
        (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support) :
    target.val ∉ next.native.application.visible.timeouts := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  let environment := runtime.roundDriver.environmentPolicy serviceSlots wire
  let schedule := MessageApplication.roundSchedule principals serviceSlots total
  let width := (MessageApplication.roundInvocations principals serviceSlots).length
  rw [runtime.roundDriver.runRounds_eq_tracePolicies principals serviceSlots players wire
    total initial
    (by rfl), FinDist.support_map] at hnext
  obtain ⟨trace, htrace, rfl⟩ := hnext
  have hclear := supported.tracePolicies_no_timeout nullValue window principals serviceSlots
    players wire reserved hservice period hperiod hcapacity who policy hpolicy target howned
    slot hslot hwindow total hperiods trace htrace
  obtain ⟨front, suffix, hsplit, hfront, hsuffix⟩ :=
    runtime.messageApplication.tracePolicies_firstReleaseEvery_split players environment width
      total (fun state => runtime.complete state.native.application.visible)
      (by simp [width, MessageApplication.roundInvocations]) schedule initial trace
      (by rw [MessageApplication.roundSchedule_length]) htrace
  intro htimeout
  exact hclear (runtime.runPolicies_timeout_mem players environment suffix _ trace.last
    target.val htimeout hsuffix)

end PeriodicService

/-- Every recorded failure belongs to an owner outside the protected set.
Protected players use compiled policies and occur in the roster; all other
players remain unrestricted. This operational statement makes no coalition
equilibrium claim. -/
theorem runRounds_timeout_owner (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (principals : List Player) (serviceSlots : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (wire : (supported.resolvingRuntime nullValue window).messageApplication.WirePolicy)
    (reserved : Nat → Bool)
    (hservice : (supported.resolvingRuntime nullValue window).messageApplication.InclusionService
      (fun turn => reserved turn = true)
      ((supported.resolvingRuntime nullValue window).messageApplication.wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (((block + 1) * period - 1) * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (profile : ∀ who, CommitPolicy G who) (honest : Player → Prop)
    (hplayers : ∀ who, honest who →
      players who = supported.resolvingPolicy nullValue window who (profile who))
    (hroster : ∀ who, honest who → who ∈ principals)
    (hwindow : G.nodeCount * (period + 1) + 2 ≤ window)
    (total : Nat) (hperiods : period ∣ total)
    (next : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hnext : next ∈ ((supported.resolvingRuntime nullValue window).roundDriver.runRounds
      principals serviceSlots players wire total (PolicyExecution.initial _
        (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support)
    (index : Nat) (htimeout : index ∈ next.native.application.visible.timeouts) :
    ∃ (node : Fin G.nodeCount) (owner : Player), node.val = index ∧ ¬ honest owner ∧
      ((∃ guard, (G.nodeRow node).sem = .commit owner guard) ∨
        ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
          (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
          (G.nodeRow producer).sem = .commit owner guard) := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  have hsound := runtime.runRounds_deadlineSound principals serviceSlots players wire total
    initial next (by rfl) (SealedResolution.PublicState.DeadlineSound.initial runtime) hnext
  obtain ⟨rule, timestamp, hrule, hstamp, hdeadline, hready⟩ := hsound index htimeout
  obtain ⟨node, hindex, _⟩ := supported.ruleAt_exists_node hrule
  have howned : ∃ owner,
      (∃ guard, (G.nodeRow node).sem = .commit owner guard) ∨
        ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
          (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
          (G.nodeRow producer).sem = .commit owner guard := by
    cases hsem : (G.nodeRow node).sem with
    | sample dist => exact (supported.noSamples node dist hsem).elim
    | commit owner guard => exact ⟨owner, Or.inl ⟨guard, rfl⟩⟩
    | reveal source =>
        obtain ⟨producer, owner, guard, hsource, hproducer⟩ :=
          supported.revealSource node source hsem
        exact ⟨owner, Or.inr ⟨producer, guard, by rw [hsource], hproducer⟩⟩
  obtain ⟨owner, howned⟩ := howned
  refine ⟨node, owner, hindex, ?_, howned⟩
  intro hprotected
  obtain ⟨slot, hslot⟩ := List.mem_iff_getElem?.mp (hroster owner hprotected)
  have hnodeWindow : (node.val + 1) * (period + 1) + 2 ≤ window := by
    have hbound := Nat.mul_le_mul_right (period + 1) node.isLt
    change (node.val + 1) * (period + 1) ≤ G.nodeCount * (period + 1) at hbound
    omega
  have hclear := supported.runRounds_no_timeout nullValue window principals serviceSlots
    players wire reserved hservice period hperiod hcapacity owner (profile owner)
    (hplayers owner hprotected) node howned slot hslot hnodeWindow total hperiods next hnext
  exact hclear (by simpa only [hindex] using htimeout)

/-- With all players compiled and covered by the roster, the stopped execution
contains no timeout records. Explicit null choices remain ordinary sealed
choices; the result excludes operational defaults, not source-level quitting. -/
theorem runRounds_timeouts_eq_nil (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (principals : List Player) (serviceSlots : Nat)
    (profile : ∀ who, CommitPolicy G who)
    (wire : (supported.resolvingRuntime nullValue window).messageApplication.WirePolicy)
    (reserved : Nat → Bool)
    (hservice : (supported.resolvingRuntime nullValue window).messageApplication.InclusionService
      (fun turn => reserved turn = true)
      ((supported.resolvingRuntime nullValue window).messageApplication.wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (((block + 1) * period - 1) * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (hroster : ∀ who, who ∈ principals)
    (hwindow : G.nodeCount * (period + 1) + 2 ≤ window)
    (total : Nat) (hperiods : period ∣ total)
    (next : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hnext : next ∈ ((supported.resolvingRuntime nullValue window).roundDriver.runRounds
      principals serviceSlots (fun who =>
        supported.resolvingPolicy nullValue window who (profile who)) wire total
      (PolicyExecution.initial _
        (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support) :
    next.native.application.visible.timeouts = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro index htimeout
  obtain ⟨node, owner, hindex, hnotHonest, howned⟩ := supported.runRounds_timeout_owner
    nullValue window principals serviceSlots (fun who =>
      supported.resolvingPolicy nullValue window who (profile who)) wire reserved hservice
    period hperiod hcapacity profile (fun _ => True) (fun _ _ => rfl)
    (fun who _ => hroster who) hwindow total hperiods next hnext index htimeout
  exact hnotHonest trivial

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.no_timeout_of_poll_service' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.no_timeout_of_poll_service

/-- info: 'Vegas.EventGraph.SealedFragment.tracePolicies_no_timeout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.tracePolicies_no_timeout

/-- info: 'Vegas.EventGraph.SealedFragment.runRounds_no_timeout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.runRounds_no_timeout

/-- info: 'Vegas.EventGraph.SealedFragment.runRounds_timeout_owner' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.runRounds_timeout_owner

/-- info: 'Vegas.EventGraph.SealedFragment.runRounds_timeouts_eq_nil' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.runRounds_timeouts_eq_nil
