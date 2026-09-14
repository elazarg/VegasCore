/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionRounds
import Interaction.MessageApplicationCheckpoints
import Interaction.MessageApplicationEnvironmentPhases

/-! # Round execution as a readout of the shared message runner

The environment services pending traffic at its ordinary opportunities and
performs the mandatory clock action at each round boundary. Its own recorded
history determines this phase; its wire policy retains the actual history and
observation. Selecting the first completed round boundary of the resulting
trace gives exactly the round driver's full execution law.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability
open MessageApplication

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- A principal's actual private history and current observation at the first
timeout, or at the end of the trace when no timeout occurs. On timeout-free
traces this terminal information is intentionally arbitrary for consumers
whose timeout branch is inactive. -/
def firstTimeoutLocalInfo (runtime : SealedResolution Principal Value)
    (principal : Principal) (trace : runtime.messageApplication.PolicyTrace) :
    List runtime.messageApplication.PlayerEntry × runtime.messageApplication.View :=
  let stop : runtime.messageApplication.PolicyExecution → Bool := fun execution =>
    !execution.native.application.visible.timeouts.isEmpty
  let stopped := trace.prefixThrough stop
  (stopped.last.principalHistory principal,
    State.observe runtime.messageApplication stopped.last.native principal)

/-- Player opportunities, wire-service opportunities, then one clock call. -/
def roundInvocations (principals : List Principal) (serviceSlots : Nat) :
    List (@Invocation Principal) :=
  (principals.map Invocation.player ++ List.replicate serviceSlots .environment) ++
    [.environment]

/-- If the completed-round readout contains a timeout, the information used
by `firstTimeoutLocalInfo` comes from at or before that readout, never from
the unused full-trace suffix. No assertion identifies this checkpoint with
the principal's last opportunity to act before the deadline. -/
theorem firstTimeout_before_roundReadout (runtime : SealedResolution Principal Value)
    (trace : runtime.messageApplication.PolicyTrace)
    (principals : List Principal) (serviceSlots count : Nat)
    (htimeout : (trace.firstReleaseEvery (roundInvocations principals serviceSlots).length
      (fun execution : runtime.messageApplication.PolicyExecution =>
        runtime.complete execution.native.application.visible)
      count).native.application.visible.timeouts ≠ []) :
    ∃ index ≤ trace.length,
      trace.firstReleaseEvery (roundInvocations principals serviceSlots).length
          (fun execution : runtime.messageApplication.PolicyExecution =>
            runtime.complete execution.native.application.visible) count =
        (trace.drop index).first ∧
      (trace.prefixThrough (fun execution : runtime.messageApplication.PolicyExecution =>
        !execution.native.application.visible.timeouts.isEmpty)).length ≤ index := by
  obtain ⟨index, hindex, hselected, _⟩ := trace.firstReleaseEvery_indexed
    (roundInvocations principals serviceSlots).length
    (fun execution => runtime.complete execution.native.application.visible) count
  refine ⟨index, hindex, hselected, ?_⟩
  apply trace.prefixThrough_length_le_of_drop_first _ index
  rw [← hselected]
  simpa using htimeout

/-- A bounded invocation schedule, before selecting its stopping boundary. -/
def roundSchedule (principals : List Principal) (serviceSlots : Nat) :
    Nat → List (@Invocation Principal)
  | 0 => []
  | count + 1 => roundInvocations principals serviceSlots ++
      roundSchedule principals serviceSlots count

omit [DecidableEq Principal] in
theorem roundSchedule_length (principals : List Principal) (serviceSlots count : Nat) :
    (roundSchedule principals serviceSlots count).length =
      count * (roundInvocations principals serviceSlots).length := by
  induction count with
  | zero => simp [roundSchedule]
  | succ count ih => simp only [roundSchedule, List.length_append, ih, Nat.succ_mul, Nat.add_comm]

omit [DecidableEq Principal] in
theorem roundSchedule_add (principals : List Principal) (serviceSlots left right : Nat) :
    roundSchedule principals serviceSlots (left + right) =
      roundSchedule principals serviceSlots left ++
        roundSchedule principals serviceSlots right := by
  induction left with
  | zero => simp only [Nat.zero_add, roundSchedule, List.nil_append]
  | succ left ih => simp only [Nat.succ_add, roundSchedule, ih, List.append_assoc]

omit [DecidableEq Principal] in
theorem roundSchedule_take (principals : List Principal) (serviceSlots total count : Nat)
    (hcount : count ≤ total) :
    (roundSchedule principals serviceSlots total).take
        (count * (roundInvocations principals serviceSlots).length) =
      roundSchedule principals serviceSlots count := by
  rw [← Nat.add_sub_of_le hcount,
    roundSchedule_add principals serviceSlots count (total - count),
    ← roundSchedule_length principals serviceSlots count, List.take_left]

omit [DecidableEq Principal] in
theorem roundSchedule_drop (principals : List Principal) (serviceSlots total count : Nat)
    (hcount : count ≤ total) :
    (roundSchedule principals serviceSlots total).drop
        (count * (roundInvocations principals serviceSlots).length) =
      roundSchedule principals serviceSlots (total - count) := by
  rw [← Nat.add_sub_of_le hcount,
    roundSchedule_add principals serviceSlots count (total - count),
    ← roundSchedule_length principals serviceSlots count, List.drop_left]
  simp

omit [DecidableEq Principal] in
/-- Roster membership supplies the same actual player invocation in every
recorded round. Repeated roster entries are permitted. -/
theorem roundSchedule_player (principals : List Principal) (serviceSlots total round slot : Nat)
    (who : Principal) (hround : round < total) (hslot : principals[slot]? = some who) :
    (roundSchedule principals serviceSlots total)[
      round * (roundInvocations principals serviceSlots).length + slot]? = some (.player who) := by
  rw [← List.getElem?_drop, roundSchedule_drop principals serviceSlots total round (by omega)]
  have hremaining : total - round = (total - round - 1) + 1 := by omega
  rw [hremaining, roundSchedule]
  have hslotLength : slot < principals.length := (List.getElem?_eq_some_iff.mp hslot).1
  have hblock : slot < (roundInvocations principals serviceSlots).length := by
    simp only [roundInvocations, List.length_append, List.length_map,
      List.length_replicate, List.length_singleton]
    omega
  have hservice : slot < (principals.map Invocation.player ++
      List.replicate serviceSlots Invocation.environment).length := by
    simp only [List.length_append, List.length_map, List.length_replicate]
    omega
  rw [List.getElem?_append_left hblock, roundInvocations,
    List.getElem?_append_left hservice,
    List.getElem?_append_left (by simpa only [List.length_map] using hslotLength),
    List.getElem?_map, hslot]
  rfl

/-- The clock phase uses only the environment's own invocation count. Wire
decisions still receive the complete real history and current observation. -/
def roundEnvironment (runtime : SealedResolution Principal Value) (serviceSlots : Nat)
    (wire : runtime.messageApplication.WirePolicy) : runtime.messageApplication.EnvironmentPolicy :=
  fun history view =>
    if history.length % (serviceSlots + 1) = serviceSlots
    then FinDist.pure (.application ⟨()⟩)
    else runtime.messageApplication.wireEnvironment wire history view

omit [DecidableEq Principal] in
private theorem service_invocations_count (principals : List Principal) (serviceSlots : Nat) :
    (principals.map Invocation.player ++ List.replicate serviceSlots Invocation.environment).countP
      Invocation.isEnvironment = serviceSlots := by
  simp [List.countP_replicate, Invocation.isEnvironment, Function.comp_def]

private theorem service_phase (start current slots : Nat)
    (hstart : start % (slots + 1) = 0) (hlo : start ≤ current)
    (hhi : current < start + slots) : current % (slots + 1) ≠ slots := by
  have heq : current = start + (current - start) := by omega
  have hlt : current - start < slots + 1 := by omega
  rw [heq, Nat.add_mod, hstart, Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt hlt]
  omega

/-- One round is exactly one invocation block. The phase premise holds at
initialization and is preserved at each successive round boundary. -/
theorem round_eq_runPolicies (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy)
    (execution : runtime.messageApplication.PolicyExecution)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0) :
    runtime.round principals serviceSlots players wire execution =
      runtime.messageApplication.runPolicies players (runtime.roundEnvironment serviceSlots wire)
        (roundInvocations principals serviceSlots) execution := by
  let app := runtime.messageApplication
  have hservice := app.runPolicies_environment_congr players
    (runtime.roundEnvironment serviceSlots wire) (app.wireEnvironment wire)
    (principals.map Invocation.player ++ List.replicate serviceSlots .environment) execution
    (fun history view hlo hhi => by
      rw [service_invocations_count] at hhi
      exact if_neg (service_phase _ _ _ hphase hlo hhi))
  rw [roundInvocations, app.runPolicies_append, hservice]
  unfold round
  apply FinDist.bind_congr
  intro next hnext
  have hlength := app.runPolicies_environmentHistory_length players (app.wireEnvironment wire)
    _ execution next hnext
  rw [service_invocations_count] at hlength
  have hclock : next.environmentHistory.length % (serviceSlots + 1) = serviceSlots := by
    rw [hlength, Nat.add_mod, hphase]
    simp
  simp only [runPolicies, invoke, roundEnvironment, hclock, ↓reduceIte,
    FinDist.pure_bind, FinDist.bind_pure]
  rfl

theorem round_environmentHistory_length (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy)
    (execution next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.round principals serviceSlots players wire execution).support) :
    next.environmentHistory.length = execution.environmentHistory.length + (serviceSlots + 1) := by
  simp only [round, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hlength := runtime.messageApplication.runPolicies_environmentHistory_length
    players (runtime.messageApplication.wireEnvironment wire) _ execution middle hmiddle
  rw [service_invocations_count] at hlength
  rw [runtime.messageApplication.environmentStep_history_length middle _ next hnext, hlength]
  omega

/-- The shared invocation trace advances the clock exactly once per complete
round. This counts recorded rounds before applying the stopping readout. -/
theorem runPolicies_roundSchedule_clock (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (count : Nat)
    (execution next : runtime.messageApplication.PolicyExecution)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players
      (runtime.roundEnvironment serviceSlots wire)
      (roundSchedule principals serviceSlots count) execution).support) :
    next.native.application.visible.clock = execution.native.application.visible.clock + count ∧
      next.environmentHistory.length = execution.environmentHistory.length +
        count * (serviceSlots + 1) := by
  induction count generalizing execution with
  | zero =>
      simp only [roundSchedule, runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      simp
  | succ count ih =>
      rw [roundSchedule, runtime.messageApplication.runPolicies_append] at hnext
      simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      rw [← runtime.round_eq_runPolicies principals serviceSlots players wire execution hphase]
        at hmiddle
      have hclock := runtime.round_clock principals serviceSlots players wire execution middle
        hmiddle
      have hhistory := runtime.round_environmentHistory_length principals serviceSlots players wire
        execution middle hmiddle
      have hmiddlePhase : middle.environmentHistory.length % (serviceSlots + 1) = 0 := by
        rw [hhistory, Nat.add_mod, hphase]
        simp
      have htail := ih middle hmiddlePhase hnext
      constructor
      · omega
      · rw [htail.2, hhistory, Nat.succ_mul]
        omega

/-- Every round-boundary snapshot of an actual shared trace has the expected
clock and environment phase, including boundaries before early stopping. -/
theorem tracePolicies_round_clock (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (total count : Nat)
    (execution : runtime.messageApplication.PolicyExecution)
    (trace : runtime.messageApplication.PolicyTrace)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (htrace : trace ∈ (runtime.messageApplication.tracePolicies players
      (runtime.roundEnvironment serviceSlots wire)
      (roundSchedule principals serviceSlots total) execution).support)
    (hcount : count ≤ total) :
    let boundary := (trace.drop (count * (roundInvocations principals serviceSlots).length)).first
    boundary.native.application.visible.clock = execution.native.application.visible.clock + count ∧
      boundary.environmentHistory.length = execution.environmentHistory.length +
        count * (serviceSlots + 1) := by
  have hprefix := (runtime.messageApplication.tracePolicies_drop_support players
    (runtime.roundEnvironment serviceSlots wire) (roundSchedule principals serviceSlots total)
    execution trace htrace (count * (roundInvocations principals serviceSlots).length)).1
  rw [roundSchedule_take principals serviceSlots total count hcount] at hprefix
  exact runtime.runPolicies_roundSchedule_clock principals serviceSlots players wire count
    execution _ hphase hprefix

/-- At a player poll within a recorded round, neither the clock nor the
environment-history phase has advanced beyond that round's boundary. -/
theorem tracePolicies_poll_clock (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (total round slot : Nat)
    (execution : runtime.messageApplication.PolicyExecution)
    (trace : runtime.messageApplication.PolicyTrace)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (htrace : trace ∈ (runtime.messageApplication.tracePolicies players
      (runtime.roundEnvironment serviceSlots wire)
      (roundSchedule principals serviceSlots total) execution).support)
    (hround : round < total) (hslot : slot < principals.length) :
    let poll := (trace.drop
      (round * (roundInvocations principals serviceSlots).length + slot)).first
    poll.native.application.visible.clock =
        execution.native.application.visible.clock + round ∧
      poll.environmentHistory.length = execution.environmentHistory.length +
        round * (serviceSlots + 1) := by
  let blockLength := (roundInvocations principals serviceSlots).length
  let boundaryIndex := round * blockLength
  let boundary := (trace.drop boundaryIndex).first
  let poll := (trace.drop (boundaryIndex + slot)).first
  have hboundary := runtime.tracePolicies_round_clock principals serviceSlots players wire
    total round execution trace hphase htrace (Nat.le_of_lt hround)
  change boundary.native.application.visible.clock =
      execution.native.application.visible.clock + round ∧
    boundary.environmentHistory.length = execution.environmentHistory.length +
      round * (serviceSlots + 1) at hboundary
  have hschedule :
      ((roundSchedule principals serviceSlots total).drop boundaryIndex).take slot =
        (principals.map Invocation.player).take slot := by
    dsimp only [boundaryIndex, blockLength]
    rw [roundSchedule_drop principals serviceSlots total round (Nat.le_of_lt hround)]
    have hremaining : total - round = (total - round - 1) + 1 := by omega
    rw [hremaining, roundSchedule]
    simp [roundInvocations, List.take_append_of_le_length,
      show slot ≤ principals.length by omega]
  have hplayersCount :
      ((principals.map Invocation.player).take slot).countP Invocation.isEnvironment = 0 := by
    rw [← List.map_take]
    generalize principals.take slot = xs
    induction xs with
    | nil => rfl
    | cons who rest ih => simp [Invocation.isEnvironment, ih]
  have hbetween := runtime.messageApplication.tracePolicies_between players
    (runtime.roundEnvironment serviceSlots wire)
    (roundSchedule principals serviceSlots total) execution trace htrace boundaryIndex slot
  rw [hschedule] at hbetween
  have hcongr := runtime.messageApplication.runPolicies_environment_congr players
    (runtime.roundEnvironment serviceSlots wire)
    (runtime.messageApplication.wireEnvironment wire)
    ((principals.map Invocation.player).take slot) boundary
    (fun _ _ hlo hhi => by
      rw [hplayersCount, Nat.add_zero] at hhi
      omega)
  rw [hcongr] at hbetween
  have hclock := runtime.runPolicies_wire_clock players wire
    ((principals.map Invocation.player).take slot) boundary poll hbetween
  have hhistory := runtime.messageApplication.runPolicies_environmentHistory_length players
    (runtime.messageApplication.wireEnvironment wire)
    ((principals.map Invocation.player).take slot) boundary poll hbetween
  change poll.native.application.visible.clock =
      execution.native.application.visible.clock + round ∧
    poll.environmentHistory.length = execution.environmentHistory.length +
      round * (serviceSlots + 1)
  constructor
  · exact hclock.trans hboundary.1
  · rw [hhistory]
    rw [hplayersCount, Nat.add_zero]
    exact hboundary.2

/-- Early stopping selects an actual round-boundary snapshot of the same
native run. The equality retains all private and public execution data, not
merely the completed application state. -/
theorem runRounds_eq_tracePolicies (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (wire : runtime.messageApplication.WirePolicy) (count : Nat)
    (execution : runtime.messageApplication.PolicyExecution)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0) :
    runtime.runRounds principals serviceSlots players wire count execution =
      (runtime.messageApplication.tracePolicies players (runtime.roundEnvironment serviceSlots wire)
        (roundSchedule principals serviceSlots count) execution).map
          (PolicyTrace.firstReleaseEvery (roundInvocations principals serviceSlots).length
            (fun state : runtime.messageApplication.PolicyExecution =>
              runtime.complete state.native.application.visible) count) := by
  induction count generalizing execution with
  | zero =>
      simp [runRounds, roundSchedule, tracePolicies,
        PolicyTrace.firstReleaseEvery, PolicyTrace.last]
  | succ count ih =>
      rw [roundSchedule, runtime.messageApplication.tracePolicies_firstReleaseEvery_block
        players (runtime.roundEnvironment serviceSlots wire) _ _ execution _ count
        (by simp [roundInvocations])]
      unfold runRounds
      split
      · rfl
      · rw [← runtime.round_eq_runPolicies principals serviceSlots players wire execution hphase]
        apply FinDist.bind_congr
        intro next hnext
        apply ih next
        rw [runtime.round_environmentHistory_length principals serviceSlots players wire
          execution next hnext, Nat.add_mod, hphase]
        simp

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runRounds_eq_tracePolicies' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runRounds_eq_tracePolicies
