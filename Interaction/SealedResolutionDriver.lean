/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionRounds
import Interaction.MessageApplicationRoundTrace

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
variable [DecidableEq Principal]

/-- A principal's actual private history and current observation at the first
timeout, or at the end of the trace when no timeout occurs. On timeout-free
traces this terminal information is intentionally arbitrary for consumers
whose timeout branch is inactive. -/
def firstTimeoutLocalInfo [DecidableEq Value] (runtime : SealedResolution Principal Value)
    (principal : Principal) (trace : runtime.messageApplication.PolicyTrace) :
    List runtime.messageApplication.PlayerEntry × runtime.messageApplication.View :=
  let stop : runtime.messageApplication.PolicyExecution → Bool := fun execution =>
    !execution.native.application.visible.timeouts.isEmpty
  let stopped := trace.prefixThrough stop
  (stopped.last.principalHistory principal,
    State.observe runtime.messageApplication stopped.last.native principal)

/-- If the completed-round readout contains a timeout, the information used
by `firstTimeoutLocalInfo` comes from at or before that readout, never from
the unused full-trace suffix. No assertion identifies this checkpoint with
the principal's last opportunity to act before the deadline. -/
theorem firstTimeout_before_roundReadout [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
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

variable {Service : Type (max uPrincipal uValue)}
variable (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
      Option (ApplicationState Principal Value Service))

/-- The shared invocation trace advances the clock exactly once per complete
round. This counts recorded rounds before applying the stopping readout. -/
theorem runPolicies_roundSchedule_clock
    (hrecords : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (wire : (runtime.host prepare applyMessage).WirePolicy) (count : Nat)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (hnext : next ∈ ((runtime.host prepare applyMessage).runPolicies players
      ((runtime.hostRoundDriver prepare applyMessage).environmentPolicy serviceSlots wire)
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
      rw [roundSchedule, (runtime.host prepare applyMessage).runPolicies_append] at hnext
      simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      rw [← (runtime.hostRoundDriver prepare applyMessage).round_eq_runPolicies principals
        serviceSlots players wire
        execution hphase]
        at hmiddle
      have hclock := runtime.round_clock prepare applyMessage hrecords principals serviceSlots
        players wire execution middle
        hmiddle
      have hhistory := (runtime.hostRoundDriver prepare
        applyMessage).round_environmentHistory_length principals
        serviceSlots players wire
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
theorem tracePolicies_round_clock
    (hrecords : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (wire : (runtime.host prepare applyMessage).WirePolicy) (total count : Nat)
    (execution : (runtime.host prepare applyMessage).PolicyExecution)
    (trace : (runtime.host prepare applyMessage).PolicyTrace)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (htrace : trace ∈ ((runtime.host prepare applyMessage).tracePolicies players
      ((runtime.hostRoundDriver prepare applyMessage).environmentPolicy serviceSlots wire)
      (roundSchedule principals serviceSlots total) execution).support)
    (hcount : count ≤ total) :
    let boundary := (trace.drop (count * (roundInvocations principals serviceSlots).length)).first
    boundary.native.application.visible.clock = execution.native.application.visible.clock + count ∧
      boundary.environmentHistory.length = execution.environmentHistory.length +
        count * (serviceSlots + 1) := by
  have hprefix := ((runtime.host prepare applyMessage).tracePolicies_drop_support players
    ((runtime.hostRoundDriver prepare applyMessage).environmentPolicy serviceSlots wire)
      (roundSchedule principals
      serviceSlots total)
    execution trace htrace (count * (roundInvocations principals serviceSlots).length)).1
  rw [roundSchedule_take principals serviceSlots total count hcount] at hprefix
  exact runtime.runPolicies_roundSchedule_clock prepare applyMessage hrecords principals
    serviceSlots players wire count
    execution _ hphase hprefix

/-- At a player poll within a recorded round, neither the clock nor the
environment-history phase has advanced beyond that round's boundary. -/
theorem tracePolicies_poll_clock
    (hrecords : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (wire : (runtime.host prepare applyMessage).WirePolicy) (total round slot : Nat)
    (execution : (runtime.host prepare applyMessage).PolicyExecution)
    (trace : (runtime.host prepare applyMessage).PolicyTrace)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (htrace : trace ∈ ((runtime.host prepare applyMessage).tracePolicies players
      ((runtime.hostRoundDriver prepare applyMessage).environmentPolicy serviceSlots wire)
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
  have hboundary := runtime.tracePolicies_round_clock prepare applyMessage hrecords principals
    serviceSlots players wire
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
  have hbetween := (runtime.host prepare applyMessage).tracePolicies_between players
    ((runtime.hostRoundDriver prepare applyMessage).environmentPolicy serviceSlots wire)
    (roundSchedule principals serviceSlots total) execution trace htrace boundaryIndex slot
  rw [hschedule] at hbetween
  have hcongr := (runtime.host prepare applyMessage).runPolicies_environment_congr players
    ((runtime.hostRoundDriver prepare applyMessage).environmentPolicy serviceSlots wire)
    ((runtime.host prepare applyMessage).wireEnvironment wire)
    ((principals.map Invocation.player).take slot) boundary
    (fun _ _ hlo hhi => by
      rw [hplayersCount, Nat.add_zero] at hhi
      omega)
  rw [hcongr] at hbetween
  have hclock := runtime.runPolicies_wire_clock prepare applyMessage hrecords players wire
    ((principals.map Invocation.player).take slot) boundary poll hbetween
  have hhistory := (runtime.host prepare applyMessage).runPolicies_environmentHistory_length players
    ((runtime.host prepare applyMessage).wireEnvironment wire)
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

end Interaction.SealedResolution
