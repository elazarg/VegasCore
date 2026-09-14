/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionDeadline
import Interaction.SealedResolutionPeriodicService

/-! # From bounded polling progress to deadline protection

The host supplies a clock, readiness provenance, and periodic inclusion capacity.
The only player-specific premise is completion after enough serviced polls of a
ready site. This theorem turns that premise into timeout exclusion on the actual
round trace. It is independent of the commitment service and the program language.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal]
variable {Service : Type (max uPrincipal uValue)}

/-- A bounded-poll completion law protects a site throughout the actual round
trace. The proof derives the poll positions, service checkpoints, and available
time from periodic capacity and the clock window; none is supplied for an
individual execution. Other players and unreserved wire choices are unrestricted. -/
theorem tracePolicies_no_timeout_of_periodic_service
    (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
      Option (ApplicationState Principal Value Service))
    (hrecords : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (wire : (runtime.host prepare applyMessage).WirePolicy) (reserved : Nat → Bool)
    (hservice : (runtime.host prepare applyMessage).InclusionService
      (fun turn => reserved turn = true) ((runtime.host prepare applyMessage).wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (((block + 1) * period - 1) * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (total : Nat) (hperiods : period ∣ total)
    (execution : (runtime.host prepare applyMessage).PolicyExecution)
    (trace : (runtime.host prepare applyMessage).PolicyTrace)
    (htrace : trace ∈ ((runtime.host prepare applyMessage).tracePolicies players
      ((runtime.hostRoundDriver prepare applyMessage).environmentPolicy serviceSlots wire)
      (roundSchedule principals serviceSlots total) execution).support)
    (hinitialClock : execution.native.application.visible.clock = 0)
    (hinitialHistory : execution.environmentHistory.length = 0)
    (hinitialEmpty : execution.native.pool.pending = [])
    (hinitialReady : execution.native.application.visible.ReadySound runtime)
    (hinitialDeadline : execution.native.application.visible.DeadlineSound runtime)
    (who : Principal) (target slot budget : Nat)
    (hslot : principals[slot]? = some who) (hwindow : budget + 2 ≤ runtime.window)
    (hcomplete : ∀ (position : Nat → Nat), StrictMono position →
      (∀ round < budget + 1, (roundSchedule principals serviceSlots total)[position round]? =
        some (.player who)) →
      (∃ rule, runtime.program.rules[target]? = some rule ∧
        rule.requires.all (trace.drop (position 0)).first.native.application.visible.completed =
          true) →
      (∀ round < budget + 1, ∃ checkpoint,
        position round + 1 ≤ checkpoint ∧ checkpoint ≤ position (round + period) ∧
        (runtime.complete (trace.drop checkpoint).first.native.application.visible = true ∨
          (trace.drop checkpoint).first.native.pool.pending = [])) →
      (trace.drop (position budget)).first.native.application.visible.completed target = true) :
    target ∉ trace.last.native.application.visible.timeouts := by
  let app := runtime.host prepare applyMessage
  let environment := (runtime.hostRoundDriver prepare applyMessage).environmentPolicy
    serviceSlots wire
  let schedule := roundSchedule principals serviceSlots total
  let width := (roundInvocations principals serviceSlots).length
  have hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0 := by
    rw [hinitialHistory, Nat.zero_mod]
  have hlast : (trace.drop (total * width)).first = trace.last := by
    have hlength := app.tracePolicies_length players environment schedule execution trace htrace
    rw [roundSchedule_length] at hlength
    rw [← hlength, PolicyTrace.drop_length]
    rfl
  have hrun := (app.tracePolicies_drop_support players environment schedule execution trace
    htrace (total * width)).1
  rw [hlast] at hrun
  have hsound := runtime.runPolicies_deadlineSound prepare applyMessage hrecords players
    environment (schedule.take (total * width)) execution trace.last hinitialDeadline hrun
  have hfinalClock := (runtime.tracePolicies_round_clock prepare applyMessage hrecords
    principals serviceSlots players wire total total execution trace hphase htrace le_rfl).1
  rw [hlast, hinitialClock, Nat.zero_add] at hfinalClock
  intro htimeout
  obtain ⟨rule, timestamp, hrule, hstampFinal, hexpired, hrequires⟩ := hsound target htimeout
  rw [hfinalClock] at hexpired
  let position := fun round => (timestamp + 1 + round) * width + slot
  have hslotLength : slot < principals.length := (List.getElem?_eq_some_iff.mp hslot).1
  have hwidth : 0 < width := by simp [width, roundInvocations]
  have hslotWidth : slot < width := by
    dsimp [width, roundInvocations]
    simp only [List.length_append, List.length_map, List.length_replicate, List.length_singleton]
    omega
  have hposition : StrictMono position := by
    intro left right hlt
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right (by omega) hwidth) slot
  have hwithin : ∀ round < budget + 1, timestamp + 1 + round < total := by
    intro round hround
    omega
  have hpollClock : ∀ round < budget + 1,
      (trace.drop (position round)).first.native.application.visible.clock =
        timestamp + 1 + round := by
    intro round hround
    have hclock := (runtime.tracePolicies_poll_clock prepare applyMessage hrecords
      principals serviceSlots players wire total (timestamp + 1 + round) slot execution trace
      hphase htrace (hwithin round hround) hslotLength).1
    simpa only [hinitialClock, Nat.zero_add] using hclock
  have hfirstLe : position 0 ≤ total * width := by
    have hbound := Nat.mul_le_mul_right width (hwithin 0 (by omega))
    rw [Nat.succ_mul] at hbound
    dsimp [position]
    omega
  have hsuffix := app.tracePolicies_between players environment schedule execution trace htrace
    (position 0) (total * width - position 0)
  rw [Nat.add_sub_of_le hfirstLe, hlast] at hsuffix
  have hstamp := runtime.runPolicies_firstReady?_of_lt_clock prepare applyMessage hrecords
    players environment ((schedule.drop (position 0)).take (total * width - position 0))
    (trace.drop (position 0)).first trace.last target timestamp hsuffix hstampFinal
    (by rw [hpollClock 0 (by omega)]; omega)
  have hprefix := (app.tracePolicies_drop_support players environment schedule execution trace
    htrace (position 0)).1
  have hready := runtime.runPolicies_readySound prepare applyMessage hrecords players
    environment (schedule.take (position 0)) execution (trace.drop (position 0)).first
    hinitialReady hprefix
  have hcompleted := hcomplete position hposition
    (fun round hround => roundSchedule_player principals serviceSlots total
      (timestamp + 1 + round) slot who (hwithin round hround) hslot)
    (hready target timestamp hstamp)
    (fun round hround => by
      obtain ⟨checkpoint, hafter, hbefore, hempty⟩ := runtime.tracePolicies_periodic_service
        prepare applyMessage hrecords principals serviceSlots players wire total execution trace
        hphase htrace reserved hservice period hperiod (by
          simpa only [hinitialHistory, Nat.zero_add] using hcapacity)
        hinitialEmpty hperiods (timestamp + 1 + round) slot (hwithin round hround) hslotLength
      refine ⟨checkpoint, hafter, ?_, Or.inr hempty⟩
      simpa only [position, Nat.add_assoc] using hbefore)
  have hclear := runtime.tracePolicies_no_timeout_of_timely_completion prepare applyMessage
    hrecords players environment schedule execution trace hinitialDeadline htrace target
    (position 0) (position budget) (total * width) (hposition.monotone (Nat.zero_le budget))
    (by
      have hbound := Nat.mul_le_mul_right width (hwithin budget (Nat.lt_succ_self budget))
      rw [Nat.succ_mul] at hbound
      dsimp [position]
      omega)
    timestamp hstamp hcompleted (by rw [hpollClock budget (by omega)]; omega)
  rw [hlast] at hclear
  exact hclear htimeout

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.tracePolicies_no_timeout_of_periodic_service'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.tracePolicies_no_timeout_of_periodic_service
