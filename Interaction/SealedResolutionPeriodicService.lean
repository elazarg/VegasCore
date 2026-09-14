/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionService

/-! # Periodic queue drainage on actual resolving-runtime traces

Reserved inclusion capacity at the end of each block of rounds empties the
queue at every block boundary, not just the first one. Arbitrary traffic in
earlier rounds may be delivered to players before inclusion. The invariant
accounts for the backlog when deriving a sliding service bound for each poll.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal]

section TraceService

variable {Service : Type (max uPrincipal uValue)}
variable (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
      Option (ApplicationState Principal Value Service))

variable (hrecords : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (wire : (runtime.host prepare applyMessage).WirePolicy) (total : Nat)
    (execution : (runtime.host prepare applyMessage).PolicyExecution)
    (trace : (runtime.host prepare applyMessage).PolicyTrace)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0)
    (htrace : trace ∈ ((runtime.host prepare applyMessage).tracePolicies players
      ((runtime.hostRoundDriver prepare applyMessage).environmentPolicy serviceSlots wire)
      (roundSchedule principals serviceSlots total) execution).support)

include hrecords hphase htrace

/-- The queue recurrence holds at adjacent boundaries of the same recorded
execution, with reservations indexed by its actual environment history. -/
theorem tracePolicies_round_pending_bound (reserved : Nat → Bool)
    (hservice : (runtime.host prepare applyMessage).InclusionService
      (fun turn => reserved turn = true) ((runtime.host prepare applyMessage).wireEnvironment wire))
    (round : Nat) (hround : round < total) :
    let boundary := fun count =>
      (trace.drop (count * (roundInvocations principals serviceSlots).length)).first
    (boundary (round + 1)).native.pool.pending.length ≤
      (boundary round).native.pool.pending.length + principals.length -
        (List.range' (execution.environmentHistory.length + round * (serviceSlots + 1))
          serviceSlots).countP reserved := by
  let width := (roundInvocations principals serviceSlots).length
  let before := (trace.drop (round * width)).first
  let after := (trace.drop ((round + 1) * width)).first
  have hbetween := (runtime.host prepare applyMessage).tracePolicies_between players
    ((runtime.hostRoundDriver prepare applyMessage).environmentPolicy serviceSlots wire)
      (roundSchedule principals
      serviceSlots total)
    execution trace htrace (round * width) width
  rw [show round * width + width = (round + 1) * width by
    rw [Nat.add_mul, Nat.one_mul]] at hbetween
  have hschedule : ((roundSchedule principals serviceSlots total).drop (round * width)).take
      width = roundInvocations principals serviceSlots := by
    rw [roundSchedule_drop principals serviceSlots total round (by omega)]
    simpa only [Nat.one_mul, roundSchedule, List.append_nil] using
      roundSchedule_take principals serviceSlots (total - round) 1 (by omega)
  rw [hschedule] at hbetween
  have hhistory := (runtime.tracePolicies_round_clock prepare applyMessage hrecords principals
    serviceSlots players wire total
    round execution trace hphase htrace (by omega)).2
  change before.environmentHistory.length =
    execution.environmentHistory.length + round * (serviceSlots + 1) at hhistory
  have hbeforePhase : before.environmentHistory.length % (serviceSlots + 1) = 0 := by
    rw [hhistory, Nat.add_mod, hphase]
    simp
  rw [← (runtime.hostRoundDriver prepare applyMessage).round_eq_runPolicies principals
    serviceSlots players wire before
    hbeforePhase]
    at hbetween
  have hbound := runtime.round_pending_bound prepare applyMessage principals serviceSlots players
    wire reserved hservice
    before after hbetween
  rw [hhistory] at hbound
  exact hbound

/-- Between any two round boundaries, player opportunities bound new pending
arrivals even when none of the intervening wire slots are reserved. -/
theorem tracePolicies_pending_growth (start count : Nat) (hcount : start + count ≤ total) :
    let boundary := fun round =>
      (trace.drop (round * (roundInvocations principals serviceSlots).length)).first
    (boundary (start + count)).native.pool.pending.length ≤
      (boundary start).native.pool.pending.length + count * principals.length := by
  induction count with
  | zero => simp
  | succ count ih =>
      have hprior := ih (by omega)
      have hstep := runtime.tracePolicies_round_pending_bound prepare applyMessage hrecords
        principals serviceSlots players wire
        total execution trace hphase htrace (fun _ => false) (by intro _ _ _ h; cases h)
        (start + count) (by omega)
      simp at hstep
      dsimp only at hprior hstep ⊢
      simp only [Nat.add_assoc] at hstep
      simp only [Nat.succ_mul]
      omega

/-- Every block ends with an empty queue when its last wire phase reserves
capacity for all of that block's player opportunities. The induction retains
empty earlier drain boundaries, discharging the backlog premise at each block. -/
theorem tracePolicies_periodic_pending_empty (reserved : Nat → Bool)
    (hservice : (runtime.host prepare applyMessage).InclusionService
      (fun turn => reserved turn = true) ((runtime.host prepare applyMessage).wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (execution.environmentHistory.length +
        ((block + 1) * period - 1) * (serviceSlots + 1)) serviceSlots).countP reserved)
    (hempty : execution.native.pool.pending = [])
    (blocks : Nat) (hblocks : blocks * period ≤ total) :
    let boundary :=
      (trace.drop (blocks * period * (roundInvocations principals serviceSlots).length)).first
    boundary.native.pool.pending = [] := by
  induction blocks with
  | zero =>
      have hfirst := (runtime.host prepare applyMessage).tracePolicies_first players
        ((runtime.hostRoundDriver prepare applyMessage).environmentPolicy serviceSlots wire)
          (roundSchedule principals
          serviceSlots total)
        execution trace htrace
      simpa only [Nat.zero_mul, PolicyTrace.drop, hfirst] using hempty
  | succ blocks ih =>
      have hprior := ih (by rw [Nat.succ_mul] at hblocks; omega)
      have hgrowth := runtime.tracePolicies_pending_growth prepare applyMessage hrecords
        principals serviceSlots players wire
        total execution trace hphase htrace (blocks * period) (period - 1) (by
          rw [Nat.succ_mul] at hblocks
          omega)
      have hstep := runtime.tracePolicies_round_pending_bound prepare applyMessage hrecords
        principals serviceSlots players wire
        total execution trace hphase htrace reserved hservice ((blocks + 1) * period - 1) (by
          rw [Nat.succ_mul] at hblocks
          rw [Nat.add_mul]
          omega)
      have hlast : blocks * period + (period - 1) = (blocks + 1) * period - 1 := by
        rw [Nat.add_mul]
        omega
      have hnext : (blocks + 1) * period - 1 + 1 = (blocks + 1) * period := by
        rw [Nat.add_mul]
        omega
      dsimp only at hgrowth hstep hprior ⊢
      rw [hlast, hprior, List.length_nil, Nat.zero_add] at hgrowth
      rw [hnext] at hstep
      have hcap := hcapacity blocks
      have harrivals : (period - 1) * principals.length + principals.length =
          period * principals.length := by
        rw [← Nat.succ_mul, show (period - 1).succ = period by omega]
      have hzero : (trace.drop ((blocks + 1) * period *
          (roundInvocations principals serviceSlots).length)).first.native.pool.pending.length =
          0 := by omega
      simpa using hzero

/-- Each actual roster poll reaches a drained queue within one service period.
The trace horizon contains whole periods so the selected drain is a real
recorded boundary, even when the poll is near the end of the horizon. -/
theorem tracePolicies_periodic_service (reserved : Nat → Bool)
    (hservice : (runtime.host prepare applyMessage).InclusionService
      (fun turn => reserved turn = true) ((runtime.host prepare applyMessage).wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (execution.environmentHistory.length +
        ((block + 1) * period - 1) * (serviceSlots + 1)) serviceSlots).countP reserved)
    (hempty : execution.native.pool.pending = [])
    (hperiods : period ∣ total) (round slot : Nat)
    (hround : round < total) (hslot : slot < principals.length) :
    let width := (roundInvocations principals serviceSlots).length
    ∃ checkpoint, round * width + slot + 1 ≤ checkpoint ∧
      checkpoint ≤ (round + period) * width + slot ∧
      (trace.drop checkpoint).first.native.pool.pending = [] := by
  let width := (roundInvocations principals serviceSlots).length
  let blocks := round / period + 1
  have hnext : round < blocks * period := by
    have hdivision := Nat.div_add_mod round period
    rw [Nat.mul_comm period (round / period)] at hdivision
    have hmod := Nat.mod_lt round hperiod
    dsimp [blocks]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hupper : blocks * period ≤ round + period := by
    have hdivision := Nat.div_add_mod round period
    rw [Nat.mul_comm period (round / period)] at hdivision
    dsimp [blocks]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hblocks : blocks * period ≤ total := by
    obtain ⟨whole, hwhole⟩ := hperiods
    have hquotient : round / period < whole := by
      apply (Nat.div_lt_iff_lt_mul hperiod).mpr
      simpa only [hwhole, Nat.mul_comm] using hround
    rw [hwhole, Nat.mul_comm period whole]
    exact Nat.mul_le_mul_right period (by dsimp [blocks]; omega)
  have hdrained := runtime.tracePolicies_periodic_pending_empty prepare applyMessage hrecords
    principals serviceSlots players
    wire total execution trace hphase htrace reserved hservice period hperiod hcapacity hempty
    blocks hblocks
  refine ⟨blocks * period * width, ?_, ?_, hdrained⟩
  · change round * width + slot + 1 ≤ blocks * period * width
    have hslotWidth : slot + 1 ≤ width := by
      dsimp [width, roundInvocations]
      simp only [List.length_append, List.length_map, List.length_replicate, List.length_singleton]
      omega
    have hbound := Nat.mul_le_mul_right width hnext
    rw [Nat.succ_mul] at hbound
    omega
  · exact (Nat.mul_le_mul_right width hupper).trans (Nat.le_add_right _ _)

end TraceService

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.tracePolicies_periodic_pending_empty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.tracePolicies_periodic_pending_empty

/-- info: 'Interaction.SealedResolution.tracePolicies_periodic_service' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.tracePolicies_periodic_service
