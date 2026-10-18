/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastKnownEligibleContinuation
import Vegas.Examples.CommitSeedBroadcastNativeTimingWait

/-! # Actual terminal loss after all original transmission opportunities are omitted -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Omitting clock zero and the original seed's eligible late opportunity
precludes every accepting original receipt at the same actual endpoint. -/
theorem original_eligible_binding_waits_unaccepted (seed : Seeds) (current : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (first last : app.PlayerEntry)
    (firstMember : first ∈ current.execution.recall owner)
    (lastMember : last ∈ current.execution.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (lastRequest : PhaseRuntimeState.requests last.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstSilent : first.action.transmission = none)
    (lastSilent : last.action.transmission = none)
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (lastClock : last.beforeView.application.2.native.clock = lateClock (seed.2 owner)) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      current.execution := by
  have missingZero := original_recorded_wait_no_emission countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) seed current trace owner first firstMember
      firstRequest firstSilent 0 firstClock
  have missingLate := original_recorded_wait_no_emission countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) seed current trace owner last lastMember
      lastRequest lastSilent (lateClock (seed.2 owner)) lastClock
  intro accepted
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  rw [initial_eq_compiled] at raw
  have resolved := PhaseService.bindingAccepted_resolved runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seed) raw
      (originalCoordinate owner) owner accepted
  exact ((original_binding_accepted_iff_clocks seed current trace owner resolved).mp accepted).elim
    missingZero missingLate

/-- The native completed endpoint pays the fixed exclusion loss after both
eligible transmissions were omitted, regardless of opponents' preparations. -/
theorem counted_eligible_waits_terminal_payoff (seed : Seeds) (after : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, after⟩)) (owner : Player) (first last : app.PlayerEntry)
    (firstMember : first ∈ after.recall owner) (lastMember : last ∈ after.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (lastRequest : PhaseRuntimeState.requests last.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstSilent : first.action.transmission = none)
    (lastSilent : last.action.transmission = none)
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (lastClock : last.beforeView.application.2.native.clock = lateClock (seed.2 owner)) :
    netPayoff (app.finished after) owner = -(3 / 2) := by
  have missing := original_eligible_binding_waits_unaccepted seed ⟨0, none, after⟩ trace owner
    first last firstMember lastMember firstRequest lastRequest firstSilent lastSilent
      firstClock lastClock
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have accounted := app.raw_trace_horizon initial horizon (family seed) raw
  change after.environmentRecall.length + 0 = 128 at accounted
  have enough : 30 ≤ after.environmentRecall.length := by omega
  have retired := original_attempt_retired seed ⟨0, none, after⟩ raw enough
  have excluded : owner ∈ after.application.current.excluded := by
    by_contra survives
    exact missing ((survivor_original_receipt_or_open (family seed) ⟨0, none, after⟩ raw owner
      survives).resolve_left retired)
  rw [counted_fixed_endpoint_payoff seed after trace owner, ite_eq_left excluded]

/-- The entire fixed-seed continuation has the exclusion value when all
three original response clocks are already recorded as WAIT. -/
theorem counted_all_original_waits_fixed_finish_value
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩)) (owner : Player)
    (entries : Fin 3 → app.PlayerEntry)
    (recorded : ∀ index, entries index ∈ execution.recall owner)
    (requested : ∀ index, PhaseRuntimeState.requests (entries index).beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : ∀ index, (entries index).action.transmission = none)
    (clocks : ∀ index, (entries index).beforeView.application.2.native.clock =
      ([0, 2, 3] : List Nat)[index.val])
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view) :
    expect (app.finish initial horizon (family seed) players
      (some ⟨remaining, none, execution⟩)) (fun state => netPayoff state owner) = -(3 / 2) := by
  rw [← expect_constant (app.finish initial horizon (family seed) players
    (some ⟨remaining, none, execution⟩)) (-(3 / 2 : ℝ))]
  apply expect_congr_on_support
  intro state reached
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] at reached
  obtain ⟨after, continued, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining execution after (by simpa only [Nat.zero_add] using trace) continued
  let retained : app.PolicyInvariant players (fun current =>
      ∀ index, entries index ∈ current.recall owner) := {
    respond := fun before actor action valid _ index =>
      app.respond_recall_mono before actor owner action (valid index)
    environment := fun before next command valid moved => by
      rw [app.environmentStep_recall before next command moved]
      exact valid }
  have kept := retained.runRounds (family seed) remaining execution after recorded continued
  cases good : seed.2 owner with
  | false =>
      exact counted_eligible_waits_terminal_payoff seed after finalTrace owner (entries 0)
        (entries 2) (kept 0) (kept 2) (requested 0) (requested 2) (silent 0) (silent 2)
          (clocks 0) (by simpa [good, lateClock] using clocks 2)
  | true =>
      exact counted_eligible_waits_terminal_payoff seed after finalTrace owner (entries 0)
        (entries 1) (kept 0) (kept 1) (requested 0) (requested 1) (silent 0) (silent 1)
          (clocks 0) (by simpa [good, lateClock] using clocks 1)

end Vegas.Examples.CommitSeedBroadcast
