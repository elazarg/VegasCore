/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalRecordedOmission
import Vegas.Examples.CommitSeedBroadcastOriginalReceipts
import Vegas.Examples.CommitSeedBroadcastPayoffs
import Vegas.Examples.CommitSeedBroadcastAsyncService

/-! # Actual terminal loss after a silent good-seed late opportunity -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

/-- The actual completed trace has excluded an owner who omitted both of its
good seed's eligible original opportunities. Opposing policies are unrestricted. -/
theorem counted_good_waits_terminal_excluded
    (seed : Seeds) (after : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, after⟩)) (owner : Player)
    (first last : app.PlayerEntry)
    (firstMember : first ∈ after.recall owner) (lastMember : last ∈ after.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (lastRequest : PhaseRuntimeState.requests last.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstSilent : first.action.transmission = none)
    (lastSilent : last.action.transmission = none)
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (lastClock : last.beforeView.application.2.native.clock = 2)
    (good : seed.2 owner = true) : owner ∈ after.application.current.excluded := by
  classical
  by_contra active
  have missing := original_good_binding_waits_unaccepted seed ⟨0, none, after⟩ trace owner good
    first last firstMember lastMember firstRequest lastRequest firstSilent lastSilent
      firstClock lastClock
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have accounted := app.raw_trace_horizon initial horizon (family seed) raw
  change after.environmentRecall.length + 0 = 128 at accounted
  have retired := original_attempt_retired seed ⟨0, none, after⟩ raw (by
    change 30 ≤ after.environmentRecall.length
    omega)
  have accepted := (survivor_original_receipt_or_open (family seed) ⟨0, none, after⟩ raw owner
    active).resolve_left retired
  exact missing accepted

/-- Counted continuation incurs exactly the fixed exclusion payoff on the
good-seed omitted-opportunity branch, with the real terminal readout and zero audit charge. -/
theorem counted_good_waits_terminal_payoff
    (seed : Seeds) (after : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, after⟩)) (owner : Player)
    (first last : app.PlayerEntry)
    (firstMember : first ∈ after.recall owner) (lastMember : last ∈ after.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (lastRequest : PhaseRuntimeState.requests last.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstSilent : first.action.transmission = none)
    (lastSilent : last.action.transmission = none)
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (lastClock : last.beforeView.application.2.native.clock = 2)
    (good : seed.2 owner = true) : netPayoff (app.finished after) owner = -(3 / 2) := by
  have excluded := counted_good_waits_terminal_excluded seed after trace owner first last
    firstMember lastMember firstRequest lastRequest firstSilent lastSilent firstClock lastClock good
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have completed := family_completesPlay seed ⟨0, none, after⟩ raw ⟨rfl, rfl⟩
  have zero := PhaseCount.onePacketMenu_countCharge_zero runtime leaks bounds initial horizon
    (family seed) evidenceService ⟨some ⟨0, none, after⟩, trace⟩ owner
  change TerminalAudit.charge app.stateTraffic audit (some ⟨0, none, after⟩) owner = 0 at zero
  change basePayoff (some ⟨0, none, after⟩) owner -
    TerminalAudit.charge app.stateTraffic audit (some ⟨0, none, after⟩) owner * deposit owner = _
  rw [zero, zero_mul, sub_zero, basePayoff_terminal_formula ⟨0, none, after⟩ completed owner,
    ite_eq_left excluded]

/-- The same actual endpoint satisfies the affine bad-seed upper bound used
in the timing comparison. The good branch is a loss; the bad branch is bounded by one. -/
theorem counted_waits_terminal_payoff_upper
    (seed : Seeds) (after : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, after⟩)) (owner : Player)
    (first last : app.PlayerEntry)
    (firstMember : first ∈ after.recall owner) (lastMember : last ∈ after.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (lastRequest : PhaseRuntimeState.requests last.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstSilent : first.action.transmission = none)
    (lastSilent : last.action.transmission = none)
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (lastClock : last.beforeView.application.2.native.clock = 2)
    : netPayoff (app.finished after) owner ≤
      (5 / 2 : ℝ) * (if seed.2 owner = false then 1 else 0) - 3 / 2 := by
  cases good : seed.2 owner with
  | false =>
      have upper := (netPayoff_mem_Icc (app.finished after) owner).2
      norm_num only [good, ite_true, mul_one]
      exact upper
  | true =>
      rw [counted_good_waits_terminal_payoff seed after trace owner first last firstMember
        lastMember firstRequest lastRequest firstSilent lastSilent firstClock lastClock good]
      norm_num [good]

end Vegas.Examples.CommitSeedBroadcast
