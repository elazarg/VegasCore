/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastRecordedEmission
import Vegas.Examples.CommitSeedBroadcastOriginalSilentFailure
import Vegas.Pending.PhaseSeedEmissionUnique

/-! # A first declaration in the bad clock-two slot loses its original binding -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Count legality makes the actual clock-two packet the sole original packet;
the bad owner's eligible clock three and clock zero are therefore absent. -/
theorem bad_clock_two_record_unaccepted (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (bad : seed.2 owner = false)
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner))
    (material : WitnessedSubmission graph) (sent : entry.action.transmission = some material)
    (clock : entry.beforeView.application.2.native.clock = 2) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner execution := by
  classical
  have emittedClock := original_recorded_transmission_clock seed remaining execution trace owner
    entry recorded requested material sent 2 clock
  obtain ⟨packet, member, tick⟩ := List.mem_map.mp emittedClock
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seed) remaining execution trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds (family seed)).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have unique := app.input_identifier_injective_history initial horizon (family seed)
    ⟨remaining, none, execution⟩ raw
  have singleton := PhaseSeedScheduler.localInput_emissions_eq_singleton runtime leaks execution
    (originalCoordinate owner) owner words clean
      (fun first firstInput second secondInput equal =>
        unique first second firstInput secondInput equal) packet.1 packet.2 member
  have clocks : PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner) owner
      execution = [2] := by
    rw [PhaseService.bindingEmissionClocks, singleton, List.map_cons, List.map_nil, tick]
  intro accepted
  have compiled := raw
  rw [initial_eq_compiled] at compiled
  have resolved := PhaseService.bindingAccepted_resolved runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seed) compiled (originalCoordinate owner)
      owner accepted
  have alternatives := (original_binding_accepted_iff_clocks seed _ trace owner resolved).mp
    accepted
  rw [clocks, bad] at alternatives
  norm_num [lateClock] at alternatives

/-- The final audited native payoff is exactly the fixed exclusion loss. -/
theorem bad_clock_two_record_terminal_payoff (seed : Seeds) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, execution⟩))
    (owner : Player) (bad : seed.2 owner = false)
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner))
    (material : WitnessedSubmission graph) (sent : entry.action.transmission = some material)
    (clock : entry.beforeView.application.2.native.clock = 2) :
    netPayoff (app.finished execution) owner = -(3 / 2) := by
  have missing := bad_clock_two_record_unaccepted seed 0 execution trace owner bad entry recorded
    requested material sent clock
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have accounted := app.raw_trace_horizon initial horizon (family seed) raw
  change execution.environmentRecall.length + 0 = 128 at accounted
  have retired := original_attempt_retired seed ⟨0, none, execution⟩ raw (by
    change 30 ≤ execution.environmentRecall.length
    omega)
  have excluded : owner ∈ execution.application.current.excluded := by
    by_contra survives
    exact missing ((survivor_original_receipt_or_open (family seed) ⟨0, none, execution⟩ raw owner
      survives).resolve_left retired)
  rw [counted_fixed_endpoint_payoff seed execution trace owner, ite_eq_left excluded]

end Vegas.Examples.CommitSeedBroadcast
