/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastBadFirstLatePackets
import Vegas.Examples.CommitSeedBroadcastOriginalZeroSnapshot
import Vegas.Examples.CommitSeedBroadcastOriginalBindingWord
import Vegas.Examples.CommitSeedBroadcastCountedInformation
import Interaction.ReactiveRecordedResponse

/-! # Original accepting receipts and the retained initial packet word -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- A remembered physical clock is the same in both components of the actual
local application observation. No equality between arbitrary views is assumed. -/
theorem recorded_private_clock (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (clock : Nat) (physical : entry.beforeView.application.2.native.clock = clock) :
    entry.beforeView.application.1.publicView.clock = clock := by
  obtain ⟨before, _prior, _kept, _active, viewed, _offered, _later, _recalled⟩ :=
    countedMenu.recorded_response_prefix initial horizon (family seed) _ trace owner entry recorded
  rw [viewed] at physical ⊢
  exact physical

/-- Any original initial transmission is present in the immutable public
clock-zero packet word, retaining its actual evidence and hidden preparation. -/
theorem initial_record_transmission_packets_nonempty (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner))
    (clock : entry.beforeView.application.2.native.clock = 0)
    (material : WitnessedSubmission graph) (sent : entry.action.transmission = some material)
    (past : 4 ≤ execution.environmentRecall.length) : initialPublicPackets execution ≠ ∅ := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  obtain ⟨message, emitted, _authored, _named⟩ := PhaseCount.recalled_submission_emitted runtime
    leaks initial horizon (family seed) raw owner entry recorded material sent
  obtain ⟨snapshot, selected, input⟩ := raw_clock_zero_packet_in_snapshot seed _ raw owner entry
    recorded message emitted requested.1.symm
      (recorded_private_clock seed remaining execution trace owner entry recorded 0 clock) past
  have packets : initialPublicPackets execution = snapshot.beforeView.network.inputs.toFinset := by
    simp only [initialPublicPackets, selected, Option.map_some, Option.getD_some]
  intro empty
  have present : message ∈ initialPublicPackets execution := by
    rw [packets]
    exact List.mem_toFinset.mpr input
  rw [empty] at present
  exact Finset.notMem_empty _ present

/-- An original receipt requires an actually authored own packet. This applies
at arbitrary original or later counted prefixes, without a preparation premise. -/
theorem outputs_empty_original_unaccepted (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩)) (owner : Player)
    (empty : app.outputs (execution.recall owner) = []) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner execution := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seed) remaining execution trace
  have recalled := app.history_inputRecall initial horizon (family seed) raw
  intro accepted
  have compiled := raw
  rw [initial_eq_compiled] at compiled
  have resolved := PhaseService.bindingAccepted_resolved runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seed) compiled (originalCoordinate owner)
      owner accepted
  have clocks := (original_binding_accepted_iff_clocks seed _ trace owner resolved).mp accepted
  have impossible (tick : Nat)
      (member : tick ∈ PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner)
        owner execution) : False := by
    obtain ⟨packet, emitted, _clock⟩ := List.mem_map.mp member
    obtain ⟨input, authored, _tagged, _named⟩ := PhaseSeedScheduler.localInput_emission_authentic
      runtime leaks execution (originalCoordinate owner) owner words recalled packet.1 packet.2
        emitted
    have output : packet.2 ∈ app.outputs (execution.recall owner) := by
      rw [← recalled owner]
      exact List.mem_filter.mpr ⟨input, decide_eq_true authored⟩
    rw [empty] at output
    exact List.not_mem_nil output
  exact clocks.elim (impossible 0) (impossible _)

end Vegas.Examples.CommitSeedBroadcast
