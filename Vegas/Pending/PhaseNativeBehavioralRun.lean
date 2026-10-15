/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeControlRun

/-! # The original counted and native behavioral runs have their actual coupling -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- The native image of globally covered physical policies is coupled to the
original counted-model behavioral run, at every finite fuel. Safety is only
the absence of physical exclusion along supported policy histories. -/
theorem exists_paired_behavioral_run (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (players : Player → (P).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
    (safe : ∀ (current : (P).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (fuel : Nat) :
    let menu := PhaseCount.onePacketMenu runtime leaks bounds
    let physicalInitial := inputs.map (PhaseRuntimeState.initial plan)
    let nativeInitial := inputs.map State.initial
    let imageScheduler := nativeScheduler runtime leaks plan scheduler
    ∃ paired : PMF ((N).ProtocolState × (P).ProtocolState),
      paired.map Prod.fst = (((N).information nativeInitial horizon
        imageScheduler).runSingleMoverBehavioralFrom
          ((N).singleMover nativeInitial horizon imageScheduler)
          (fun who => (N).encodePolicy (nativePolicy runtime leaks plan (players who))) fuel
            ((N).protocol nativeInitial horizon imageScheduler).initHistory).map History.state ∧
      paired.map Prod.snd = ((menu.information physicalInitial horizon scheduler).runBehavioralFrom
        (fun who => menu.restrictPolicy physicalInitial horizon scheduler who (players who)) fuel
          (menu.protocol physicalInitial horizon scheduler).initHistory).map History.state ∧
      ∀ pair ∈ paired.support,
        pair.1 = protocolState runtime leaks plan pair.2 ∧
        PairedPublicRecord runtime leaks plan pair.1 pair.2 := by
  intro menu physicalInitial nativeInitial imageScheduler
  obtain ⟨paired, first, second, valid⟩ := exists_paired_control_run runtime leaks plan bounds
    ordered maximal inputs horizon scheduler players covered safe fuel
  refine ⟨paired, ?_, ?_, valid⟩
  · rw [(N).run_map_state]
    exact first
  · rw [menu.run_restrict_control_steps physicalInitial horizon scheduler players
      (menu.admissible_of_covered physicalInitial horizon scheduler players covered)]
    exact second

end Vegas.EventGraphRuntime.PhaseNativeProjection
