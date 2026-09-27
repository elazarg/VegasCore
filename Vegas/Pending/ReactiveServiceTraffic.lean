/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveTrafficContinuation
import Vegas.Pending.ReactiveServiceEvaluation

/-! # Traffic evidence survives arbitrary remaining service instructions

This connects physical service execution to the terminal audit readout. The
remaining plan and all player responses are unrestricted. A rejected packet
keeps the phase and author recorded at transmission, even if it later becomes
acceptable, is rebroadcast, or is included in the ledger.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem executionTraffic_runInteractionPlan
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (before after : (runtime.reactiveApplication leaks).Execution)
    (reached : after ∈ (runtime.runInteractionPlan leaks players network plan before).support) :
    (runtime.reactiveApplication leaks).executionTraffic before <+:
      (runtime.reactiveApplication leaks).executionTraffic after := by
  induction plan generalizing before with
  | nil => cases FinDist.mem_support_pure.mp reached; rfl
  | cons instruction rest ih =>
      obtain ⟨middle, stepped, continued⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨command, _, dispatched⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ stepped)
      exact ((runtime.reactiveApplication leaks).executionTraffic_dispatch
        players command before middle dispatched).trans (ih middle continued)

/-- A transmission's actual record is still present at settlement after any
remaining service plan. This proves persistence, not sampling or collection. -/
theorem trafficRecord_after_activation_plan
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (before activated after : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (action : (runtime.reactiveApplication leaks).Action) (remaining : Nat)
    (sampled : activated ∈
      (before.environmentStep (runtime.reactiveApplication leaks) (.activate who)).support)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : record ∈ (runtime.reactiveApplication leaks).trafficStep
      (some ⟨remaining + 1, none, before⟩)
      (some ⟨remaining, none, activated.respond (runtime.reactiveApplication leaks) who action⟩))
    (reached : after ∈ (runtime.runInteractionPlan leaks players network plan
      (activated.respond (runtime.reactiveApplication leaks) who action)).support) :
    record ∈ (runtime.reactiveApplication leaks).executionTraffic after := by
  apply (runtime.executionTraffic_runInteractionPlan
    leaks players network plan _ after reached).subset
  rw [(runtime.reactiveApplication leaks).executionTraffic_activated_response
    before activated who action remaining sampled]
  exact List.mem_append_right _ present

/-- A recorded violation gives the promised conditional collection rate after
any remaining physical service plan. The sample may depend on the entire final
transcript; no independence from later transmissions or reactions is assumed. -/
theorem trafficAudit_collection_after_plan {Evidence : Type}
    (project : (runtime.reactiveApplication leaks).TrafficRecord → Evidence)
    (attribution : Evidence → Player) (permitted : Evidence → Bool)
    (sample : List Evidence → FinDist (List Evidence))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (before : (runtime.reactiveApplication leaks).Execution) (who : Player) (rate : ℝ)
    (coverage : ∀ actual record, record ∈ actual →
      attribution record = who → permitted record = false →
      rate ≤ (sample actual).probOf {observed | record ∈ observed})
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : record ∈ (runtime.reactiveApplication leaks).executionTraffic before)
    (owner : attribution (project record) = who)
    (forbidden : permitted (project record) = false) :
    let app := runtime.reactiveApplication leaks
    rate ≤ (((((runtime.runInteractionPlan leaks players network plan before).map
      app.executionTraffic).bind (app.sampledTrafficAudit project attribution permitted sample)).map
        (fun verdict => verdict who)).prob true) := by
  apply (runtime.reactiveApplication leaks).sampledTrafficAudit_collection_from_record
    project attribution permitted sample _ _ who rate coverage record _ owner forbidden
  intro final supported
  exact (runtime.executionTraffic_runInteractionPlan
    leaks players network plan before final supported).subset present

end Vegas.EventGraphRuntime
