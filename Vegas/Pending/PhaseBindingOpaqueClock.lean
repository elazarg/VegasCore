/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingOpaqueStep
import Vegas.Pending.PhaseBindingClockReplay

/-! # The actual clear clock step with a hidden binding preparation -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The real clock command and normalizer preserve the entire external channel
across hidden private binding meanings. Saved private states may differ. -/
theorem phase_clock_external_congr (left right : (app).Execution) (hidden : Player)
    (phases : left.application.phases = right.application.phases)
    (generation : left.application.generation = right.application.generation)
    (retired : left.application.retired.map (fun prior =>
        (prior.attempt, prior.state.publicView)) =
      right.application.retired.map (fun prior => (prior.attempt, prior.state.publicView)))
    (nativePublic : left.application.current.native.publicView =
      right.application.current.native.publicView)
    (nativeViews : ∀ who, who ≠ hidden →
      left.application.current.native.playerView who =
        right.application.current.native.playerView who)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ hidden → left.recall who = right.recall who)
    (leftClear : left.application.current.excluded = ∅)
    (rightClear : right.application.current.excluded = ∅) :
    phaseExternalObservation runtime leaks hidden
        (PhaseRuntimeState.normalizeExecution runtime leaks
          (PhaseBindingRepair.rawClock runtime leaks left)) =
      phaseExternalObservation runtime leaks hidden
        (PhaseRuntimeState.normalizeExecution runtime leaks
          (PhaseBindingRepair.rawClock runtime leaks right)) := by
  let first := (PhaseBindingRepair.rawClock runtime leaks left).application
  let second := (PhaseBindingRepair.rawClock runtime leaks right).application
  have clocks : left.application.current.native.clock =
      right.application.current.native.clock := congrArg PublicView.clock nativePublic
  have rawPublic : first.current.native.publicView = second.current.native.publicView := by
    change ({ left.application.current.native.publicView with
        clock := left.application.current.native.clock + 1 } : PublicView graph) =
      { right.application.current.native.publicView with
        clock := right.application.current.native.clock + 1 }
    rw [nativePublic, clocks]
  have rawViews (who : Player) (different : who ≠ hidden) :
      first.current.native.playerView who = second.current.native.playerView who := by
    change ({ left.application.current.native.playerView who with
        publicView := { left.application.current.native.publicView with
          clock := left.application.current.native.clock + 1 } } : PlayerView graph) =
      { right.application.current.native.playerView who with
        publicView := { right.application.current.native.publicView with
          clock := right.application.current.native.clock + 1 } }
    rw [nativeViews who different, nativePublic, clocks]
  have firstCurrent : first.normalize.current = first.current :=
    (PhaseRuntimeState.settle_of_clear first.phases first.generation first.entry first.current
      first.retired leftClear).1
  have secondCurrent : second.normalize.current = second.current :=
    (PhaseRuntimeState.settle_of_clear second.phases second.generation second.entry second.current
      second.retired rightClear).1
  have normalized := PhaseRuntimeState.normalize_publicView_congr_of_clear first second phases
    generation retired rawPublic leftClear rightClear
  have environment : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    have publicView : left.application.publicView = right.application.publicView := by
      simp only [PhaseRuntimeState.publicView, PhaseRuntimeState.attempt, phases, generation,
        retired, nativePublic, leftClear, rightClear]
    rw [network, publicView, receipts]
    rfl
  apply phaseExternalObservation_congr runtime leaks
    (PhaseRuntimeState.normalizeExecution runtime leaks (PhaseBindingRepair.rawClock runtime leaks
      left))
    (PhaseRuntimeState.normalizeExecution runtime leaks (PhaseBindingRepair.rawClock runtime leaks
      right)) hidden network receipts
  · change left.environmentRecall ++ [⟨left.observeEnvironment app, .application .advanceClock⟩] =
      right.environmentRecall ++ [⟨right.observeEnvironment app, .application .advanceClock⟩]
    rw [service, environment]
  · exact normalized
  · intro who different
    change (first.normalize.current.native.playerView who, first.normalize.publicView) =
      (second.normalize.current.native.playerView who, second.normalize.publicView)
    rw [firstCurrent, secondCurrent]
    exact Prod.ext (rawViews who different) normalized
  · exact recalled

end Vegas.EventGraphRuntime
