/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountProjection
import Vegas.Pending.ReactiveContinuationObservation
import Interaction.ReactiveRoundCongruence

/-! # Exact focal communication laws under phase metadata

The proof projection retains the complete network, actual environment recall,
receipts, focal own recall and its complete native and public phase view.
Equal projections give equal laws through an arbitrary focal raw response and
through passive activation followed by an arbitrary focal policy. No source
counterpart, hidden-state equality, or hypothesis about a later packet handler
is assumed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A proof readout, retaining actual archives, handles and all communication
data; it is neither additional game state nor a player's observation. -/
def phaseTraffic (who : Player) (execution : (app).Execution) :=
  (execution.network, execution.receipts, execution.environmentRecall, execution.recall who,
    execution.application.playerView who)

private theorem phase_submit_playerView_congr (left right : PhaseRuntimeState graph) (who : Player)
    (material : WitnessedSubmission graph) (views : left.playerView who = right.playerView who) :
    ((app).submit left who material).playerView who =
      ((app).submit right who material).playerView who := by
  let nativeLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
    fun _ _ => PMF.pure ∅
  have native := EventGraphRuntime.submit_playerView_congr runtime nativeLeaks
    left.current.native right.current.native who material (congrArg Prod.fst views)
  exact Prod.ext native (by
    change (left.submit who material).publicView = (right.submit who material).publicView
    rw [PhaseCount.submit_publicView, PhaseCount.submit_publicView]
    exact congrArg Prod.snd views)

private theorem phase_packet_playerView_congr (left right : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph) (views : left.playerView who = right.playerView who) :
    (app).packet ((app).submit left who material) who known material =
      (app).packet ((app).submit right who material) who known material := by
  change (left.submit who material).emit who known material =
    (right.submit who material).emit who known material
  have publicEq : left.publicView = right.publicView := congrArg Prod.snd views
  have attempts : left.attempt = right.attempt := congrArg PhasePublicView.attempt publicEq
  have candidates : (left.current.native.playerView who).candidates =
      (right.current.native.playerView who).candidates :=
    congrArg (fun view => view.1.candidates) views
  have nativePublic : left.current.native.publicView = right.current.native.publicView :=
    congrArg (fun view => view.1.publicView) views
  rw [PhaseCount.emit_after_submit, PhaseCount.emit_after_submit, publicEq, attempts,
    candidates, nativePublic]

private theorem observe_eq (left right : (app).Execution) (who : Player)
    (same : phaseTraffic runtime leaks who left = phaseTraffic runtime leaks who right) :
    left.observe (app) who = right.observe (app) who := by
  have network : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2) same
  change (⟨left.network.observe who, left.application.playerView who, left.receipts⟩ :
    (app).PlayerView) =
      ⟨right.network.observe who, right.application.playerView who, right.receipts⟩
  rw [network, receipts, views]

private theorem observeEnvironment_eq (left right : (app).Execution) (who : Player)
    (same : phaseTraffic runtime leaks who left = phaseTraffic runtime leaks who right) :
    left.observeEnvironment (app) = right.observeEnvironment (app) := by
  have network : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have publicEq : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
    (app).EnvironmentView) =
      ⟨right.network.publicView, right.application.publicView, right.receipts⟩
  rw [network, receipts, publicEq]

/-- Every common raw focal response preserves equality of complete focal
traffic, including malformed packets, forwarded evidence and silence. -/
theorem phaseTraffic_focal_response (left right : (app).Execution) (who : Player)
    (same : phaseTraffic runtime leaks who left = phaseTraffic runtime leaks who right)
    (response : (app).Action) :
    phaseTraffic runtime leaks who (left.respond (app) who response) =
      phaseTraffic runtime leaks who (right.respond (app) who response) := by
  have network : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall who = right.recall who :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2) same
  have packet (material : WitnessedSubmission graph) :
      (app).packet ((app).submit left.application who material) who
          (left.network.known who) material =
        (app).packet ((app).submit right.application who material) who
          (right.network.known who) material := by
    rw [network]
    exact phase_packet_playerView_congr runtime leaks left.application right.application who _
      material views
  have afterRecall := (app).respond_focal_recall_eq left right who who response network
    (observe_eq runtime leaks left right who same) recalled (fun material _ => packet material)
  have afterViews : (left.respond (app) who response).application.playerView who =
      (right.respond (app) who response).application.playerView who := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact views
    | some material =>
      exact phase_submit_playerView_congr runtime leaks left.application right.application who
        material views
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext environments (Prod.ext afterRecall afterViews)))
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact network
  | some material =>
    change (left.network.submit who ((app).packet ((app).submit left.application who material)
      who (left.network.known who) material)).2 = _
    rw [packet, network]
    rfl

/-- A focal policy may depend on its entire actual input and own recall. Its
complete response law has the same traffic effect at equal focal traffic. -/
theorem phaseTraffic_focal_policy (left right : (app).Execution) (who : Player)
    (same : phaseTraffic runtime leaks who left = phaseTraffic runtime leaks who right)
    (policy : (app).Policy) :
    ((policy (left.recall who) (left.observe (app) who)).map
        (fun response => phaseTraffic runtime leaks who (left.respond (app) who response))) =
      ((policy (right.recall who) (right.observe (app) who)).map
        (fun response => phaseTraffic runtime leaks who (right.respond (app) who response))) := by
  have recalled : left.recall who = right.recall who :=
    congrArg (fun value => value.2.2.2.1) same
  rw [recalled, observe_eq runtime leaks left right who same]
  apply map_congr_on_support _
  intro response _
  exact phaseTraffic_focal_response runtime leaks left right who same response

/-- Shared passive samples couple activation for every actor, keeping the
entire physical phase archive and environmental transcript. -/
theorem phaseTraffic_sampledActivation (left right : (app).Execution) (who actor : Player)
    (same : phaseTraffic runtime leaks who left = phaseTraffic runtime leaks who right)
    (sample : Finset (MessageId Player)) :
    phaseTraffic runtime leaks who (left.sampledActivation (app) actor sample) =
      phaseTraffic runtime leaks who (right.sampledActivation (app) actor sample) := by
  have network : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall who = right.recall who :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2) same
  simp only [phaseTraffic, ReactiveApplication.Execution.sampledActivation, network, receipts,
    environments, recalled, views, observeEnvironment_eq runtime leaks left right who same]

/-- Activation's actual observation kernel preserves equal focal traffic,
without any restriction on the passive observation rule. -/
theorem phaseTraffic_activation (left right : (app).Execution) (who actor : Player)
    (same : phaseTraffic runtime leaks who left = phaseTraffic runtime leaks who right) :
    ((left.environmentStep (app) (.activate actor)).map (phaseTraffic runtime leaks who)) =
      ((right.environmentStep (app) (.activate actor)).map (phaseTraffic runtime leaks who)) := by
  have network : left.network = right.network := congrArg Prod.fst same
  rw [ReactiveApplication.Execution.activation_samples,
    ReactiveApplication.Execution.activation_samples, PMF.map_comp, PMF.map_comp, network]
  apply map_congr_on_support _
  intro sample _
  exact phaseTraffic_sampledActivation runtime leaks left right who actor same sample

/-- The complete physical focal activation, including its private pending
sample and arbitrary raw policy response, has exactly the same traffic law. -/
theorem phaseTraffic_focal_dispatch (left right : (app).Execution) (who : Player)
    (same : phaseTraffic runtime leaks who left = phaseTraffic runtime leaks who right)
    (players : Player → (app).Policy) :
    (((app).dispatch players (.activate who) left).map (phaseTraffic runtime leaks who)) =
      (((app).dispatch players (.activate who) right).map (phaseTraffic runtime leaks who)) := by
  rw [ReactiveApplication.dispatch, ReactiveApplication.dispatch, PMF.map_bind, PMF.map_bind]
  apply bind_eq_of_map_eq _ _ _ _ (phaseTraffic_activation runtime leaks left right who who same)
  intro first _ second _ matched
  simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
    ReactiveApplication.invoke, PMF.map_comp, Function.comp_def]
  exact phaseTraffic_focal_policy runtime leaks first second who matched (players who)

end Vegas.EventGraphRuntime
