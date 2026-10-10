/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobRawBinding

/-! # Binding response states after arbitrary earlier receiver traffic

The response uses the receiver's actual next envelope serial. Fixed responses
still select the same visible physical state throughout a native information
class, independently of hidden initialization and foreign traffic.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobResponseState

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
open LateOpeningRuntimeBobRawBinding (known_same_information)

/-- Actual local submission and handler result using the next native message ID. -/
def responseState (execution : app.Execution) (response : app.Action) : app.State :=
  match response.transmission with
  | none => execution.application
  | some material =>
      let submitted := app.submit execution.application bob material
      (app.handle submitted ⟨(bob, execution.network.nextSerial bob),
        app.packet submitted bob (execution.network.known bob) material⟩).getD submitted

theorem responseState_same_view (first second : app.Execution)
    (firstValid : first.InputRecall app) (secondValid : second.InputRecall app)
    (sameRecall : first.recall bob = second.recall bob)
    (sameView : first.observe app bob = second.observe app bob) (response : app.Action) :
    (responseState first response).playerView bob =
      (responseState second response).playerView bob := by
  have physicalView := congrArg ReactiveApplication.PlayerView.application sameView
  change first.application.playerView bob = second.application.playerView bob at physicalView
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact physicalView
  | some material =>
      have submitted := LateOpeningRuntimeService.runtime.submit_playerView_congr leaks
        first.application second.application bob material physicalView
      have known := known_same_information first second firstValid secondValid sameRecall sameView
      have packets := LateOpeningRuntimeService.runtime.packet_playerView_congr leaks
        first.application second.application bob (first.network.known bob) material physicalView
      have emitted : app.packet (app.submit first.application bob material) bob
          (first.network.known bob) material =
        app.packet (app.submit second.application bob material) bob
          (second.network.known bob) material := by
        rw [← known]
        exact packets
      apply LateOpeningRuntimeService.runtime.reactive_handle_result_playerView_congr leaks
        _ _ bob (first.network.nextSerial bob) (second.network.nextSerial bob) _ _
          (congrArg WitnessedPacket.call emitted)
          (congrArg WitnessedPacket.tokenValid emitted) submitted

end Vegas.Examples.LateOpeningRuntimeBobResponseState
