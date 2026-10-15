/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedOwnerRecall

/-! # Event-local binding responses from activation clocks -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- A pure own-service rule reads the complete local activation-clock history
and chooses either to wait or the prepared handle slot of its single packet.
The hidden source result is fixed outside the service rule. -/
def bindingServiceResponse (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (choose : List Nat → Option Nat)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) : (app).Action :=
  if view.application.publicView.EventReady event ∧
      (runtime.ownerSeedInput leaks event past view).emitted = [] then
    match choose ((runtime.ownerActivationQueries leaks event past).map
        (fun query => query.input.elapsed) ++
          [(runtime.ownerSeedInput leaks event past view).elapsed]) with
    | none => ⟨none⟩
    | some slot => runtime.reactiveBinding leaks owner event payload result slot
  else ⟨none⟩

end Vegas.EventGraphRuntime

end
