/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountedSeedObservation

/-! # Fields of genuine active-owner decision observations -/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

local notation "app" => runtime.reactiveApplication leaks

/-- A present owner observation identifies the actual activation and the full
recorded own input, including every earlier emitted packet. -/
theorem decisionObservation_fields (owner : Player)
    (point : graph.Inputs × (app).Command × (app).Execution)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : decisionObservation (owner := owner) point = some (past, view)) :
    point.2.1 = .activate owner ∧
      (point.2.2.recall owner, point.2.2.observe app owner) = (past, view) := by
  classical
  have present : ((app).observe owner (some ⟨0, point.2.1.actor? app, point.2.2⟩)).isSome := by
    change (decisionObservation (owner := owner) point).isSome
    rw [observed]
    rfl
  have actorEq := ((app).observe_isSome owner
    (some ⟨0, point.2.1.actor? app, point.2.2⟩)).mp present
  change point.2.1.actor? app = some owner at actorEq
  have acting : point.2.1 = .activate owner := by
    cases commandEq : point.2.1 with
    | activate actor =>
        rw [commandEq] at actorEq
        change some actor = some owner at actorEq
        exact congrArg (fun actor : Player => (.activate actor : (app).Command))
          (Option.some.inj actorEq)
    | application operation => simp only [commandEq, ReactiveApplication.Command.actor?,
        reduceCtorEq] at actorEq
    | «include» id => simp only [commandEq, ReactiveApplication.Command.actor?,
        reduceCtorEq] at actorEq
    | wait => simp only [commandEq, ReactiveApplication.Command.actor?, reduceCtorEq] at actorEq
  refine ⟨acting, ?_⟩
  simpa only [decisionObservation, acting, ReactiveApplication.Command.actor?,
    ReactiveApplication.observe, ↓reduceIte, Option.some.injEq] using observed

end Vegas.EventGraphRuntime.LocalSeedController
