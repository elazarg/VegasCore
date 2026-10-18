/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.ReservedEpochConcurrencyValidity

/-! # Usable native values in the concurrent pending witness -/

noncomputable section

namespace Vegas.Examples.ReservedEpochConcurrency

open SourceProgram EventGraph EventGraphRuntime Interaction
open CommitTimingInformation

private theorem offer_other_view (execution : app.Execution) (actor observer : Player)
    (different : observer ≠ actor) :
    (offer execution actor).application.current.native.playerView observer =
      execution.application.current.native.playerView observer := by
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment (bindingEvent actor) (actor, .prepared 0), some ⟨.bool, true⟩⟩, .none⟩
  change (submitStep (material.call.register execution.application.current.native actor)
    actor material.call.packet).playerView observer = _
  exact (submitStep_playerView_other _ actor observer different material.call.packet).trans
    (material.call.register_other execution.application.current.native actor observer different)

private theorem offer_result (execution : app.Execution) (owner : Player)
    (fresh : execution.application.current.native.candidates.lookup (owner, .prepared 0) = .fresh) :
    (offer execution owner).application.current.native.bindingResult (owner, .prepared 0) .bool =
      .success true :=
  phaseBindingResponse_result runtime leaks _ owner (bindingEvent owner) .bool
    (.success true) 0 fresh

private theorem offer_other_result (execution : app.Execution) (actor observer : Player)
    (different : observer ≠ actor) :
    (offer execution actor).application.current.native.bindingResult (observer, .prepared 0) .bool =
      execution.application.current.native.bindingResult (observer, .prepared 0) .bool := by
  have lookup := congrArg (fun view : PlayerView graph => view.candidates (.prepared 0))
    (offer_other_view execution actor observer different)
  change (offer execution actor).application.current.native.candidates.lookup
      (observer, .prepared 0) =
    execution.application.current.native.candidates.lookup (observer, .prepared 0) at lookup
  simp only [State.bindingResult, lookup]

theorem pending_binding_usable (reverse bit : Bool) (owner : Player) :
    (afterBoth reverse bit).application.current.native.bindingResult (owner, .prepared 0) .bool =
      .success true := by
  have firstFresh : (beforeOffers bit).application.current.native.candidates.lookup
      (first reverse, .prepared 0) = .fresh := initialState_candidate bit _ _
  have secondFresh : (beforeOffers bit).application.current.native.candidates.lookup
      (second reverse, .prepared 0) = .fresh := initialState_candidate bit _ _
  have foreignView := congrArg (fun view : PlayerView graph => view.candidates (.prepared 0))
    (offer_other_view (beforeOffers bit) (first reverse) (second reverse)
      (Ne.symm (distinct_pending_owners reverse)))
  change (afterFirst reverse bit).application.current.native.candidates.lookup
      (second reverse, .prepared 0) =
    (beforeOffers bit).application.current.native.candidates.lookup
      (second reverse, .prepared 0) at foreignView
  have secondResult := offer_result (afterFirst reverse bit) (second reverse)
    (foreignView.trans secondFresh)
  have firstResult := (offer_other_result (afterFirst reverse bit) (second reverse) (first reverse)
    (distinct_pending_owners reverse)).trans
      (offer_result (beforeOffers bit) (first reverse) firstFresh)
  have owners : owner = first reverse ∨ owner = second reverse := by
    fin_cases owner <;> cases reverse <;> simp [first, second]
  rcases owners with rfl | rfl
  · exact firstResult
  · exact secondResult

end Vegas.Examples.ReservedEpochConcurrency
