/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAllocation

/-! # Joint binding frames for arbitrary private raw material

Private material can be absent or have a different type from the binding
payload. It nevertheless emits the same canonical packet. The real reserved
binding block preserves all opponents' inputs jointly, together with public
state, network, receipts, service recall and remaining fresh slots.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem rawBinding_submit_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView)
    (views : ∀ who, who ≠ owner →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (event : graph.EventId) (serial : Nat) (first second : Option (Raw L)) :
    let app := runtime.reactiveApplication leaks
    let before := left.respond app owner
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩⟩
    let after := right.respond app owner
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩
    before.network = after.network ∧ before.receipts = after.receipts ∧
      before.application.publicView = after.application.publicView ∧
      (∀ who, who ≠ owner →
        before.application.playerView who = after.application.playerView who) ∧
      (∀ who, who ≠ owner → before.recall who = after.recall who) := by
  let app := runtime.reactiveApplication leaks
  have foreign (execution : app.Execution) (who : Player) (different : who ≠ owner)
      (opening : Option (Raw L)) :
      let response : app.Action :=
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
      (execution.respond app owner response).application.playerView who =
        execution.application.playerView who := by
    exact (submitStep_playerView_other _ owner who different _).trans
      (Submission.register_other _ execution.application owner who different)
  refine ⟨?_, receipts, ?_, ?_, ?_⟩
  · simp only [ReactiveApplication.Execution.respond, reactiveApplication_packet_none,
      network, publicEq]
  · exact (runtime.reactive_respond_application leaks left owner _).2.trans
      (publicEq.trans (runtime.reactive_respond_application leaks right owner _).2.symm)
  · intro who different
    exact (foreign left who different first).trans
      ((views who different).trans (foreign right who different second).symm)
  · intro who different
    exact (app.respond_recall_other left owner who different _).trans
      ((recall who different).trans (app.respond_recall_other right owner who different _).symm)

end Vegas.EventGraphRuntime
