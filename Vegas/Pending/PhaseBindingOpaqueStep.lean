/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedBudget

/-! # Literal same-command inclusion and histories for all-value phase shadows -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The joint physical channel outside one owner's private local state and
response word. Full networks and scheduler recall are retained. -/
def phaseExternalObservation (hidden : Player) (execution : (app).Execution) :=
  (execution.network, execution.receipts, execution.environmentRecall,
    execution.observeEnvironment app,
    fun who => if who = hidden then none else
      some (execution.recall who, execution.observe app who))

theorem phaseExternalObservation_congr (left right : (app).Execution) (hidden : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (application : left.application.publicView = right.application.publicView)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recalled : ∀ who, who ≠ hidden → left.recall who = right.recall who) :
    phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right := by
  have environment : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, application]
    rfl
  unfold phaseExternalObservation
  refine Prod.ext network (Prod.ext receipts (Prod.ext service (Prod.ext environment ?_)))
  funext who
  by_cases same : who = hidden
  · simp only [same, ite_true]
  · simp only [same, ite_false]
    apply congrArg some
    apply Prod.ext (recalled who same)
    change (⟨left.network.observe who, left.application.playerView who, left.receipts⟩ :
      (app).PlayerView) = ⟨_, _, _⟩
    rw [network, receipts, views who same]
    rfl

end Vegas.EventGraphRuntime
