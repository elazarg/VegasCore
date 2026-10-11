/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReactiveSourceDecision
import Vegas.Pending.ReactiveOriginalResponseStability
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveOffTurnPosterior

/-! # Reconstructed source recall across actual responses -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Sampling a new authentic prescribed response leaves the complete original
source action history fixed until its event is physically completed. -/
theorem originalReactiveSourceRecall_respond
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (whole : SourceProgram Player L Γ names)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    (who : Player) (policy : (toEventGraph whole).BehavioralPolicy who)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (intentions : List (Option (toEventGraph whole).Completion))
    (aligned : (execution.recall who).length = intentions.length)
    (action : (runtime.reactiveApplication leaks).Action)
    (saved : Option (toEventGraph whole).Completion)
    (supported : (action, saved) ∈
      (runtime.prescribedReactiveResponse leaks who policy (execution.recall who) intentions
        (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    originalReactiveSourceRecall whole runtime leaks who
      (execution.respond (runtime.reactiveApplication leaks) who action) (intentions ++ [saved]) =
      originalReactiveSourceRecall whole runtime leaks who execution intentions := by
  have configEq := (runtime.reactive_respond_application leaks execution who action).1
  unfold originalReactiveSourceRecall
  rw [configEq]
  apply congrArg (decodeCompletions whole)
  apply List.map_congr_left
  intro completion retained
  apply runtime.reactiveOriginal_respond_completed leaks who policy execution intentions
    aligned action saved supported completion
  apply (execution.application.config.history_exact completion.event).mp
  exact List.mem_map.mpr ⟨completion, (List.mem_filter.mp retained).1, rfl⟩

/-- A genuine off-turn callback preserves the exact posterior law of the
complete reconstructed source own-action history. Extra observed traffic
cannot reweight the source intentions through this callback. -/
theorem originalReactiveSourceRecall_posterior_respond_of_no_turn
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (whole : SourceProgram Player L Γ names)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    (who : Player) (policy : (toEventGraph whole).BehavioralPolicy who)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      (execution.recall who))
    (offTurn : execution.application.publicView.ownTurn? who = none) :
    let next := execution.respond (runtime.reactiveApplication leaks) who ⟨none⟩
    ((runtime.prescribedReactiveImplementation leaks who policy).posterior (next.recall who)).map
      (originalReactiveSourceRecall whole runtime leaks who next) =
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (execution.recall who)).map
          (originalReactiveSourceRecall whole runtime leaks who execution) := by
  intro next
  let entry : (runtime.reactiveApplication leaks).PlayerEntry :=
    ⟨execution.observe (runtime.reactiveApplication leaks) who, ⟨none⟩, none⟩
  have recalled : next.recall who = execution.recall who ++ [entry] := by
    simp [next, entry, ReactiveApplication.Execution.respond]
  rw [recalled, runtime.prescribedReactivePosterior_snoc_of_no_turn leaks who policy
    (execution.recall who) entry (by exact offTurn), PMF.map_comp]
  apply map_congr_on_support
  intro intentions supported
  have aligned := (runtime.prescribedReactivePosterior_length leaks who policy consistent
    intentions supported).symm
  let view := execution.observe (runtime.reactiveApplication leaks) who
  have viewedTurn : view.application.publicView.ownTurn? who = none := offTurn
  dsimp only [view] at viewedTurn
  exact originalReactiveSourceRecall_respond whole runtime leaks who policy execution intentions
    aligned ⟨none⟩ none (by
      simp only [prescribedReactiveResponse, viewedTurn, PMF.mem_support_pure_iff])

end Vegas
