/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedRecall
import Interaction.ReactiveHistory
import Interaction.ReactivePolicyInvariant

/-! # Actual local emission words retain their immutable timed prefix -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem runRounds_recall_prefix (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support)
    (owner : Player) : execution.recall owner <+: next.recall owner := by
  let invariant : (app).PolicyInvariant players
      (fun current => execution.recall owner <+: current.recall owner) := {
    respond current actor action before _ :=
      before.trans ((app).respond_recall_prefix current actor owner action)
    environment current after command before moved := by
      rw [(app).environmentStep_recall current after command moved]
      exact before }
  exact invariant.runRounds scheduler count execution next
    ⟨[], by simp only [List.append_nil]⟩ reached

/-- Every supported future round retains the full timed emission prefix for a
fixed physical coordinate. This keeps raw values for provenance without exposing
them to the operational calendar query. -/
theorem runRounds_emissions_prefix (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    (wordRecall : WordRecall runtime leaks execution)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support)
    (owner : Player) (coordinate : CommitAttemptEvent graph) :
    (localInput runtime leaks coordinate owner execution.environmentRecall
      (execution.observeEnvironment app)).emissions <+:
      (localInput runtime leaks coordinate owner next.environmentRecall
        (next.observeEnvironment app)).emissions := by
  classical
  have afterRecall := runRounds_wordRecall runtime leaks scheduler players count execution next
    wordRecall reached
  have recalled := runRounds_recall_prefix runtime leaks scheduler players count execution next
    reached owner
  rw [localInput_word, localInput_word, wordRecall owner coordinate, afterRecall owner coordinate]
  exact ((recalled.filter fun entry =>
    decide (PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)).map
      (fun entry => (entry.beforeView.application.2.native.clock -
        (entry.beforeView.application.2.native.activatedAt coordinate.event).getD
          entry.beforeView.application.2.native.clock,
        entry.emitted.toList.filter (ownPacket coordinate owner)))).flatMap
          (fun entry => entry.2.map (Prod.mk entry.1))

end Vegas.EventGraphRuntime.PhaseSeedScheduler
