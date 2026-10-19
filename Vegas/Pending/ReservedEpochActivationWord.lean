/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochActiveSlot
import Interaction.ReactiveResponseAccounting

/-! # Exogenous owner response ordinals in actual reserved-service histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem command_actor_view_independent {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (cursor : Nat) (left right : (app).EnvironmentView) :
    (command runtime leaks packetBudget tape cursor left).actor? app =
      (command runtime leaks packetBudget tape cursor right).actor? app := by
  dsimp only [command]
  split_ifs <;> first
    | rfl
    | rw [process_actor_none, process_actor_none]
    | rw [sample_actor_none, sample_actor_none]

private theorem consistent_activation_words {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (left right earlierLeft earlierRight : List (app).EnvironmentEntry)
    (samePast : earlierLeft.length = earlierRight.length) (sameLength : left.length = right.length)
    (leftConsistent : (app).commandConsistentFrom
      (fun selected past view => command runtime leaks packetBudget selected past.length view)
      tape earlierLeft left)
    (rightConsistent : (app).commandConsistentFrom
      (fun selected past view => command runtime leaks packetBudget selected past.length view)
      tape earlierRight right) :
    left.filterMap (fun entry => entry.command.actor? app) =
      right.filterMap (fun entry => entry.command.actor? app) := by
  induction left generalizing right earlierLeft earlierRight with
  | nil =>
      cases right with
      | nil => rfl
      | cons first rest => simp only [List.length_nil, List.length_cons] at sameLength; omega
  | cons first rest ih =>
      cases right with
      | nil => simp only [List.length_cons, List.length_nil] at sameLength; omega
      | cons second later =>
          have firstChoice := leftConsistent.1
          have secondChoice := rightConsistent.1
          have actors : first.command.actor? app = second.command.actor? app := by
            rw [← firstChoice, ← secondChoice]
            dsimp only
            rw [samePast]
            exact command_actor_view_independent runtime leaks packetBudget tape
              earlierRight.length first.beforeView second.beforeView
          have remaining : rest.length = later.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using sameLength
          have prefixes : (earlierLeft ++ [first]).length =
              (earlierRight ++ [second]).length := by
            simp only [List.length_append, List.length_singleton, samePast]
          have tail := ih later (earlierLeft ++ [first]) (earlierRight ++ [second])
            prefixes remaining leftConsistent.2 rightConsistent.2
          simp only [List.filterMap_cons, actors, tail]

theorem trace_activation_words_congr {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (leftInitial rightInitial : PMF (app).State)
    (leftHorizon rightHorizon : Nat) (left right : (app).Control)
    (leftTrace : ((app).protocol leftInitial leftHorizon
      (family runtime leaks packetBudget tape)).Trace (some left))
    (rightTrace : ((app).protocol rightInitial rightHorizon
      (family runtime leaks packetBudget tape)).Trace (some right))
    (cursor : left.execution.environmentRecall.length =
      right.execution.environmentRecall.length) :
    (app).activationHistory left.execution = (app).activationHistory right.execution := by
  let choose := fun (selected : Tape Player length) (past : List (app).EnvironmentEntry)
    (view : (app).EnvironmentView) => command runtime leaks packetBudget selected past.length view
  have consistentLeft := ((app).deterministic_transcript_invariant choose tape).history leftInitial
    leftHorizon (fun _ _ => trivial) leftTrace
  have consistentRight := ((app).deterministic_transcript_invariant choose tape).history
    rightInitial rightHorizon (fun _ _ => trivial) rightTrace
  exact consistent_activation_words runtime leaks packetBudget tape left.execution.environmentRecall
    right.execution.environmentRecall [] [] rfl cursor consistentLeft consistentRight

theorem trace_response_ordinals_congr {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (leftInitial rightInitial : PMF (app).State)
    (leftHorizon rightHorizon : Nat) (left right : (app).Control)
    (leftTrace : ((app).protocol leftInitial leftHorizon
      (family runtime leaks packetBudget tape)).Trace (some left))
    (rightTrace : ((app).protocol rightInitial rightHorizon
      (family runtime leaks packetBudget tape)).Trace (some right))
    (cursor : left.execution.environmentRecall.length =
      right.execution.environmentRecall.length)
    (actor : left.actor = right.actor) (owner : Player) :
    (left.execution.recall owner).length = (right.execution.recall owner).length := by
  have words := trace_activation_words_congr runtime leaks packetBudget tape
    leftInitial rightInitial leftHorizon rightHorizon left right leftTrace rightTrace cursor
  have leftCount := (app).response_count_history leftInitial leftHorizon
    (family runtime leaks packetBudget tape) left leftTrace owner
  have rightCount := (app).response_count_history rightInitial rightHorizon
    (family runtime leaks packetBudget tape) right rightTrace owner
  rw [words, actor] at leftCount
  omega

end Vegas.EventGraphRuntime.ReservedEpoch
