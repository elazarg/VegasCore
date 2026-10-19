/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLostBindingReplay
import Interaction.ReactiveOwnPlay

/-! # Whole information retained by actual lost-preparation replay

The trace counterpart keeps the literal initialized input and every other
player's entire input and own-play word. No reduced observation or deletion
of rare private alias records is used for those players.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open Interaction EventGraph GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

local notation "app" => phaseApplication runtime leaks

/-- Read the original joint input and all non-designated full action factors
from the constructed genuine suffix image. -/
theorem preparationOnly_full_information
    (bounds : MessageBounds graph) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (owner : Player) (slot : CandidateSlot graph)
    (first second : Raw L) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some control))
    (image : (app).Execution)
    (imageTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some ⟨control.remaining, control.actor, image⟩))
    (paired : image.eraseRecall app owner =
      ((preparationOnly (owner, slot) first second).phaseExecution control.execution).eraseRecall
        app owner) :
    image.application.current.native.config.inputs =
        control.execution.application.current.native.config.inputs ∧
      ∀ who, who ≠ owner →
        (image.recall who, image.observe app who) =
            (control.execution.recall who, control.execution.observe app who) ∧
          ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
            scheduler).ownPlay who imageTrace =
            ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
              scheduler).ownPlay who trace := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let swap := preparationOnly (owner, slot) first second
  constructor
  · have original := congrArg (fun execution : (app).Execution =>
      execution.application.current.native.config.inputs) paired
    exact original
  · intro who different
    have handles (query : CandidateSlot graph) : swap.raw (who, query) = id := by
      apply preparationOnly_raw_of_ne
      exact fun same => different (congrArg Prod.fst same)
    have input := swap.phaseInput_eq_of_fixed bounds initial horizon scheduler control trace who
      (fun _ _ => rfl) (fun _ _ => rfl) handles
    have observed : (image.recall who, image.observe app who) =
        ((swap.phaseExecution control.execution).recall who,
          (swap.phaseExecution control.execution).observe app who) := by
      have original := congrArg (fun execution : (app).Execution =>
        (execution.recall who, execution.observe app who)) paired
      simpa only [ReactiveApplication.eraseRecall_recall_other app _ _ _ different,
        ReactiveApplication.eraseRecall_observe] using original
    have exactInput := observed.trans input
    refine ⟨exactInput, ?_⟩
    have word (current : (app).Control)
        (history : (menu.protocol initial horizon scheduler).Trace (some current)) :
        (menu.information initial horizon scheduler).ownPlay who history =
          (app).recallOwnPlay (current.execution.recall who) := by
      change (menu.signals initial horizon scheduler).ownPlay who history = _
      rw [← menu.ownPlay_toRawTrace initial horizon scheduler who history,
        (app).trace_ownPlay]
      rfl
    rw [word _ imageTrace, word control trace]
    exact congrArg (app).recallOwnPlay (congrArg Prod.fst exactInput)

end Vegas.EventGraphRuntime.HiddenSwap
