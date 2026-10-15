/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapInformation
import Vegas.Pending.ValueSwapPairs

/-! # Observer information for foreign-owner pairs in every dependency mode -/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

/-- Pair support determines which observer is fixed. The proof applies to the
actual graph, including its chosen dependency mode. -/
theorem ofPairs_phaseInput_eq (pairs : graph.SwapPairs)
    (handlePairs : Handle graph → Option (Raw L × Raw L)) (who : Player)
    (visibleNone : ∀ field, graph.fieldVisibleTo who field → pairs.pair field = none)
    (handlesNone : ∀ slot, handlePairs (who, slot) = none)
    (bounds : MessageBounds graph) (initial : PMF (phaseApplication runtime leaks).State)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial
      horizon scheduler).Trace (some control)) :
    (((HiddenSwap.ofPairs pairs handlePairs).phaseExecution control.execution).recall who,
        ((HiddenSwap.ofPairs pairs handlePairs).phaseExecution control.execution).observe
          (phaseApplication runtime leaks) who) =
      (control.execution.recall who,
        control.execution.observe (phaseApplication runtime leaks) who) := by
  apply (HiddenSwap.ofPairs pairs handlePairs).phaseInput_eq_of_fixed bounds initial
    horizon scheduler control trace who
  · intro field visible
    change pairSwap (pairs.pair field) = id
    rw [visibleNone field visible]
    rfl
  · intro event acting
    change pairs.action event = id
    unfold SwapPairs.action
    cases nodeView graph event with
    | resolve | sample => rfl
    | bind owner payload outputEq codeEq =>
        have actorEq : graph.actor? event = some owner :=
          (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
        rw [actorEq] at acting
        cases Option.some.inj acting
        have visible : graph.fieldVisibleTo who (.inr event) := by
          change (graph.outputLayout event).VisibleTo who
          rw [outputEq]
          rfl
        rw [visibleNone _ visible]
        funext original
        simp [pairSwap]
  · intro slot
    change pairSwap (handlePairs (who, slot)) = id
    rw [handlesNone slot]
    rfl

/-- A swap whose pairs occur only at one foreign owner's private fields and
handles preserves the focal player's full actual input, without restricting
the execution mode or assuming equality of player views. -/
theorem foreignPairs_phaseInput_eq (pairs : graph.SwapPairs)
    (handlePairs : Handle graph → Option (Raw L × Raw L)) (owner who : Player)
    (different : who ≠ owner)
    (valueOwner : ∀ field, pairs.pair field ≠ none →
      (graph.layout field).VisibleTo owner ∧ ¬ (graph.layout field).IsPublic)
    (handleOwner : ∀ handle, handlePairs handle ≠ none → handle.1 = owner)
    (bounds : MessageBounds graph) (initial : PMF (phaseApplication runtime leaks).State)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial
      horizon scheduler).Trace (some control)) :
    (((HiddenSwap.ofPairs pairs handlePairs).phaseExecution control.execution).recall who,
        ((HiddenSwap.ofPairs pairs handlePairs).phaseExecution control.execution).observe
          (phaseApplication runtime leaks) who) =
      (control.execution.recall who,
        control.execution.observe (phaseApplication runtime leaks) who) := by
  apply ofPairs_phaseInput_eq pairs handlePairs who _ _ bounds initial horizon scheduler
    control trace
  · intro field visible
    by_contra paired
    obtain ⟨owned, privateField⟩ := valueOwner field paired
    change (graph.layout field).VisibleTo who at visible
    cases layoutEq : graph.layout field with
    | publicData | publication => exact privateField (by rw [layoutEq]; trivial)
    | binding other payload | privateInput other payload =>
        have focal : other = who := by
          simpa only [layoutEq, EventField.VisibleTo] using visible
        have original : other = owner := by
          simpa only [layoutEq, EventField.VisibleTo] using owned
        exact different (focal.symm.trans original)
  · intro slot
    by_contra paired
    exact different (handleOwner (who, slot) paired)

end Vegas.EventGraphRuntime.HiddenSwap
