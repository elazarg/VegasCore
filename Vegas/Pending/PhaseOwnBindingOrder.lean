/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearTraceProgress

/-! # Chronological order of ready events of the same owner -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Along an actual clear history, a later ready event of the same owner
cannot precede the earlier ready event in static source rank. This applies to
arbitrary legal response menus and retains the actual history-prefix witness. -/
theorem phase_ready_owner_rank_le_of_clear_prefix
    (ordered : graph.RevealRelaxedOrdered)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (trace : (menu.protocol initial horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix prior trace)
    (clear : after.execution.application.current.excluded = ∅)
    (owner : Player) (first second : graph.EventId)
    (firstActor : graph.actor? first = some owner)
    (secondActor : graph.actor? second = some owner)
    (firstReady : before.execution.application.current.native.config.cut.Ready first)
    (secondReady : after.execution.application.current.native.config.cut.Ready second) :
    first.val ≤ second.val := by
  have completed := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before after prior trace isPrefix clear).2.2.2.2
  have visible := ordered.ready_visible_iff before.execution.application.current.native.config.cut
    firstReady firstActor (EventCode.output_visible_of_actor (graph.nodes second) owner secondActor)
      (IndependentReveals.not_of_actor_eq (by rw [secondActor, firstActor]))
      (IndependentReveals.not_of_actor_eq (by rw [secondActor, firstActor]))
  by_contra reversed
  have done := visible.mpr (show second.val < first.val by omega)
  exact secondReady.1 (completed done)

/-- Distinct same-owner ready events occur in strict static rank order along
an actual clear history. Uniqueness of physical sends can supply distinctness
without imposing a separate sorted-record assumption. -/
theorem phase_ready_owner_rank_lt_of_clear_prefix
    (ordered : graph.RevealRelaxedOrdered)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (trace : (menu.protocol initial horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix prior trace)
    (clear : after.execution.application.current.excluded = ∅)
    (owner : Player) (first second : graph.EventId)
    (firstActor : graph.actor? first = some owner)
    (secondActor : graph.actor? second = some owner)
    (firstReady : before.execution.application.current.native.config.cut.Ready first)
    (secondReady : after.execution.application.current.native.config.cut.Ready second)
    (different : first ≠ second) : first.val < second.val := by
  have lower := phase_ready_owner_rank_le_of_clear_prefix runtime leaks ordered menu initial
    horizon scheduler before after prior trace isPrefix clear owner first second firstActor
      secondActor firstReady secondReady
  have unequal : first.val ≠ second.val := fun same => different (Fin.ext same)
  omega

end Vegas.EventGraphRuntime
