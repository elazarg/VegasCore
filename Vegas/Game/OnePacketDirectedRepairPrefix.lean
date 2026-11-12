module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketCounterpartGuard

@[expose] public section

/-! # Exposure guards through every actual history prefix

Readiness or completion persists along a native trace. Hence a reveal that has
not reached either status at the final cut was never active at any earlier cut.
This carries the failed-binding repair guard back through the whole history.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- Every initialized prefix's ready or completed event remains ready or
completed at every later actual history state. -/
theorem readyOrCompleted_of_tracePrefix {before : (application setup timeouts leaks).Control}
    (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some before))
    {state : (application setup timeouts leaks).ProtocolState}
    {trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state}
    (isPrefix : TracePrefix prior trace) {event : (graph setup).EventId}
    (active : before.execution.application.config.cut.Ready event ∨
      event ∈ before.execution.application.config.cut.completed) :
    ∃ after : (application setup timeouts leaks).Control, state = some after ∧
      (after.execution.application.config.cut.Ready event ∨
        event ∈ after.execution.application.config.cut.completed) := by
  have carry : ∀ {first final :
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).State}
      (firstTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace first)
      (lastTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace final),
      TracePrefix firstTrace lastTrace → ∀ current,
      first = some current →
      (current.execution.application.config.cut.Ready event ∨
        event ∈ current.execution.application.config.cut.completed) →
      ∃ next : (application setup timeouts leaks).Control, final = some next ∧
        (next.execution.application.config.cut.Ready event ∨
          event ∈ next.execution.application.config.cut.completed) := by
    intro first final firstTrace lastTrace
    induction lastTrace with
    | start =>
        intro found current same activeNow
        cases found
        exact ⟨current, same, activeNow⟩
    | @extend source target earlier joint legal realized ih =>
        intro found current same activeNow
        cases found with
        | refl => exact ⟨current, same, activeNow⟩
        | extend isEarlier _ _ _ =>
            obtain ⟨middle, sourceEq, activeMiddle⟩ := ih isEarlier current same activeNow
            subst sourceEq
            obtain ⟨next, targetEq, _⟩ := (application setup timeouts
              leaks).transition_recall_prefix
              (initialLaw setup) horizon scheduler middle target joint realized
            refine ⟨next, targetEq, ?_⟩
            subst targetEq
            have retained := EventGraph.Config.Step.path_completed_mono
              (reactive_protocol_graph_steps timeouts leaks (initialLaw setup) horizon scheduler
                middle next joint realized)
            rcases activeMiddle with ready | completed
            · by_cases completed : event ∈ next.execution.application.config.cut.completed
              · exact Or.inr completed
              · exact Or.inl ⟨completed, ready.2.trans retained⟩
            · exact Or.inr (retained completed)
  exact carry prior trace isPrefix before rfl active

/-- An available typed field keeps its value through every actual history
extension, including arbitrary admitted responses and environment commands. -/
theorem storedValue_of_tracePrefix {before after : (application setup timeouts leaks).Control}
    (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some before))
    {trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some after)}
    (isPrefix : TracePrefix prior trace) (field : (graph setup).Field)
    (value : ((graph setup).layout field).Value)
    (stored : before.execution.application.config.store field = some value) :
    after.execution.application.config.store field = some value := by
  have retain {first last : (graph setup).Config}
      (path : Relation.ReflTransGen EventGraph.Config.Step first last)
      (present : first.store field = some value) : last.store field = some value := by
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact present
    | @head current next moved _ ih =>
        obtain ⟨event, ready, action, supported⟩ := moved
        exact ih (current.step_store_of_some next event ready action supported field value present)
  have carry : ∀ {first final :
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).State}
      (firstTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace first)
      (lastTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace final),
      TracePrefix firstTrace lastTrace → ∀ current,
      first = some current → current.execution.application.config.store field = some value →
      ∃ next : (application setup timeouts leaks).Control, final = some next ∧
        next.execution.application.config.store field = some value := by
    intro first final firstTrace lastTrace
    induction lastTrace with
    | start =>
        intro found current same present
        cases found
        exact ⟨current, same, present⟩
    | @extend source target earlier joint legal realized ih =>
        intro found current same present
        cases found with
        | refl => exact ⟨current, same, present⟩
        | extend isEarlier _ _ _ =>
            obtain ⟨middle, sourceEq, storedMiddle⟩ := ih isEarlier current same present
            subst sourceEq
            obtain ⟨next, targetEq, _⟩ := (application setup timeouts
              leaks).transition_recall_prefix
              (initialLaw setup) horizon scheduler middle target joint realized
            refine ⟨next, targetEq, ?_⟩
            subst targetEq
            have path := reactive_protocol_graph_steps timeouts leaks (initialLaw setup) horizon
              scheduler middle next joint realized
            exact retain path storedMiddle
  obtain ⟨next, same, present⟩ := carry prior trace isPrefix before rfl stored
  cases Option.some.inj same
  exact present

end Vegas
