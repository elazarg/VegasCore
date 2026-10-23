/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCompletedBindings

/-! # Accepted handles are fixed after completion

A completed event cannot acquire, lose, or change its accepted handle along
an actual continuation. Thus acceptance at a final debt-free forced input
already holds at every earlier prefix where that event has completed.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- Completion makes the accepted handle immutable along an actual history,
including the case where no handle was accepted. -/
theorem completed_accepted_of_tracePrefix
    {before after : (application setup leaks).Control}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some before))
    {trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some after)}
    (isPrefix : TracePrefix prior trace) (event : (graph setup).EventId)
    (completed : event ∈ before.execution.application.config.cut.completed) :
    event ∈ after.execution.application.config.cut.completed ∧
      after.execution.application.accepted (.inr event) =
        before.execution.application.accepted (.inr event) := by
  have carry : ∀ {first final :
      (onePacketProtocol setup leaks bounds horizon scheduler).State}
      (firstTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first)
      (lastTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final),
      TracePrefix firstTrace lastTrace → ∀ current,
      first = some current → event ∈ current.execution.application.config.cut.completed →
      ∃ next : (application setup leaks).Control, final = some next ∧
        event ∈ next.execution.application.config.cut.completed ∧
          next.execution.application.accepted (.inr event) =
            current.execution.application.accepted (.inr event) := by
    intro first final firstTrace lastTrace
    induction lastTrace with
    | start =>
        intro found current same done
        cases found
        exact ⟨current, same, done, rfl⟩
    | @extend source target earlier joint legal realized ih =>
        intro found current same done
        cases found with
        | refl => exact ⟨current, same, done, rfl⟩
        | extend isEarlier _ _ _ =>
            obtain ⟨middle, sourceEq, completedMiddle, table⟩ := ih isEarlier current same done
            subst sourceEq
            obtain ⟨next, targetEq, _⟩ := (application setup leaks).transition_recall_prefix
              (initialLaw setup) horizon scheduler middle target joint realized
            refine ⟨next, targetEq, ?_, ?_⟩
            · subst targetEq
              exact completed_transition (horizon := horizon) leaks joint realized completedMiddle
            · subst targetEq
              rcases acceptedKept_transition leaks (initialLaw setup) horizon scheduler middle
                  next joint realized event with unchanged | ⟨ready, _, _⟩
              · exact unchanged.trans table
              · exact (ready.1 completedMiddle).elim
  obtain ⟨next, same, done, table⟩ := carry prior trace isPrefix before rfl completed
  cases Option.some.inj same
  exact ⟨done, table⟩

/-- Every binding completed at a prefix has already been accepted if the final
public record and focal debt-free state rule out missing bindings. -/
theorem completedBinding_accepted_at_tracePrefix
    {who : Player} {before after : (application setup leaks).Control}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some before))
    {trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some after)}
    (isPrefix : TracePrefix prior trace) (record : PublicRecord setup who after)
    (debtFree : ∀ point, nativeDecodedState setup leaks (some after) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (layoutEq : (graph setup).outputLayout event = .binding owner payload)
    (completed : event ∈ before.execution.application.config.cut.completed) :
    before.execution.application.accepted (.inr event) ≠ none := by
  obtain ⟨persists, sameTable⟩ := completed_accepted_of_tracePrefix prior isPrefix event completed
  rw [← sameTable]
  exact completedBinding_accepted_of_publicRecord trace record debtFree event owner payload
    layoutEq persists

end Vegas
