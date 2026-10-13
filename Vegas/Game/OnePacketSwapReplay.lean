/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapRecord
import Vegas.Game.SourceSwapPairs
import Vegas.Game.OnePacketActingJoint
import Vegas.Game.OnePacketDecodedActor
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Swapped histories replay the swapped intended history

Fix two intended histories `first` and `second` of equal length, with states
`p` and `q`. The native swap of the pairs between `p` and `q`
(`Vegas.betweenPairs`) moves the decoded point of every configuration by the
source swap between `p` and `q` (`Vegas.decodedPoint_betweenPairs`), and a
decoded action of a completion by the same swap.

So along a native history whose intended replay is a prefix of `first`, the
image history under the swap symmetry replays the corresponding prefix of
`second` (`Vegas.intendedHistory?_mapTrace`). Each completion lands on the next
step of `second`: by the prefix correspondence of intended histories the target
is the next state of `second`, and the acting joint of the swapped decoded
action is the joint action of that step, since a realized intended step is the
acting joint of every choice reaching its target.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **A decoded action is available at its decoded point** under the forfeiture
interface, to every player. -/
theorem decodeSourcePrefix?_available (who : Player) {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} : ∀ (count : Nat)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L) (state : ProtocolState program),
    decodeSourcePrefix? program refs registry revelations outputs count store history =
      some state →
    (inside : count < eventCount program) →
    ∀ (graphAction : EventGraph.EventField.Action (outputLayout program ⟨count, inside⟩))
      (action : OwnAction Player L),
      decodeEventAction program ⟨count, inside⟩ graphAction = some action →
      action ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program)
        (ProtocolState.observe who program state)
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, state, decoded,
      inside => by
      cases program with
      | ret _ => simp [eventCount] at inside
      | sample _ _ _ next =>
          intro _ _ decodedAction
          cases decodedAction
      | commit _ _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro graphAction action decodedAction
          cases decodedAction
          exact ⟨graphAction, by cases graphAction <;> trivial, rfl⟩
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro graphAction action decodedAction
          cases decodedAction
          exact ⟨graphAction, rfl⟩
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, state,
      decoded, inside => by
      cases program with
      | ret _ => cases decoded
      | sample _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_available who count next _ _ _ _ store history rest
            restDecoded (by simpa [eventCount] using inside)
      | commit _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_available who count next _ _ _ _ store history rest
            restDecoded (by simpa [eventCount] using inside)
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_available who count next _ _ _ _ store history rest
            restDecoded (by simpa [eventCount] using inside)

variable {setup : Setup (Player := Player) (L := L)}

/-- **A completion's decoded action is addressed to its decoded point**: it is
available there to every active player under the forfeiture interface. -/
theorem decoded_addressed {config : (graph setup).Config} {event : (graph setup).EventId}
    (ready : config.cut.Ready event) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) (graphAction : (graph setup).Action event) :
    ∀ who action, decodeEventAction setup.program event graphAction = some action →
      (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).active
        (some point) who →
      action ∈ (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).available
        (some point) who := by
  intro who action decodedAction _
  exact decodeSourcePrefix?_available who event.val setup.program _ _ _ _ _ _ point
    (decodedPoint_decode ready decoded) event.isLt graphAction action decodedAction

section Between

variable [DecidableEq (CellTy Player L)] {first second : ProtocolState setup.program}
  {publicAgree : PublicCellsAgree setup first second}
  {succeed : CommitmentCellsSucceed setup first second}

/-- **The decoded point of a swapped configuration** is the swapped decoded point. -/
theorem decodedPoint_betweenPairs (config : (graph setup).Config) :
    decodedPoint setup (config.swap (EventGraph.ValueSwap.ofPairs
        (betweenPairs publicAgree succeed))) =
      (decodedPoint setup config).map
        ((CellSwap.between setup.program first second).protocolState setup.program) := by
  unfold decodedPoint
  by_cases ordered : ∃ rank, config.cut.IsPrefix rank
  · have swappedOrdered : ∃ rank, (config.swap (EventGraph.ValueSwap.ofPairs
        (betweenPairs publicAgree succeed))).cut.IsPrefix rank := ordered
    rw [dite_eq_left_of_eq_true (eq_true swappedOrdered),
      dite_eq_left_of_eq_true (eq_true ordered)]
    exact sourceServicePrefix?_betweenPairs _ config
  · have swappedOrdered : ¬ ∃ rank, (config.swap (EventGraph.ValueSwap.ofPairs
        (betweenPairs publicAgree succeed))).cut.IsPrefix rank := ordered
    rw [dite_eq_right_of_eq_false (eq_false swappedOrdered),
      dite_eq_right_of_eq_false (eq_false ordered)]
    rfl

end Between

end Vegas
