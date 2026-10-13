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

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A nonempty history extends a shorter one by one step. -/
theorem exists_extend_of_length_pos {ι : Type*} {E : ExecutionProtocol ι} {state : E.State}
    (trace : E.Trace state) (positive : 0 < trace.length) :
    ∃ (source : E.State) (shorter : E.Trace source) (joint : ∀ i, Option (E.Action i))
      (isLegal : E.Legal source joint)
      (realized : state ∈ (E.step source ⟨joint, isLegal⟩).support),
      trace = shorter.extend joint isLegal realized ∧ shorter.length + 1 = trace.length := by
  cases trace with
  | start => simp [Trace.length] at positive
  | extend shorter joint isLegal realized => exact ⟨_, shorter, joint, isLegal, realized, rfl, rfl⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- The history a prefix extends by one step is a prefix as well. -/
theorem TracePrefix.of_extend {ι : Type*} {E : ExecutionProtocol ι} {source target final : E.State}
    {prior : E.Trace source} {joint : ∀ i, Option (E.Action i)} {isLegal : E.Legal source joint}
    {realized : target ∈ (E.step source ⟨joint, isLegal⟩).support} {trace : E.Trace final}
    (isPrefix : TracePrefix (prior.extend joint isLegal realized) trace) :
    TracePrefix prior trace :=
  (TracePrefix.extend .refl joint isLegal realized).trans isPrefix

/-- An advanced replay extends the replay it advances. -/
theorem tracePrefix_of_advanceIntended? {leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (graph setup))}
    {history result : setup.intendedProtocol.History}
    {before after : (application setup leaks).ProtocolState}
    (advanced : advanceIntended? setup leaks history before after = some result) :
    TracePrefix history.trace result.trace := by
  have extended : ∀ {choice target}, extendIntended? setup history choice target = some result →
      TracePrefix history.trace result.trace := by
    intro choice target extendedEq
    unfold extendIntended? at extendedEq
    split at extendedEq
    · split at extendedEq
      · cases extendedEq
        exact .extend .refl _ _ _
      · cases extendedEq
    · cases extendedEq
  match before, after, advanced with
  | none, some _, advanced => exact extended advanced
  | some before, some after, advanced =>
      simp only [advanceIntended?] at advanced
      rcases dropped : List.drop before.execution.application.config.history.length
          after.execution.application.config.history with
        _ | ⟨⟨event, action⟩, _ | ⟨_, _⟩⟩
      · rw [dropped] at advanced
        cases advanced
        exact .refl
      · rw [dropped] at advanced
        exact extended advanced
      · rw [dropped] at advanced
        cases advanced

variable [DecidableEq (CellTy Player L)]

/-- **One step of a prefix lands on the next step of the corresponding prefix.**
Let `extended` be a prefix of `first` extending `prior` by one step, and let
`prior'` be the prefix of `second` of the same length as `prior`. If the
acting joint of a choice addressed to the state of `prior'` reaches the swapped
state of `extended`, then extending `prior'` by that choice to that state is
the prefix of `second` of the same length as `extended`. -/
theorem extendIntended?_between {first second : setup.intendedProtocol.History}
    {p q : ProtocolState setup.program} (firstState : first.state = some p)
    (secondState : second.state = some q)
    (sameLength : first.trace.length = second.trace.length)
    {prior extended prior' : setup.intendedProtocol.History}
    (oneStep : extended.trace.length = prior.trace.length + 1)
    (extendedPrefix : TracePrefix extended.trace first.trace)
    (priorPrefix' : TracePrefix prior'.trace second.trace)
    (priorLength : prior'.trace.length = prior.trace.length)
    {admission : CommitmentInterface setup.program} {choice : Option (OwnAction Player L)}
    (addressed : ∀ who action, choice = some action →
      (setup.executionProtocol admission).active prior'.state who →
        action ∈ (setup.executionProtocol admission).available prior'.state who)
    (reaches : extended.state.map
        ((CellSwap.between setup.program p q).protocolState setup.program) ∈
      (setup.protocolStep prior'.state (actingJoint setup prior'.state choice)).support) :
    ∃ extended', extendIntended? setup prior' choice (extended.state.map
        ((CellSwap.between setup.program p q).protocolState setup.program)) = some extended' ∧
      TracePrefix extended'.trace second.trace ∧
      extended'.trace.length = extended.trace.length := by
  obtain ⟨state', trace', prefix', length', stateEq⟩ :=
    Setup.intended_prefix_between setup firstState secondState sameLength extended.trace
      extendedPrefix
  obtain ⟨source, shorter, joint, legal, realized, rfl, shorterLength⟩ :=
    exists_extend_of_length_pos trace' (by omega)
  have shorterPrefix := TracePrefix.of_extend prefix'
  have samePrior := TracePrefix.eq_of_same_length shorterPrefix priorPrefix' (by omega)
  rcases prior' with ⟨priorState, priorTrace⟩
  cases samePrior
  have jointEq := intended_joint_eq_actingJoint setup legal realized choice addressed
    (stateEq ▸ reaches)
  subst jointEq
  refine ⟨⟨state', priorTrace.extend _ legal realized⟩, ?_, prefix', by omega⟩
  rw [← stateEq]
  unfold extendIntended?
  rw [dite_eq_left_of_eq_true (eq_true legal), dite_eq_left_of_eq_true (eq_true realized)]

end Vegas
