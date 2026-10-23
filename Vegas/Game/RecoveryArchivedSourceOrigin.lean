/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryArchivedInitialization
import Vegas.Game.PhaseProposalReplayPath

/-! # Actual archived checkpoints in one linked chosen source chronology -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Archive creation retains the earlier chronology at the literal starting
trace of the newly closed block. Actual onward steps include the intervening
sample and reveal instructions, rather than independent reachable witnesses. -/
inductive ArchivedSourceOrigins (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode) :
    List (RetiredCommitAttempt ((toEventGraph setup.program).withMode mode)) →
      setup.commitRecoveryProtocol.History → Prop where
  | initial (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
      (input : State L setup.context) (supported : input ∈ setup.initialLaw.support) :
      ArchivedSourceOrigins setup mode []
        ⟨_, (RecoverySourceCheckpoint.initialized setup mode plan input supported).trace⟩
  | append {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
      (checkpoint : RecoverySourceCheckpoint setup mode state)
      (origins : ArchivedSourceOrigins setup mode state.retired ⟨_, checkpoint.trace⟩)
      (aligned : checkpoint.ArchivedRecall)
      (record : RetiredCommitAttempt ((toEventGraph setup.program).withMode mode))
      (attempt : state.attempt = record.attempt)
      (retained : state.entry.native.config.history.IsPrefix record.state.config.history)
      (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase)
      (agrees : checkpoint.refs.Agrees checkpoint.source.state record.state.config.store)
      (positive : 0 < eventCount checkpoint.residual.tail)
      {closed : setup.commitRecoveryProtocol.History} {steps : Nat}
      (reached : setup.commitRecoveryProtocol.ReachesWithin steps ⟨_, checkpoint.trace⟩ closed)
      (instructions : setup.recoveryJointRecall closed.trace =
        (checkpoint.commitInstructionWord record.state).reverse ++
          setup.recoveryJointRecall checkpoint.trace)
      (addresses : ∃ word, setup.recoveryAddressWord closed.trace =
        setup.recoveryAddressWord checkpoint.trace ++ word ∧
        word.map (fun address => address.2.1) = checkpoint.commitExclusionWord record.state ∧
        (CommitRecoveryState.atPoint
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
          state.entry.excluded state.generation).IntervalAddresses word ∧
        word.getLast? = closed.state.map CommitRecoveryState.publicAddress)
      : ArchivedSourceOrigins setup mode (state.retired ++ [record]) closed
  /-- A completed nonarchiving phase retains both chosen endpoints and its actual native image. -/
  | advance {state nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
      (checkpoint : RecoverySourceCheckpoint setup mode state)
      (next : RecoverySourceCheckpoint setup mode nextState)
      (origins : ArchivedSourceOrigins setup mode state.retired ⟨_, checkpoint.trace⟩)
      (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
      (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
      (installed : state.phases = phase :: remaining)
      (advanced : nextState.phases = remaining)
      (generation : nextState.generation = state.generation)
      (archives : nextState.retired = state.retired)
      (boundary : phase.high = nextState.attempt.phase)
      (aligned : checkpoint.ArchivedRecall)
      (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase)
      (retained : state.entry.native.config.history.IsPrefix
        nextState.entry.native.config.history)
      (stored : KeepsStore state.entry.native nextState.entry.native)
      (finished : phase.Finished nextState.entry)
      (reachable : ∃ inputs, nextState.entry.native.Invariant inputs)
      {fuel : Nat}
      (reached : setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
      (instructions : phase.kind = .commitment →
        setup.recoveryJointRecall next.trace =
          (checkpoint.commitInstructionWord nextState.entry.native).reverse ++
            setup.recoveryJointRecall checkpoint.trace)
      (publicSteps : phase.kind ≠ .commitment →
        Relation.ReflTransGen
          (NativePublicSourceStep nextState.entry.native 0 setup.program)
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source), state.entry.excluded)
          (next.residual.lift (ProtocolState.entry next.residual.tail next.source),
            nextState.entry.excluded))
      (publicAddresses : phase.kind ≠ .commitment →
        ∃ states : List (ProtocolState setup.program × Finset Player),
          ((checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
            state.entry.excluded) :: states).IsChain
              (NativePublicSourceStep nextState.entry.native 0 setup.program) ∧
          ((checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
            state.entry.excluded) :: states).getLast (List.cons_ne_nil _ _) =
              (next.residual.lift (ProtocolState.entry next.residual.tail next.source),
                nextState.entry.excluded) ∧
          setup.recoveryAddressWord next.trace = setup.recoveryAddressWord checkpoint.trace ++
            states.map (fun point =>
              (CommitRecoveryState.atPoint point.1 point.2 state.generation).publicAddress))
      (addresses : phase.kind = .commitment →
        ∃ word, setup.recoveryAddressWord next.trace =
          setup.recoveryAddressWord checkpoint.trace ++ word ∧
          word.map (fun address => address.2.1) =
            checkpoint.commitExclusionWord nextState.entry.native ∧
          (CommitRecoveryState.atPoint
            (checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
            state.entry.excluded state.generation).IntervalAddresses word ∧
          word.getLast? = some (CommitRecoveryState.atPoint
            (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
            nextState.entry.excluded nextState.generation).publicAddress)
      (replay : phase.kind ≠ .commitment →
        NativeSourceReplayExtension setup nextState.entry.native state.generation
          checkpoint.trace next.trace) :
      ArchivedSourceOrigins setup mode nextState.retired ⟨_, next.trace⟩

namespace ArchivedSourceOrigins

/-- Reading an indexed archive retains its actual old typed checkpoint,
original decoded joint word, and genuine source paths into the final chosen trace. -/
theorem get {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {retired : List (RetiredCommitAttempt ((toEventGraph setup.program).withMode mode))}
    {history : setup.commitRecoveryProtocol.History}
    (origins : ArchivedSourceOrigins setup mode retired history)
    (index : Nat) (bound : index < retired.length) :
    ∃ (state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))
      (checkpoint : RecoverySourceCheckpoint setup mode state),
      checkpoint.ArchivedRecall ∧
      ArchivedSourceOrigins setup mode state.retired ⟨_, checkpoint.trace⟩ ∧
      state.retired = retired.take index ∧
      state.attempt = retired[index].attempt ∧
      state.entry.native.config.history.IsPrefix retired[index].state.config.history ∧
      state.entry.native.config.cut.IsPrefix state.attempt.phase ∧
      checkpoint.refs.Agrees checkpoint.source.state retired[index].state.config.store ∧
      0 < eventCount checkpoint.residual.tail ∧
      ∃ (closed : setup.commitRecoveryProtocol.History) (steps later : Nat),
        setup.commitRecoveryProtocol.ReachesWithin steps ⟨_, checkpoint.trace⟩ closed ∧
        setup.recoveryJointRecall closed.trace =
          (checkpoint.commitInstructionWord retired[index].state).reverse ++
            setup.recoveryJointRecall checkpoint.trace ∧
        setup.commitRecoveryProtocol.ReachesWithin later closed history
 := by
  induction origins generalizing index with
  | initial => exact (Nat.not_lt_zero index bound).elim
  | @append state checkpoint previous aligned record attempt retained saved agrees positive
      closed steps path instructions _addresses ih =>
      by_cases earlier : index < state.retired.length
      · obtain ⟨old, source, sourceAligned, earlierOrigins, archive, oldAttempt, oldRetained,
          oldSaved,
          oldAgrees,
          oldPositive, oldClosed, oldSteps, oldLater, sourcePath, oldInstructions, onward⟩ :=
            ih index earlier
        refine ⟨old, source, sourceAligned, earlierOrigins, ?_, ?_, ?_, oldSaved, ?_, oldPositive,
          oldClosed, oldSteps, oldLater + steps, sourcePath, ?_,
          onward.trans path⟩
        · simpa only [List.take_append_of_le_length earlier.le] using archive
        · simpa only [List.getElem_append_left earlier] using oldAttempt
        · simpa only [List.getElem_append_left earlier] using oldRetained
        · intro name cell selected
          simpa only [List.getElem_append_left earlier] using oldAgrees selected
        · simpa only [List.getElem_append_left earlier] using oldInstructions
      · have last : index = state.retired.length := by
          simp only [List.length_append, List.length_singleton] at bound
          omega
        subst index
        refine ⟨state, checkpoint, aligned, previous, ?_, ?_, ?_, saved, ?_, positive,
          closed, steps,
          0, path, ?_, .refl 0 _⟩
        · simp only [List.take_left' rfl]
        · simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem_cons_zero] using attempt
        · simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem_cons_zero] using retained
        · intro name cell selected
          simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem_cons_zero] using agrees selected
        · simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem_cons_zero] using instructions
  | advance _checkpoint _next _previous _phase _remaining _installed _advanced _generation archives
      _boundary _aligned _saved _retained _stored _finished _reachable path _instructions
      _publicSteps _publicAddresses _addresses _replay ih =>
      obtain ⟨old, source, sourceAligned, earlierOrigins, archive, oldAttempt, oldRetained,
        oldSaved, oldAgrees, oldPositive, oldClosed, oldSteps, oldLater, sourcePath,
        oldInstructions, onward⟩ := ih index (by simpa only [archives] using bound)
      refine ⟨old, source, sourceAligned, earlierOrigins, ?_, ?_, ?_, oldSaved, ?_, oldPositive,
        oldClosed, oldSteps, oldLater + _, sourcePath, ?_, onward.trans path⟩
      · simpa only [archives] using archive
      · simpa only [archives] using oldAttempt
      · simpa only [archives] using oldRetained
      · intro name cell selected
        simpa only [archives] using oldAgrees selected
      · simpa only [archives] using oldInstructions

end ArchivedSourceOrigins
end Vegas
