/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ReservedEpochPublicationBoundary
import Vegas.Game.ReservedEpochPublicationReadCone
import Vegas.Game.CompiledRevealBindingRow
import Vegas.Game.PhaseProposalOrdinaryBindingCheckpoint
import Vegas.Source.CommitRecoveryNonCommitJoint
import Vegas.Source.CommitRecoveryNonCommitValues
import Vegas.Game.PhaseProposalAttemptArchive
import Vegas.Pending.PhaseCountedOpeningSubmission
import Vegas.EventGraph.PrivateInputs
import Vegas.Game.ReservedEpochPublicationEmission
import Vegas.Game.ReservedEpochPublicationEpisode
import Vegas.Game.ReservedEpochPublicationOldWord
import Vegas.Game.ReservedEpochPublicationSourceStep
import Vegas.Game.ReservedEpochPublicationWord
import Vegas.Pending.PhaseReadyPacketStatus

/-! # Actual paired publication records at one saved source checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)

private theorem publication_completed_row
    (anchor left right : EventGraphRuntime.State (serviceGraph setup mode))
    (leftKept : anchor.config.history.IsPrefix left.config.history)
    (rightKept : anchor.config.history.IsPrefix right.config.history)
    (event : (serviceGraph setup mode).EventId)
    (completed : event ∈ anchor.config.cut.completed) :
    ∃ action,
      (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ left.config.history ∧
      (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ right.config.history := by
  obtain ⟨completion, remembered, same⟩ := List.mem_map.mp
    ((anchor.config.history_exact event).mpr completed)
  rcases completion with ⟨other, action⟩
  change other = event at same
  subst other
  exact ⟨action, leftKept.subset remembered, rightKept.subset remembered⟩

private theorem publication_owner_outputs_eq
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ state.phases.head?) (kind : phase.kind = .reveal)
    (left right : RecoveryState (serviceGraph setup mode))
    (leftReached : left.native.config.Reachable left.native.config.inputs)
    (rightReached : right.native.config.Reachable right.native.config.inputs)
    (sameInputs : left.native.config.inputs = right.native.config.inputs)
    (fixed : ∀ event : (serviceGraph setup mode).EventId, event.val < phase.low →
      left.native.config.outputs event = right.native.config.outputs event)
    (inherited : Finset Player)
    (leftOrdered : left.OrderedPublicFailures phase.low inherited)
    (rightOrdered : right.OrderedPublicFailures phase.low inherited)
    (leftFinished : phase.Finished left) (rightFinished : phase.Finished right)
    (owner : Player)
    (row : ∀ event ∈ phase.events, (serviceGraph setup mode).actor? event = some owner →
      owner ∉ inherited →
      (¬ ∃ prior ∈ phase.events, prior.val < event.val ∧
        (serviceGraph setup mode).actor? prior = some owner ∧ left.native.PublicFailure prior) →
      (∀ prior ∈ phase.events, prior.val < event.val →
        (serviceGraph setup mode).actor? prior = some owner →
          left.native.config.outputs prior = right.native.config.outputs prior) →
      ∃ leftAction rightAction,
          (⟨event, leftAction⟩ : (serviceGraph setup mode).Completion) ∈
            left.native.config.history ∧
          (⟨event, rightAction⟩ : (serviceGraph setup mode).Completion) ∈
            right.native.config.history ∧
          PhaseProposal.publicationDiscloses ((serviceGraph setup mode).outputLayout event)
              leftAction =
            PhaseProposal.publicationDiscloses ((serviceGraph setup mode).outputLayout event)
              rightAction) :
    ∀ event ∈ phase.events, (serviceGraph setup mode).actor? event = some owner →
      left.native.config.outputs event = right.native.config.outputs event := by
  classical
  let graph := serviceGraph setup mode
  have castSome : ∀ {first second : EventField Player L} (equal : first = second)
      (value : first.Value), cast (congrArg (fun cell => Option cell.Value) equal) (some value) =
        some (cast (congrArg EventField.Value equal) value) := by
    intro first second equal value
    cases equal
    rfl
  have ownerWord : ∀ rank, ∀ event : graph.EventId, event.val = rank →
      event ∈ phase.events → graph.actor? event = some owner →
        left.native.config.outputs event = right.native.config.outputs event := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
        intro event ranked inside acting
        have earlier : ∀ prior ∈ phase.events, prior.val < event.val →
            graph.actor? prior = some owner →
              left.native.config.outputs prior = right.native.config.outputs prior := by
          intro prior priorInside before priorActor
          exact ih prior.val (by omega) prior rfl priorInside priorActor
        obtain ⟨payload, publication⟩ := kind ▸ phase.fields event
          ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
        have alternatives :
            (left.native.PublicFailure event ∧ right.native.PublicFailure event) ∨
              ∃ leftAction rightAction,
                (⟨event, leftAction⟩ : graph.Completion) ∈ left.native.config.history ∧
                (⟨event, rightAction⟩ : graph.Completion) ∈ right.native.config.history ∧
                PhaseProposal.publicationDiscloses (graph.outputLayout event) leftAction =
                  PhaseProposal.publicationDiscloses (graph.outputLayout event) rightAction := by
          have isPublication : (graph.outputLayout event).IsPublication := by
            rw [publication]
            trivial
          have lower := ((phase.mem_events event).mp inside).1
          by_cases old : owner ∈ inherited
          · exact Or.inl ⟨leftOrdered event owner lower isPublication acting (leftFinished inside)
              (Or.inl old), rightOrdered event owner lower isPublication acting
                (rightFinished inside) (Or.inl old)⟩
          by_cases failed : ∃ prior ∈ phase.events, prior.val < event.val ∧
              graph.actor? prior = some owner ∧ left.native.PublicFailure prior
          · obtain ⟨prior, priorInside, before, priorActor, priorFailed⟩ := failed
            obtain ⟨priorPayload, priorPublication⟩ := kind ▸ phase.fields prior
              ((phase.mem_events prior).mp priorInside).1
                ((phase.mem_events prior).mp priorInside).2
            have sameFailure : left.native.PublicFailure prior ↔
                right.native.PublicFailure prior := by
              have missedLeft : left.native.publicView.missedBinding prior = false := by
                simp only [PublicView.missedBinding, priorPublication]
              have missedRight : right.native.publicView.missedBinding prior = false := by
                simp only [PublicView.missedBinding, priorPublication]
              simp only [EventGraphRuntime.State.PublicFailure, missedLeft, missedRight,
                Bool.false_eq_true, false_or]
              unfold RecoveryState.publicationFailed
              rw [earlier prior priorInside before priorActor]
            have priorLower := ((phase.mem_events prior).mp priorInside).1
            exact Or.inl ⟨leftOrdered event owner lower isPublication acting (leftFinished inside)
              (Or.inr ⟨prior, priorLower, before, priorActor, priorFailed⟩),
                rightOrdered event owner lower isPublication acting (rightFinished inside)
                  (Or.inr ⟨prior, priorLower, before, priorActor, sameFailure.mp priorFailed⟩)⟩
          · exact Or.inr (row event inside acting old failed earlier)
        cases viewed : nodeView graph event with
        | bind actor sort output code =>
            cases output.symm.trans publication
        | sample sort law output code =>
            cases output.symm.trans publication
        | resolve actor sort binding checks output code =>
            rcases alternatives with failed | disclosed
            · have failureRead : ∀ native : EventGraphRuntime.State graph,
                  native.PublicFailure event →
                  (⟨.inr event, output⟩ : FieldRef graph.layout (.publication sort)).get?
                    native.config.store = some .failure := by
                intro native failed
                obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
                  ((native.config.output_available event).mpr failed.completed)
                have read : (⟨.inr event, output⟩ :
                    FieldRef graph.layout (.publication sort)).get? native.config.store =
                      some (cast (congrArg EventField.Value output) value) := by
                  change cast (congrArg (fun cell => Option cell.Value) output)
                    (native.config.outputs event) = _
                  rw [stored]
                  exact castSome output value
                have valueFailed := (publication_failure_iff_read native event binding checks
                  output code _ read).mp failed
                exact read.trans (congrArg some valueFailed)
              have readLeft := failureRead left.native failed.1
              have readRight := failureRead right.native failed.2
              have readEqual := readLeft.trans readRight.symm
              change cast (congrArg (fun cell => Option cell.Value) output)
                  (left.native.config.outputs event) =
                cast (congrArg (fun cell => Option cell.Value) output)
                  (right.native.config.outputs event) at readEqual
              have uncased := congrArg
                (cast (congrArg (fun cell => Option cell.Value) output.symm)) readEqual
              simpa only [cast_cast, cast_eq] using uncased
            · obtain ⟨leftAction, rightAction, leftRecorded, rightRecorded, bits⟩ := disclosed
              have actions : leftAction = rightAction := by
                have firstCast := PhaseProposal.publicationDiscloses_cast output leftAction
                have secondCast := PhaseProposal.publicationDiscloses_cast output rightAction
                have castEqual := firstCast.trans (bits.trans secondCast.symm)
                have uncased := congrArg (cast (congrArg EventField.Action output.symm)) castEqual
                simpa only [PhaseProposal.publicationDiscloses, cast_cast, cast_eq] using uncased
              subst rightAction
              have agree : Store.AgreeOn left.native.config.store right.native.config.store
                  (graph.nodes event).readFields := by
                intro field member
                have cone := checkpoint.publication_read_cone setup phase installed kind event
                  inside owner acting field member
                cases field with
                | inl input =>
                    exact congrArg (fun inputs : graph.Inputs => some (inputs input)) sameInputs
                | inr prior =>
                    rcases cone with before | owned
                    · exact fixed prior before
                    · have before := graph.order.predecessor_lt
                        (graph.reads_available event (.inr prior) member)
                      by_cases beforePhase : prior.val < phase.low
                      · exact fixed prior beforePhase
                      · exact earlier prior ((phase.mem_events prior).mpr ⟨by omega,
                          by have upper := ((phase.mem_events event).mp inside).2; omega⟩)
                            before owned
              obtain ⟨leftLaw, leftValue, leftStored, leftEval, leftSupported⟩ :=
                leftReached.history_output_semantics ⟨event, leftAction⟩ leftRecorded
              obtain ⟨rightLaw, rightValue, rightStored, rightEval, rightSupported⟩ :=
                rightReached.history_output_semantics ⟨event, leftAction⟩ rightRecorded
              have evaluated := EventCode.eval?_congr (graph.nodes event) leftAction
                left.native.config.store right.native.config.store agree
              have sameLaw : leftLaw = rightLaw :=
                Option.some.inj (leftEval.symm.trans (evaluated.trans rightEval))
              have completed := (left.native.config.history_exact event).mp
                (List.mem_map.mpr ⟨⟨event, leftAction⟩, leftRecorded, rfl⟩)
              have available : ∀ field ∈ (graph.nodes event).readFields,
                  (left.native.config.store field).isSome = true := by
                intro field member
                cases field with
                | inl input => rfl
                | inr prior =>
                    exact (left.native.config.output_available prior).mpr
                      (left.native.config.cut.predecessor_closed completed
                        (graph.reads_available event (.inr prior) member))
              obtain ⟨value, pureEval⟩ := (graph.nodes event).eval?_eq_pure_of_actor owner acting
                leftAction left.native.config.store available
              have pureLaw : leftLaw = PMF.pure value := Option.some.inj
                (leftEval.symm.trans pureEval)
              rw [pureLaw, PMF.mem_support_pure_iff] at leftSupported
              rw [← sameLaw, pureLaw, PMF.mem_support_pure_iff] at rightSupported
              exact leftStored.trans ((congrArg some
                (leftSupported.trans rightSupported.symm)).trans rightStored.symm)
  intro event inside acting
  exact ownerWord event.val event rfl inside acting

private theorem publication_replay_row
    (native : EventGraphRuntime.State (serviceGraph setup mode)) (generation : Nat)
    (initial : ProtocolState setup.program × Finset Player)
    (prior : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint initial.1 initial.2 generation)))
    {ending : setup.commitRecoveryProtocol.State}
    (full : setup.commitRecoveryProtocol.Trace ending)
    (replay : NativeSourceReplayExtension setup native generation prior full)
    {before after : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace before)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (realized : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (kept : GameTheory.Protocol.ExecutionProtocol.TracePrefix prior trace)
    (within : GameTheory.Protocol.ExecutionProtocol.TracePrefix
      (trace.extend joint legal realized) full) :
    ∃ (first last : ProtocolState setup.program × Finset Player) (index : Nat),
      before = some (CommitRecoveryState.atPoint first.1 first.2 generation) ∧
      after = some (CommitRecoveryState.atPoint last.1 last.2 generation) ∧
      NativePublicSourceStep native 0 setup.program first last ∧
      NativeDisclosureReadback native 0 setup.program first.1 first.2 joint ∧
      index < full.length - prior.length ∧
      instructionCount setup.program - ProtocolState.remaining setup.program first.1 =
        instructionCount setup.program - ProtocolState.remaining setup.program initial.1 +
          index := by
  obtain ⟨events, _points, _chain, _head, word, annotated, count, cursors⟩ := replay
  have appended : ∀ {source target : setup.commitRecoveryProtocol.State}
      (first : setup.commitRecoveryProtocol.Trace source)
      (last : setup.commitRecoveryProtocol.Trace target),
      GameTheory.Protocol.ExecutionProtocol.TracePrefix first last →
        ∃ rest, proposalSourceSteps setup last = proposalSourceSteps setup first ++ rest := by
    intro source target first last prefixTrace
    induction prefixTrace with
    | refl => exact ⟨[], (List.append_nil _).symm⟩
    | extend _ joint legal realized ih =>
        obtain ⟨rest, equal⟩ := ih
        exact ⟨rest ++ [⟨_, joint, legal, _, realized⟩], by
          rw [proposalSourceSteps_extend, equal, List.append_assoc]⟩
  obtain ⟨middle, middleEq⟩ := appended prior trace kept
  obtain ⟨tail, tailEq⟩ := appended (trace.extend joint legal realized) full within
  let event : setup.commitRecoveryProtocol.StepEvent := ⟨before, joint, legal, after, realized⟩
  have eventsEq : events = middle ++ [event] ++ tail := by
    apply List.append_cancel_left (as := proposalSourceSteps setup prior)
    rw [← word, tailEq, proposalSourceSteps_extend, middleEq]
    simp only [List.append_assoc, event]
  have member : event ∈ events := by
    rw [eventsEq]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨first, last, sourceEq, targetEq, moved, readback, _member⟩ := annotated event member
  obtain ⟨index, bounded, selected⟩ := List.mem_iff_getElem.mp member
  have cursor := cursors index bounded
  rw [selected, sourceEq] at cursor
  refine ⟨first, last, index, sourceEq, targetEq, moved, readback, ?_, ?_⟩
  · rwa [← count]
  · exact Option.some.inj cursor

private theorem publication_replay_endpoint_rank
    (native : EventGraphRuntime.State (serviceGraph setup mode)) (generation : Nat)
    (initial : ProtocolState setup.program × Finset Player)
    (prior : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint initial.1 initial.2 generation)))
    {ending : setup.commitRecoveryProtocol.State}
    (full : setup.commitRecoveryProtocol.Trace ending)
    (replay : NativeSourceReplayExtension setup native generation prior full)
    (retained : GameTheory.Protocol.ExecutionProtocol.TracePrefix prior full) :
    ∃ last : ProtocolState setup.program × Finset Player,
      ending = some (CommitRecoveryState.atPoint last.1 last.2 generation) ∧
      instructionCount setup.program - ProtocolState.remaining setup.program last.1 =
        instructionCount setup.program - ProtocolState.remaining setup.program initial.1 +
          (full.length - prior.length) := by
  have along : ∀ {current : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace current),
      GameTheory.Protocol.ExecutionProtocol.TracePrefix prior trace →
      GameTheory.Protocol.ExecutionProtocol.TracePrefix trace full →
      ∃ last : ProtocolState setup.program × Finset Player,
        current = some (CommitRecoveryState.atPoint last.1 last.2 generation) ∧
        instructionCount setup.program - ProtocolState.remaining setup.program last.1 =
          instructionCount setup.program - ProtocolState.remaining setup.program initial.1 +
            (trace.length - prior.length) := by
    intro current trace kept
    induction kept with
    | refl =>
        intro _within
        exact ⟨initial, rfl, by rw [Nat.sub_self, Nat.add_zero]⟩
    | @extend source target earlier kept joint legal realized ih =>
        intro within
        have earlierWithin :=
          (GameTheory.Protocol.ExecutionProtocol.TracePrefix.extend .refl
            joint legal realized).trans within
        obtain ⟨saved, sourceEq, ranked⟩ := ih earlierWithin
        obtain ⟨first, last, _index, firstEq, targetEq, moved, _readback, _bounded, _cursor⟩ :=
          publication_replay_row setup mode native generation initial prior full replay earlier
            joint legal realized kept within
        have same : saved = first := by
          have pointEq := congrArg (fun state : setup.commitRecoveryProtocol.State =>
            state.map (fun current => (current.point, current.excluded)))
              (sourceEq.symm.trans firstEq)
          exact Option.some.inj pointEq
        subst first
        refine ⟨last, targetEq, ?_⟩
        have nextRank := moved.position
        have lower := kept.length_le
        simp only [GameTheory.Protocol.ExecutionProtocol.Trace.length]
        omega
  exact along full retained .refl

private theorem publication_source_histories_eq
    (leftNative rightNative : EventGraphRuntime.State (serviceGraph setup mode))
    (generation : Nat) (initial : ProtocolState setup.program × Finset Player)
    (prior : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint initial.1 initial.2 generation)))
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftKept : GameTheory.Protocol.ExecutionProtocol.TracePrefix prior leftTrace)
    (rightKept : GameTheory.Protocol.ExecutionProtocol.TracePrefix prior rightTrace)
    (clock : leftTrace.length = rightTrace.length)
    (leftRows : ∀ {before after : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace before)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (legal : setup.commitRecoveryProtocol.Legal before joint)
      (realized : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support),
      GameTheory.Protocol.ExecutionProtocol.TracePrefix prior trace →
      GameTheory.Protocol.ExecutionProtocol.TracePrefix
        (trace.extend joint legal realized) leftTrace →
      ∃ (first last : ProtocolState setup.program × Finset Player) (owner : Player),
        before = some (CommitRecoveryState.atPoint first.1 first.2 generation) ∧
        after = some (CommitRecoveryState.atPoint last.1 last.2 generation) ∧
        NativePublicSourceStep leftNative 0 setup.program first last ∧
        NativeDisclosureReadback leftNative 0 setup.program first.1 first.2 joint ∧
        ProtocolState.actor setup.program first.1 = some owner)
    (rightRows : ∀ {before after : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace before)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (legal : setup.commitRecoveryProtocol.Legal before joint)
      (realized : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support),
      GameTheory.Protocol.ExecutionProtocol.TracePrefix prior trace →
      GameTheory.Protocol.ExecutionProtocol.TracePrefix
        (trace.extend joint legal realized) rightTrace →
      ∃ (first last : ProtocolState setup.program × Finset Player) (owner : Player),
        before = some (CommitRecoveryState.atPoint first.1 first.2 generation) ∧
        after = some (CommitRecoveryState.atPoint last.1 last.2 generation) ∧
        NativePublicSourceStep rightNative 0 setup.program first last ∧
        NativeDisclosureReadback rightNative 0 setup.program first.1 first.2 joint ∧
        ProtocolState.actor setup.program first.1 = some owner)
    (bits : ∀ (point : ProtocolState setup.program) (excluded : Finset Player)
      (first second : Player → Option (CommitRecoveryMove Player L)),
      NativeDisclosureReadback leftNative 0 setup.program point excluded first →
      NativeDisclosureReadback rightNative 0 setup.program point excluded second →
      ∀ owner, ProtocolState.actor setup.program point = some owner → owner ∉ excluded →
        OwnAction.disclosure ((first owner).map (·.action)) =
          OwnAction.disclosure ((second owner).map (·.action))) :
    (⟨leftState, leftTrace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨rightState, rightTrace⟩ := by
  classical
  have compare : ∀ {left right : setup.commitRecoveryProtocol.State}
      (leftPrefix : setup.commitRecoveryProtocol.Trace left)
      (rightPrefix : setup.commitRecoveryProtocol.Trace right),
      GameTheory.Protocol.ExecutionProtocol.TracePrefix prior leftPrefix →
      GameTheory.Protocol.ExecutionProtocol.TracePrefix prior rightPrefix →
      GameTheory.Protocol.ExecutionProtocol.TracePrefix leftPrefix leftTrace →
      GameTheory.Protocol.ExecutionProtocol.TracePrefix rightPrefix rightTrace →
      leftPrefix.length = rightPrefix.length →
        (⟨left, leftPrefix⟩ : setup.commitRecoveryProtocol.History) =
          ⟨right, rightPrefix⟩ := by
    intro left right leftPrefix rightPrefix keptLeft
    induction keptLeft generalizing right with
    | refl =>
        intro keptRight _withinLeft _withinRight sameLength
        exact keptRight.eq_of_length sameLength
    | @extend source target earlier kept joint legal realized ih =>
        intro keptRight withinLeft withinRight sameLength
        cases keptRight with
        | refl =>
            have lower := kept.length_le
            simp only [GameTheory.Protocol.ExecutionProtocol.Trace.length] at sameLength
            omega
        | @extend rightSource rightTarget rightEarlier rightKept
            rightJoint rightLegal rightRealized =>
            have leftEarlierWithin :=
              (GameTheory.Protocol.ExecutionProtocol.TracePrefix.extend .refl
                joint legal realized).trans withinLeft
            have rightEarlierWithin :=
              (GameTheory.Protocol.ExecutionProtocol.TracePrefix.extend .refl
                rightJoint rightLegal rightRealized).trans withinRight
            have before := ih rightEarlier rightKept leftEarlierWithin rightEarlierWithin
              (by simpa only [GameTheory.Protocol.ExecutionProtocol.Trace.length,
                Nat.add_left_inj] using sameLength)
            cases before
            obtain ⟨first, last, owner, sourceEq, targetEq, leftStep, leftReadback, acting⟩ :=
              leftRows earlier joint legal realized kept withinLeft
            obtain ⟨otherFirst, otherLast, _otherOwner, otherSourceEq, otherTargetEq,
                rightStep, rightReadback, _otherActing⟩ :=
              rightRows earlier rightJoint rightLegal rightRealized kept withinRight
            have firstEq : first = otherFirst := by
              have saved := congrArg (fun state : setup.commitRecoveryProtocol.State =>
                state.map (fun current => (current.point, current.excluded)))
                  (sourceEq.symm.trans otherSourceEq)
              exact Option.some.inj saved
            subst otherFirst
            obtain ⟨firstJoint, firstSupported, firstSelected⟩ := leftStep.2.2.2
            obtain ⟨secondJoint, secondSupported, secondSelected⟩ := rightStep.2.2.2
            have lastEq := publication_source_step_eq setup.program first.1 first.2 owner
              acting leftStep.1.2.1 firstJoint secondJoint
              (bits first.1 first.2 firstJoint secondJoint firstSelected secondSelected owner
                acting) last firstSupported otherLast secondSupported
            have jointEq := ProtocolState.noncommit_legal_joint_eq_of_disclosure setup.program
              first.1 first.2 joint rightJoint leftStep.1.2.1
                (by
                  have copied := legal.2
                  rw [sourceEq] at copied
                  change GameTheory.Protocol.IsLegalJoint
                    (CommitRecoveryState.atPoint first.1 first.2 generation).Active
                    (CommitRecoveryState.atPoint first.1 first.2 generation).available joint
                      at copied
                  exact copied)
                (by
                  have copied := rightLegal.2
                  rw [sourceEq] at copied
                  change GameTheory.Protocol.IsLegalJoint
                    (CommitRecoveryState.atPoint first.1 first.2 generation).Active
                    (CommitRecoveryState.atPoint first.1 first.2 generation).available rightJoint
                      at copied
                  exact copied)
                (bits first.1 first.2 joint rightJoint leftReadback rightReadback)
            have endingEq := targetEq.trans
              ((congrArg (fun point : ProtocolState setup.program × Finset Player =>
                some (CommitRecoveryState.atPoint point.1 point.2 generation)) lastEq).trans
                  otherTargetEq.symm)
            cases jointEq
            cases endingEq
            rfl
  exact compare leftTrace rightTrace leftKept rightKept .refl .refl clock

private theorem publication_phase_histories_eq
    (phase : RuntimePhase (serviceGraph setup mode)) (kind : phase.kind = .reveal)
    (leftNative rightNative : EventGraphRuntime.State (serviceGraph setup mode))
    (generation : Nat) (initial leftEnd rightEnd : ProtocolState setup.program × Finset Player)
    (prior : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint initial.1 initial.2 generation)))
    (leftTrace : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint leftEnd.1 leftEnd.2 generation)))
    (rightTrace : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint rightEnd.1 rightEnd.2 generation)))
    (initialRank : instructionCount setup.program -
      ProtocolState.remaining setup.program initial.1 = phase.low)
    (leftRank : instructionCount setup.program -
      ProtocolState.remaining setup.program leftEnd.1 = phase.high)
    (rightRank : instructionCount setup.program -
      ProtocolState.remaining setup.program rightEnd.1 = phase.high)
    (leftKept : GameTheory.Protocol.ExecutionProtocol.TracePrefix prior leftTrace)
    (rightKept : GameTheory.Protocol.ExecutionProtocol.TracePrefix prior rightTrace)
    (leftReplay : NativeSourceReplayExtension setup leftNative generation prior leftTrace)
    (rightReplay : NativeSourceReplayExtension setup rightNative generation prior rightTrace)
    (nativeBits : ∀ event : (serviceGraph setup mode).EventId, ∀ leftAction rightAction,
      (⟨event, leftAction⟩ : (serviceGraph setup mode).Completion) ∈
        leftNative.config.history →
      (⟨event, rightAction⟩ : (serviceGraph setup mode).Completion) ∈
        rightNative.config.history →
      PhaseProposal.publicationDiscloses ((serviceGraph setup mode).outputLayout event)
          leftAction =
        PhaseProposal.publicationDiscloses ((serviceGraph setup mode).outputLayout event)
          rightAction) :
    (⟨_, leftTrace⟩ : setup.commitRecoveryProtocol.History) = ⟨_, rightTrace⟩ := by
  have extent : ∀ (native : EventGraphRuntime.State (serviceGraph setup mode))
      (last : ProtocolState setup.program × Finset Player)
      (trace : setup.commitRecoveryProtocol.Trace
        (some (CommitRecoveryState.atPoint last.1 last.2 generation))),
      NativeSourceReplayExtension setup native generation prior trace →
      GameTheory.Protocol.ExecutionProtocol.TracePrefix prior trace →
      instructionCount setup.program - ProtocolState.remaining setup.program last.1 =
        phase.high → trace.length - prior.length = phase.high - phase.low := by
    intro native last trace replay retained lastRank
    obtain ⟨actual, same, rank⟩ := publication_replay_endpoint_rank setup mode native generation
      initial prior trace replay retained
    have actualEq : last = actual := by
      have points := congrArg (fun state : setup.commitRecoveryProtocol.State =>
        state.map (fun current => (current.point, current.excluded))) same
      exact Option.some.inj points
    subst actual
    rw [initialRank, lastRank] at rank
    omega
  have leftCount := extent leftNative leftEnd leftTrace leftReplay leftKept leftRank
  have rightCount := extent rightNative rightEnd rightTrace rightReplay rightKept rightRank
  have rows : ∀ (native : EventGraphRuntime.State (serviceGraph setup mode))
      {ending : setup.commitRecoveryProtocol.State}
      (full : setup.commitRecoveryProtocol.Trace ending),
      NativeSourceReplayExtension setup native generation prior full →
      full.length - prior.length = phase.high - phase.low →
      ∀ {before after : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace before)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (legal : setup.commitRecoveryProtocol.Legal before joint)
      (realized : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support),
      GameTheory.Protocol.ExecutionProtocol.TracePrefix prior trace →
      GameTheory.Protocol.ExecutionProtocol.TracePrefix
        (trace.extend joint legal realized) full →
      ∃ (first last : ProtocolState setup.program × Finset Player) (owner : Player),
        before = some (CommitRecoveryState.atPoint first.1 first.2 generation) ∧
        after = some (CommitRecoveryState.atPoint last.1 last.2 generation) ∧
        NativePublicSourceStep native 0 setup.program first last ∧
        NativeDisclosureReadback native 0 setup.program first.1 first.2 joint ∧
        ProtocolState.actor setup.program first.1 = some owner := by
    intro native ending full replay count before after trace joint legal realized retained within
    obtain ⟨first, last, index, sourceEq, targetEq, moved, readback, bounded, cursor⟩ :=
      publication_replay_row setup mode native generation initial prior full replay trace joint
        legal realized retained within
    rw [count] at bounded
    rw [initialRank] at cursor
    let event : (serviceGraph setup mode).EventId :=
      ⟨instructionCount setup.program - ProtocolState.remaining setup.program first.1, by
        have upper := phase.bounded
        omega⟩
    have inside : event ∈ phase.events := (phase.mem_events event).mpr ⟨by
      dsimp only [event]
      omega, by dsimp only [event]; omega⟩
    obtain ⟨payload, publication⟩ := kind ▸ phase.fields event
      ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
    obtain ⟨owner, acting⟩ : ∃ owner, (serviceGraph setup mode).actor? event = some owner := by
      cases viewed : nodeView (serviceGraph setup mode) event with
      | bind owner sort output code => cases output.symm.trans publication
      | sample sort law output code => cases output.symm.trans publication
      | resolve owner sort binding checks output code =>
          exact ⟨owner, (EventCode.actor_cast output _).symm.trans
            (congrArg EventCode.actor code)⟩
    exact ⟨first, last, owner, sourceEq, targetEq, moved, readback,
      (source_actor_at_compiled_rank setup.program mode first.1 event rfl).trans acting⟩
  have sameLength : leftTrace.length = rightTrace.length := by
    have leftLower := leftKept.length_le
    have rightLower := rightKept.length_le
    omega
  apply publication_source_histories_eq setup mode leftNative rightNative generation initial prior
    leftTrace rightTrace leftKept rightKept sameLength
      (rows leftNative leftTrace leftReplay leftCount)
      (rows rightNative rightTrace rightReplay rightCount)
  intro point excluded first second firstReadback secondReadback owner acting active
  obtain ⟨leftEvent, leftPayload, leftPublication, leftAction, leftRank, leftRecorded,
      leftSelected⟩ := firstReadback owner acting active
  obtain ⟨rightEvent, rightPayload, rightPublication, rightAction, rightRank, rightRecorded,
      rightSelected⟩ := secondReadback owner acting active
  have same : leftEvent = rightEvent := Fin.ext (leftRank.trans rightRank.symm)
  subst rightEvent
  have recorded := nativeBits leftEvent leftAction rightAction leftRecorded rightRecorded
  have firstBit := (PhaseProposal.publicationDiscloses_cast leftPublication
    leftAction).symm.trans leftSelected
  have secondBit := (PhaseProposal.publicationDiscloses_cast rightPublication
    rightAction).symm.trans rightSelected
  exact firstBit.symm.trans (recorded.trans secondBit)

/-- The actual two-support publication comparison at one saved source
checkpoint. The foreign complete word is unconditional. Equality of the full
logical boundary is conditional on the WAIT image's focal survival. -/
def PairedPublicationBoundary [Fintype Player]
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : Interaction.MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (remaining : Nat) (active : (phaseApplication runtime leaks).Execution) (actor : Player)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (activeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, some actor, active⟩))
    (phase : RuntimePhase (serviceGraph setup mode))
    (checkpoint : RecoverySourceCheckpoint setup mode active.application) : Prop :=
  let graph := serviceGraph setup mode
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
  let horizon := ReservedEpoch.executionHorizon runtime
  let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
  let responseJoint := fun (response : app.Action) (who : Player) =>
    if who = actor then some response else none
  let prompt := active.respond app actor ⟨some material⟩
  let waiting := active.respond app actor ⟨none⟩
  ∃ promptTrace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, prompt⟩),
  ∃ waitingTrace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, waiting⟩),
  GameTheory.Protocol.ExecutionProtocol.TracePrefix activeTrace promptTrace ∧
  GameTheory.Protocol.ExecutionProtocol.TracePrefix activeTrace waitingTrace ∧
  promptTrace.length = activeTrace.length + 1 ∧
  waitingTrace.length = activeTrace.length + 1 ∧
  (∃ (legal : (menu.protocol initial horizon scheduler).Legal
        (some ⟨remaining, some actor, active⟩) (responseJoint ⟨some material⟩))
      (realized : some (⟨remaining, none, prompt⟩ : app.Control) ∈
        (app.transition initial horizon scheduler (some ⟨remaining, some actor, active⟩)
          (responseJoint ⟨some material⟩)).support),
      promptTrace = activeTrace.extend (responseJoint ⟨some material⟩) legal realized) ∧
  (∃ (legal : (menu.protocol initial horizon scheduler).Legal
        (some ⟨remaining, some actor, active⟩) (responseJoint ⟨none⟩))
      (realized : some (⟨remaining, none, waiting⟩ : app.Control) ∈
        (app.transition initial horizon scheduler (some ⟨remaining, some actor, active⟩)
          (responseJoint ⟨none⟩)).support),
      waitingTrace = activeTrace.extend (responseJoint ⟨none⟩) legal realized) ∧
  let law := fun (anchor : app.Execution)
      (trace : (menu.protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, anchor⟩)) =>
    let players := Interaction.ReactiveApplication.anchoredPolicy anchor
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
    let profile := fun who => menu.restrictPolicy initial horizon scheduler who (players who)
    let stopped := fun history : (menu.protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ anchor.application.attempt
    (menu.information initial horizon scheduler).runBehavioralUntil
      (menu.bounded initial horizon scheduler).wellFoundedHistories profile stopped
        ⟨some ⟨remaining, none, anchor⟩, trace⟩
  ∀ promptFinal ∈ (law prompt promptTrace).support,
  ∀ waitingFinal ∈ (law waiting waitingTrace).support,
    ∃ (promptEnding waitingEnding promptBefore waitingBefore : app.Control)
      (promptPrior : (menu.protocol initial horizon scheduler).Trace (some promptBefore))
      (waitingPrior : (menu.protocol initial horizon scheduler).Trace (some waitingBefore))
      (promptJoint waitingJoint : Player → Option app.Action)
      (promptLegal : (menu.protocol initial horizon scheduler).Legal
        (some promptBefore) promptJoint)
      (waitingLegal : (menu.protocol initial horizon scheduler).Legal
        (some waitingBefore) waitingJoint)
      (promptRealized : some promptEnding ∈ (app.transition initial horizon scheduler
        (some promptBefore) promptJoint).support)
      (waitingRealized : some waitingEnding ∈ (app.transition initial horizon scheduler
        (some waitingBefore) waitingJoint).support)
      (promptRaw waitingRaw : RecoveryState graph),
      promptFinal.state = some promptEnding ∧ waitingFinal.state = some waitingEnding ∧
      promptEnding.actor = none ∧ waitingEnding.actor = none ∧
      promptEnding.execution.application =
        ({promptBefore.execution.application with current := promptRaw} :
          PhaseRuntimeState graph).normalize ∧
      waitingEnding.execution.application =
        ({waitingBefore.execution.application with current := waitingRaw} :
          PhaseRuntimeState graph).normalize ∧
      GameTheory.Protocol.ExecutionProtocol.TracePrefix promptTrace promptPrior ∧
      GameTheory.Protocol.ExecutionProtocol.TracePrefix waitingTrace waitingPrior ∧
      GameTheory.Protocol.ExecutionProtocol.TracePrefix
        (promptPrior.extend promptJoint promptLegal promptRealized) promptFinal.trace ∧
      GameTheory.Protocol.ExecutionProtocol.TracePrefix
        (waitingPrior.extend waitingJoint waitingLegal waitingRealized) waitingFinal.trace ∧
      promptBefore.execution.application.attempt = active.application.attempt ∧
      waitingBefore.execution.application.attempt = active.application.attempt ∧
      promptEnding.execution.application.attempt ≠ active.application.attempt ∧
      waitingEnding.execution.application.attempt ≠ active.application.attempt ∧
      PhaseClosingEffect runtime leaks promptBefore.execution promptEnding.execution promptRaw ∧
      PhaseClosingEffect runtime leaks waitingBefore.execution waitingEnding.execution waitingRaw ∧
      phase ∈ promptBefore.execution.application.phases.head? ∧
      phase ∈ waitingBefore.execution.application.phases.head? ∧
      phase.Finished (phase.drain promptRaw) ∧ phase.Finished (phase.drain waitingRaw) ∧
      (phase.drain promptRaw).FailureCoverage ∧ (phase.drain waitingRaw).FailureCoverage ∧
      (phase.drain promptRaw).excluded = promptEnding.execution.application.current.excluded ∧
      (phase.drain waitingRaw).excluded = waitingEnding.execution.application.current.excluded ∧
      (∀ event ∈ phase.events, ∀ owner, owner ≠ actor → graph.actor? event = some owner →
        (PhaseService.BindingAccepted runtime leaks ⟨active.application.attempt, event⟩ owner
            promptEnding.execution ↔
          PhaseService.BindingAccepted runtime leaks ⟨active.application.attempt, event⟩ owner
            waitingEnding.execution) ∧
        (phase.drain promptRaw).native.config.outputs event =
          (phase.drain waitingRaw).native.config.outputs event ∧
        (∀ promptAction waitingAction,
          (⟨event, promptAction⟩ : graph.Completion) ∈
            (phase.drain promptRaw).native.config.history →
          (⟨event, waitingAction⟩ : graph.Completion) ∈
            (phase.drain waitingRaw).native.config.history →
          PhaseProposal.publicationDiscloses (graph.outputLayout event) promptAction =
            PhaseProposal.publicationDiscloses (graph.outputLayout event) waitingAction) ∧
        ∀ raw : Raw L,
          (⟨active.application.attempt, event⟩, raw) ∈
              PhaseProposal.archive promptEnding.execution.network.inputs ↔
            (⟨active.application.attempt, event⟩, raw) ∈
              PhaseProposal.archive waitingEnding.execution.network.inputs) ∧
      (actor ∉ (phase.drain waitingRaw).excluded →
        actor ∉ (phase.drain promptRaw).excluded ∧
        (phase.drain promptRaw).excluded = (phase.drain waitingRaw).excluded ∧
        (phase.drain promptRaw).native.config.inputs =
          (phase.drain waitingRaw).native.config.inputs ∧
        PhaseProposal.sourceArchive promptEnding.execution.network.inputs =
          PhaseProposal.sourceArchive waitingEnding.execution.network.inputs ∧
        PhaseRuntimeState.sourceControlRecords promptEnding.execution.application.retired =
          PhaseRuntimeState.sourceControlRecords waitingEnding.execution.application.retired ∧
        ∃ promptNext : RecoverySourceCheckpoint setup mode
            (⟨active.application.phases.tail, active.application.generation, phase.drain promptRaw,
              phase.drain promptRaw, active.application.retired⟩ : PhaseRuntimeState graph),
        ∃ waitingNext : RecoverySourceCheckpoint setup mode
            (⟨active.application.phases.tail, active.application.generation, phase.drain waitingRaw,
              phase.drain waitingRaw, active.application.retired⟩ : PhaseRuntimeState graph),
          (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
            ⟨_, checkpoint.trace⟩ ⟨_, promptNext.trace⟩) ∧
          Relation.ReflTransGen (NativePublicSourceStep (phase.drain promptRaw).native 0
            setup.program)
            (checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded)
            (promptNext.residual.lift (ProtocolState.entry promptNext.residual.tail
              promptNext.source), (phase.drain promptRaw).excluded) ∧
          (∃ states : List (ProtocolState setup.program × Finset Player),
            ((checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded) :: states).IsChain
              (NativePublicSourceStep (phase.drain promptRaw).native 0 setup.program) ∧
            ((checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded) :: states).getLast
              (List.cons_ne_nil _ _) = (promptNext.residual.lift (ProtocolState.entry
                promptNext.residual.tail promptNext.source), (phase.drain promptRaw).excluded) ∧
            setup.recoveryAddressWord promptNext.trace = setup.recoveryAddressWord checkpoint.trace
              ++
              states.map (fun point => (CommitRecoveryState.atPoint point.1 point.2
                active.application.generation).publicAddress)) ∧
          (∀ owner, owner ∉ (phase.drain promptRaw).excluded → promptNext.source.history owner =
            checkpoint.source.history owner ++
              (decodeHistory setup.program ((phase.drain promptRaw).native.config.history.map
                ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
                  (decodeHistory setup.program (active.application.entry.native.config.history.map
                    ((toEventGraph setup.program).fromModeCompletion mode)) owner).length) ∧
          (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
            ⟨_, checkpoint.trace⟩ ⟨_, waitingNext.trace⟩) ∧
          Relation.ReflTransGen (NativePublicSourceStep (phase.drain waitingRaw).native 0
            setup.program)
            (checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded)
            (waitingNext.residual.lift (ProtocolState.entry waitingNext.residual.tail
              waitingNext.source), (phase.drain waitingRaw).excluded) ∧
          (∃ states : List (ProtocolState setup.program × Finset Player),
            ((checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded) :: states).IsChain
              (NativePublicSourceStep (phase.drain waitingRaw).native 0 setup.program) ∧
            ((checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded) :: states).getLast
              (List.cons_ne_nil _ _) = (waitingNext.residual.lift (ProtocolState.entry
                waitingNext.residual.tail waitingNext.source), (phase.drain waitingRaw).excluded) ∧
            setup.recoveryAddressWord waitingNext.trace = setup.recoveryAddressWord checkpoint.trace
              ++
              states.map (fun point => (CommitRecoveryState.atPoint point.1 point.2
                active.application.generation).publicAddress)) ∧
          (∀ owner, owner ∉ (phase.drain waitingRaw).excluded → waitingNext.source.history owner =
            checkpoint.source.history owner ++
              (decodeHistory setup.program ((phase.drain waitingRaw).native.config.history.map
                ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
                  (decodeHistory setup.program (active.application.entry.native.config.history.map
                    ((toEventGraph setup.program).fromModeCompletion mode)) owner).length) ∧
          NativeSourceReplayExtension setup (phase.drain promptRaw).native
            active.application.generation checkpoint.trace promptNext.trace ∧
          NativeSourceReplayExtension setup (phase.drain waitingRaw).native
            active.application.generation checkpoint.trace waitingNext.trace ∧
          promptNext.residual.lift (ProtocolState.entry promptNext.residual.tail
            promptNext.source) =
              waitingNext.residual.lift (ProtocolState.entry waitingNext.residual.tail
                waitingNext.source) ∧
          (⟨_, promptNext.trace⟩ : setup.commitRecoveryProtocol.History) =
            (⟨_, waitingNext.trace⟩ : setup.commitRecoveryProtocol.History) ∧
          (⟨_, setup.proposalRecoveryLiftTrace
              (nativeArchiveLabels setup
                (PhaseProposal.sourceArchive promptEnding.execution.network.inputs))
              promptNext.trace⟩ : setup.proposalRecoveryProtocol.History) =
            (⟨_, setup.proposalRecoveryLiftTrace
                (nativeArchiveLabels setup
                  (PhaseProposal.sourceArchive waitingEnding.execution.network.inputs))
                waitingNext.trace⟩ : setup.proposalRecoveryProtocol.History) ∧
          setup.recoveryAddressWord promptNext.trace =
            setup.recoveryAddressWord waitingNext.trace ∧
          ∀ owner, owner ∉ (phase.drain promptRaw).excluded →
            ProtocolState.BindingsHoldValues owner setup.program
              (promptNext.residual.lift (ProtocolState.entry promptNext.residual.tail
                promptNext.source)))

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)

private theorem publication_old_foreign_receipt
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (remaining : Nat) (active : (app).Execution) (actor owner : Player)
    (different : owner ≠ actor) (leftResponse rightResponse : (app).Action)
    (leftApplication : (active.respond app actor leftResponse).application = active.application)
    (rightApplication : (active.respond app actor rightResponse).application = active.application)
    (leftStart : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, active.respond app actor leftResponse⟩))
    (rightStart : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, active.respond app actor rightResponse⟩))
    (leftCount rightCount : Nat)
    (leftClosed rightClosed : (app).Control)
    (leftIdle : leftClosed.actor = none) (rightIdle : rightClosed.actor = none)
    (leftTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some leftClosed))
    (rightTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some rightClosed))
    (leftKept : TracePrefix leftStart leftTrace) (rightKept : TracePrefix rightStart rightTrace)
    (leftRetired : leftClosed.execution.application.attempt ≠ active.application.attempt)
    (rightRetired : rightClosed.execution.application.attempt ≠ active.application.attempt)
    (event : (graph).EventId) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (output : (graph).outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode (graph).layout) output) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks output code)
    (value : L.Val payload)
    (locked : binding.get? active.application.current.native.config.store = some (.success value))
    (bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (request : active.application.SeedRequest owner ⟨active.application.attempt, event⟩)
    (entered : Nat) (stamp : active.application.current.native.activatedAt event = some entered)
    (positive : 0 < runtime.deadline event)
    (afterProcessing : ReservedEpoch.packetCapacity runtime ≤ active.environmentRecall.length %
      ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime))
    (leftPath : leftClosed.execution ∈ ((app).runRounds
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) leftCount
        (active.respond app actor leftResponse)).support)
    (rightPath : rightClosed.execution ∈ ((app).runRounds
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) rightCount
        (active.respond app actor rightResponse)).support) :
    PhaseService.BindingAccepted runtime leaks ⟨active.application.attempt, event⟩ owner
        leftClosed.execution ↔
      PhaseService.BindingAccepted runtime leaks ⟨active.application.attempt, event⟩ owner
        rightClosed.execution := by
  rcases leftClosed with ⟨leftRemaining, leftActor, leftClosed⟩
  change leftActor = none at leftIdle
  subst leftActor
  rcases rightClosed with ⟨rightRemaining, rightActor, rightClosed⟩
  change rightActor = none at rightIdle
  subst rightActor
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  have leftWord := phaseProposalUnflagged_stopped_old_opening_receipt_word setup mode runtime
    leaks bounds plan ordered values tape remaining leftRemaining leftCount owner
      (active.respond app actor leftResponse) leftClosed leftStart leftTrace leftKept
        (by simpa only [leftApplication] using leftRetired) event payload binding checks output
          code node value (by simpa only [leftApplication] using locked) bounded
            (by simpa only [leftApplication] using request) entered
              (by simpa only [leftApplication] using stamp) positive
                (by simpa only [(app).respond_environmentRecall] using afterProcessing) leftPath
  have rightWord := phaseProposalUnflagged_stopped_old_opening_receipt_word setup mode runtime
    leaks bounds plan ordered values tape remaining rightRemaining rightCount owner
      (active.respond app actor rightResponse) rightClosed rightStart rightTrace rightKept
        (by simpa only [rightApplication] using rightRetired) event payload binding checks output
          code node value (by simpa only [rightApplication] using locked) bounded
            (by simpa only [rightApplication] using request) entered
              (by simpa only [rightApplication] using stamp) positive
                (by simpa only [(app).respond_environmentRecall] using afterProcessing) rightPath
  have first := ReservedEpoch.openingFrontierReceipt_respond_foreign runtime leaks tape active
    actor owner different leftResponse event
  have second := ReservedEpoch.openingFrontierReceipt_respond_foreign runtime leaks tape active
    actor owner different rightResponse event
  simpa only [leftApplication, rightApplication] using
    leftWord.trans ((first.trans second.symm).trans rightWord.symm)

private theorem publication_old_emission_word
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (remaining count : Nat) (owner : Player)
    (before : (app).Execution) (closed : (app).Control) (idle : closed.actor = none)
    (trace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, before⟩))
    (closedTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some closed))
    (kept : TracePrefix trace closedTrace)
    (retired : closed.execution.application.attempt ≠ before.application.attempt)
    (event : (graph).EventId) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (output : (graph).outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode (graph).layout) output) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks output code)
    (value : L.Val payload)
    (locked : binding.get? before.application.current.native.config.store = some (.success value))
    (bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (request : before.application.SeedRequest owner ⟨before.application.attempt, event⟩)
    (entered : Nat) (stamp : before.application.current.native.activatedAt event = some entered)
    (positive : 0 < runtime.deadline event)
    (path : closed.execution ∈ ((app).runRounds
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) count
        before).support) :
    (∃ message ∈ closed.execution.network.inputs, message.sender = owner ∧
      PhaseProposal.packetProposal? message.payload =
        some (⟨before.application.attempt, event⟩, (⟨payload, value⟩ : Raw L))) ↔
      ReservedEpoch.openingFrontierEmission runtime leaks tape before owner event := by
  rcases closed with ⟨closedRemaining, closedActor, closed⟩
  change closedActor = none at idle
  subst closedActor
  classical
  let horizon := ReservedEpoch.executionHorizon runtime
  let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  rcases ReservedEpoch.opening_frontier_sent_status runtime leaks bounds plan inputs horizon
    scheduler ⟨remaining, none, before⟩ trace owner event payload binding checks output code node
      request with unsent |
      ⟨message, candidate, oldValue, input, sender, address, call, _status, saved, _accepted,
        _fixed⟩
  · exact phaseProposalUnflagged_stopped_unsent_opening_emission_word setup mode runtime leaks
      bounds plan ordered values tape remaining closedRemaining count owner before closed trace
        closedTrace kept retired event payload binding checks output code node value locked
          bounded request entered stamp unsent positive path
  · have valuesEq : oldValue = value := PublicationResult.success.inj
      (Option.some.inj (saved.symm.trans locked))
    subst oldValue
    have retained := ReservedEpoch.input_mem_prefix runtime leaks menu initial horizon scheduler
      ⟨remaining, none, before⟩ ⟨closedRemaining, none, closed⟩ trace closedTrace kept message input
    have outputRecall : message ∈ (app).outputs (before.recall owner) := by
      rw [← (app).history_inputRecall initial horizon scheduler
        ((menu).toRawTrace initial horizon scheduler trace) owner]
      exact List.mem_filter.mpr ⟨input, by simp only [sender, decide_true]⟩
    have emitted : ∃ message ∈ closed.network.inputs, message.sender = owner ∧
        PhaseProposal.packetProposal? message.payload =
          some (⟨before.application.attempt, event⟩, (⟨payload, value⟩ : Raw L)) :=
      ⟨message, retained, sender, by simp only [PhaseProposal.packetProposal?, call, address]⟩
    have frontier : ReservedEpoch.openingFrontierEmission runtime leaks tape before owner event :=
      Or.inl ⟨message, outputRecall, candidate, ⟨payload, value⟩, address, call⟩
    exact iff_of_true emitted frontier

/-- The actual old/fresh split supplies the selected action at an unfinished
foreign publication row. Both branches retain their original closing primitive
and supported unflagged continuation; no row-comparison premise is used. -/
private theorem publication_unfinished_foreign_disclosures_eq
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (remaining : Nat) (anchor : (app).Execution) (actor owner : Player)
    (different : owner ≠ actor) (responses : Bool → (app).Action)
    (applications : ∀ side, (anchor.respond app actor (responses side)).application =
      anchor.application)
    (starts : ∀ side, ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, anchor.respond app actor (responses side)⟩))
    (checkpoint : RecoverySourceCheckpoint setup mode anchor.application)
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (kind : phase.kind = .reveal) (stored : anchor.application.StoredCheckpoint)
    (event : (graph).EventId) (inside : event ∈ phase.events)
    (acting : (graph).actor? event = some owner)
    (active : owner ∉ anchor.application.current.excluded)
    (proper : checkpoint.source.BindingsHoldValues owner)
    (closing ending : Bool → (app).Control)
    (idle : ∀ side, (ending side).actor = none)
    (priors : ∀ side, ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some (closing side)))
    (joints : Bool → Player → Option (app).Action)
    (legal : ∀ side, ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Legal
        (some (closing side)) (joints side))
    (realized : ∀ side, some (ending side) ∈ ((app).transition initial
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
        (some (closing side)) (joints side)).support)
    (kept : ∀ side, TracePrefix (starts side) (priors side))
    (same : ∀ side, (closing side).execution.application.attempt = anchor.application.attempt)
    (changed : ∀ side, (ending side).execution.application.attempt ≠ anchor.application.attempt)
    (closingInstalled : ∀ side, phase ∈ (closing side).execution.application.phases.head?)
    (raw : Bool → RecoveryState graph)
    (effects : ∀ side, PhaseClosingEffect runtime leaks (closing side).execution
      (ending side).execution (raw side))
    (coverage : ∀ side, (phase.drain (raw side)).FailureCoverage)
    (excluded : ∀ side, (phase.drain (raw side)).excluded =
      (ending side).execution.application.current.excluded)
    (scans : ∀ side, owner ∉ (phase.drain (raw side)).native.failureOwnersBefore event.val)
    (actions : Bool → ((graph).outputLayout event).Action)
    (recorded : ∀ side, (⟨event, actions side⟩ : (graph).Completion) ∈
      (phase.drain (raw side)).native.config.history)
    (counts : Bool → Nat)
    (paths : ∀ side, (ending side).execution ∈ ((app).runRounds
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) (counts side)
        (anchor.respond app actor (responses side))).support)
    (afterProcessing : ReservedEpoch.packetCapacity runtime ≤ anchor.environmentRecall.length %
      ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime))
    (finals : Bool → ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).History)
    (supports : ∀ side,
      let horizon := ReservedEpoch.executionHorizon runtime
      let scheduler := ReservedEpoch.family runtime leaks
        (ReservedEpoch.packetCapacity runtime) tape
      let start := anchor.respond app actor (responses side)
      let players := ReactiveApplication.anchoredPolicy start
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
      let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
      let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
        match history.state with
        | none => False
        | some control => control.execution.application.attempt ≠ start.application.attempt
      finals side ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded _ horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, start⟩, starts side⟩).support)
    (finalStates : ∀ side, (finals side).state = some (ending side))
    (finalKept : ∀ side, TracePrefix
      ((priors side).extend (joints side) (legal side) (realized side)) (finals side).trace) :
    PhaseProposal.publicationDiscloses ((graph).outputLayout event) (actions false) =
      PhaseProposal.publicationDiscloses ((graph).outputLayout event) (actions true) := by
  classical
  let horizon := ReservedEpoch.executionHorizon runtime
  let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  obtain ⟨payload, _name, selected, checks, output, code, value, locked⟩ :=
    checkpoint.publication_binding_row setup mode phase installed kind stored event inside owner
      acting proper
  have node := nodeView_eq_resolve output code
  by_cases request : anchor.application.SeedRequest owner ⟨anchor.application.attempt, event⟩
  · obtain ⟨draw, invariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
      scheduler ((menu).toRawTrace initial horizon scheduler (starts false))
    have native : anchor.application.current.native.Invariant draw := by
      simpa only [applications false] using invariant.active
    obtain ⟨entered, stamp⟩ := native.activatedAt_eq_some_of_ready_actor event request.2.2.1
      (by simp only [acting, Option.isSome_some])
    have positive : 0 < runtime.deadline event := by
      have room := margin event (by simp only [acting, Option.isSome_some])
      omega
    have bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values := by
      have covered := coveredValues event
      rw [output] at covered
      exact covered value
    have receipt := publication_old_foreign_receipt setup mode runtime leaks bounds plan values
      tape remaining anchor actor owner different (responses false) (responses true)
        (applications false) (applications true) (starts false) (starts true)
          (counts false) (counts true) (ending false) (ending true) (idle false) (idle true)
            ((priors false).extend (joints false) (legal false) (realized false))
            ((priors true).extend (joints true) (legal true) (realized true))
            (.extend (kept false) _ _ _) (.extend (kept true) _ _ _)
            (by simpa only [applications false] using changed false)
            (by simpa only [applications true] using changed true)
            event payload (checkpoint.refs.get selected) checks output code node value locked
              bounded request entered stamp positive afterProcessing (paths false) (paths true)
    have exactBit : ∀ side, PhaseService.BindingAccepted runtime leaks
        ⟨anchor.application.attempt, event⟩ owner (ending side).execution ↔
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) (actions side) =
            true := by
      intro side
      have factual := ReservedEpoch.publication_unresolved_receipt_iff_recorded runtime leaks bounds
        plan inputs horizon scheduler ⟨remaining, none, anchor.respond app actor (responses side)⟩
          (closing side) (ending side) (starts side) (priors side) (joints side) (legal side)
            (realized side) (kept side) (by simpa only [applications side] using (same side).symm)
              (raw side) (effects side) event phase (closingInstalled side) inside payload output
                ordered (by simpa only [same side] using changed side) (actions side)
                  (recorded side) owner (fun resolved =>
                    resolved.not_request _ _ owner
                      (by simpa only [applications side] using request)) acting
      have sameBit : cast (congrArg EventField.Action output) (actions side) =
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) (actions side) :=
        PhaseProposal.publicationDiscloses_cast output (actions side)
      rw [sameBit] at factual
      simpa only [applications side] using factual
    exact Bool.eq_iff_iff.mpr ((exactBit false).symm.trans (receipt.trans (exactBit true)))
  · have disclosed : ∀ side, cast (congrArg EventField.Action output) (actions side) = true := by
      intro side
      exact phaseProposalUnflagged_fresh_opening_disclosure setup mode runtime leaks bounds plan
        coveredValues maximal ordered values tape activationGap processingGap gaps margin remaining
          (anchor.respond app actor (responses side)) (starts side) (closing side) (ending side)
            (priors side) (joints side) (legal side) (realized side) (kept side)
              (by simpa only [applications side] using same side)
              (by simpa only [applications side] using changed side) phase
              (by simpa only [applications side] using installed) kind (raw side) (effects side)
              (coverage side) (excluded side) event inside owner acting
              (by simpa only [applications side] using active) payload
                (checkpoint.refs.get selected)
                checks output code node value (by simpa only [applications side] using locked)
                  (scans side) (actions side) (recorded side)
                  (fun old => request (by simpa only [applications side] using old.1))
                  (finals side) (by
                    convert supports side using 1
                    congr 2
                    funext history
                    cases history.state <;> rfl) (finalStates side) (finalKept side)
    exact (PhaseProposal.publicationDiscloses_cast output (actions false)).symm.trans
      ((disclosed false).trans ((disclosed true).symm.trans
        (PhaseProposal.publicationDiscloses_cast output (actions true))))

/-- Completion freezes this coordinate's accepting-receipt bit along the
actual physical history. Existing TRUE receipts remain, including openings
whose guarded native result failed. -/
private theorem publication_resolved_receipt_word
    (horizon : Nat) (scheduler : (app).Scheduler)
    (start final : (app).Control)
    (startTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
    (finalTrace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (kept : TracePrefix startTrace finalTrace)
    (coordinate : CommitAttemptEvent graph)
    (resolved : coordinate.Resolved start.execution.application) (owner : Player) :
    PhaseService.BindingAccepted runtime leaks coordinate owner final.execution ↔
      PhaseService.BindingAccepted runtime leaks coordinate owner start.execution := by
  classical
  let rawStart := (menu).toRawTrace initial horizon scheduler startTrace
  let rawFinal := (menu).toRawTrace initial horizon scheduler finalTrace
  constructor
  · rintro ⟨message, input, sender, address, named, receipt⟩
    by_cases old : (message.id, true) ∈ start.execution.receipts
    · have identifiers := (app).receipt_identifiers_history initial horizon scheduler start rawStart
      have oldId : message.id ∈ start.execution.network.ledger.map Message.id := by
        rw [← identifiers]
        exact List.mem_map.mpr ⟨(message.id, true), old, rfl⟩
      obtain ⟨actual, ledger, sameId⟩ := List.mem_map.mp oldId
      have oldInput := (app).ledger_subset_inputs_history initial horizon scheduler start rawStart
        ledger
      have retained := ReservedEpoch.input_mem_prefix runtime leaks menu initial horizon scheduler
        start final startTrace finalTrace kept actual oldInput
      have identical := (app).input_identifier_injective_history initial horizon scheduler final
        rawFinal actual message retained input sameId
      subst actual
      exact ⟨message, oldInput, sender, address, named, old⟩
    · obtain ⟨before, after, prior, joint, legal, realized, fromStart, toFinal, absent, _selected,
        moved, accepted⟩ := ReservedEpoch.prefix_accepting_receipt_boundary runtime leaks menu
          initial horizon scheduler start final startTrace finalTrace kept message.id old receipt
      have beforeFinal : TracePrefix prior finalTrace :=
        (TracePrefix.extend .refl joint legal realized).trans toFinal
      let rawBefore := (menu).toRawTrace initial horizon scheduler prior
      have found : before.execution.network.lookup message.id = some message := by
        cases lookup : before.execution.network.lookup message.id with
        | none =>
            have unchanged := moved
            simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at unchanged
            have literal := (PMF.mem_support_pure_iff _ _).mp unchanged
            have receiptsEq := congrArg (fun execution : (app).Execution => execution.receipts)
              literal
            have sameReceipts : after.execution.receipts = before.execution.receipts := by
              simpa only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending,
                lookup] using receiptsEq
            exact (absent (sameReceipts ▸ accepted)).elim
        | some actual =>
            have pending := List.mem_of_find?_eq_some lookup
            have actualInput := ((app).retained_envelopes_mem_inputs before.execution
              ((app).history_provenance initial horizon scheduler rawBefore)
              ((app).history_inputRecall initial horizon scheduler rawBefore)).pending actual
                pending
            have atEnd := ReservedEpoch.input_mem_prefix runtime leaks menu initial horizon
              scheduler
              before final prior finalTrace beforeFinal actual actualInput
            have sameId : actual.id = message.id := by
              simpa only [decide_eq_true_eq] using List.find?_some lookup
            exact congrArg some ((app).input_identifier_injective_history initial horizon scheduler
              final rawFinal actual message atEnd input sameId)
      have pending := List.mem_of_find?_eq_some found
      have acceptingInput := ((app).retained_envelopes_mem_inputs before.execution
        ((app).history_provenance initial horizon scheduler rawBefore)
        ((app).history_inputRecall initial horizon scheduler rawBefore)).pending message pending
      obtain ⟨_native, following, handled, _nativeHandled⟩ := ReservedEpoch.accepting_include_native
        runtime leaks plan inputs horizon scheduler before rawBefore after.execution message
          acceptingInput absent moved accepted
      have preserved := phase_resolved_prefix runtime leaks menu plan inputs horizon scheduler
        start before startTrace prior fromStart coordinate resolved
      have unfinished := PhaseRuntimeState.handle_event_unresolved runtime
        before.execution.application
        following message coordinate.event named handled
      exact (unfinished (by simpa only [address] using preserved)).elim
  · rintro ⟨message, input, sender, address, named, receipt⟩
    refine ⟨message, ReservedEpoch.input_mem_prefix runtime leaks menu initial horizon scheduler
      start final startTrace finalTrace kept message input, sender, address, named, ?_⟩
    exact ((app).reaches_receipts_prefix initial horizon scheduler
      ((menu).reaches_raw initial horizon scheduler kept.reachesWithin) start final rfl rfl).subset
        receipt

/-- A publication removed by its literal source prefix has no physical
proposal, no TRUE receipt and no TRUE action in the original stopped image. -/
private theorem publication_suppressed_row_word
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before ending : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (phase : RuntimePhase graph) (installed : phase ∈ before.execution.application.phases.head?)
    (kind : phase.kind = .reveal) (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (event : (graph).EventId) (inside : event ∈ phase.events) (owner : Player)
    (acting : (graph).actor? event = some owner)
    (saved : before.execution.application.entry.native.config.cut.IsPrefix phase.low)
    (kept : KeepsStore before.execution.application.current.native (phase.drain raw).native)
    (frame : before.execution.application.entry.native.PublicFailureExtension
      (phase.drain raw).native)
    (suppressed : owner ∈ before.execution.application.entry.excluded ∪
      (phase.drain raw).native.failureOwnersBefore event.val) :
    (∀ value, (⟨before.execution.application.attempt, event⟩, value) ∉
      PhaseProposal.archive ending.execution.network.inputs) ∧
    ¬ PhaseService.BindingAccepted runtime leaks ⟨before.execution.application.attempt, event⟩
      owner ending.execution ∧
    ∀ action : ((graph).outputLayout event).Action,
      (⟨event, action⟩ : (graph).Completion) ∈ (phase.drain raw).native.config.history →
        PhaseProposal.publicationDiscloses ((graph).outputLayout event) action = false := by
  classical
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  have inputEq : ending.execution.network.inputs = before.execution.network.inputs := by
    rcases effect with ⟨id, message, native, _found, moved, _handled, _raw⟩ |
        ⟨command, native, moved, _supported, _raw⟩
    · exact (app).environmentStep_inputs _ _ (.include id) moved
    · exact (app).environmentStep_inputs _ _ (.application command) moved
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) prior
  obtain ⟨payload, publication⟩ := kind ▸ phase.fields event
    ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
  have absent : ∀ value, (⟨before.execution.application.attempt, event⟩, value) ∉
      PhaseProposal.archive ending.execution.network.inputs := by
    intro value proposed
    obtain ⟨message, input, claim⟩ := (PhaseProposal.mem_archive _ _).mp proposed
    rw [inputEq] at input
    obtain ⟨_address, candidate, call⟩ := PhaseProposal.opening_of_packetProposal _ _ _ claim
    have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)).2.1
    have owned := countCallCorrect_owned_event _ (PhaseCount.nativeMessage message) correct
      (by change Payload.event? graph message.payload.packet.call = some event; rw [call]; rfl)
    have sender : message.sender = owner := Option.some.inj (owned.symm.trans acting)
    have permitted := PhaseProposal.submitted_proposal_owner_not_in_scan runtime leaks bounds plan
      ordered inputs horizon scheduler before prior phase kind message input
        ⟨before.execution.application.attempt, event⟩ value claim rfl inside saved
          (phase.drain raw).native kept frame
    exact permitted (sender.symm ▸ suppressed)
  refine ⟨absent, ?_, ?_⟩
  · rintro ⟨message, input, _sender, address, named, _received⟩
    have earlier : message ∈ before.execution.network.inputs := by rwa [inputEq] at input
    have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message earlier)).2.1
    have opening : ∃ candidate value,
        message.payload.packet.call = .opening event candidate value :=
        by
      cases call : message.payload.packet.call with
      | malformed value => rw [call] at named; cases named
      | commitment other candidate =>
          have same : other = event := Option.some.inj (by
            simpa only [call, Payload.event?] using named)
          subst other
          simp only [CountCallCorrect, PhaseCount.nativeMessage, call, bindingOwnedBy, publication,
            Bool.false_eq_true, false_and] at correct
      | opening other candidate value =>
          have same : other = event := Option.some.inj (by
            simpa only [call, Payload.event?] using named)
          subst other
          exact ⟨candidate, value, rfl⟩
    obtain ⟨candidate, value, call⟩ := opening
    exact absent value ((PhaseProposal.mem_archive _ _).mpr ⟨message, input, by
      simp only [PhaseProposal.packetProposal?, call, address]⟩)
  · intro action recorded
    apply Bool.eq_false_of_not_eq_true
    intro disclosed
    have trueAction : cast (congrArg EventField.Action publication) action = true :=
      (PhaseProposal.publicationDiscloses_cast publication action).trans disclosed
    obtain ⟨message, candidate, value, input, address, call, _receipt⟩ :=
      ReservedEpoch.closing_disclosure_has_receipt runtime leaks bounds plan ordered inputs horizon
        scheduler before prior ending.execution raw changed effect phase installed event inside
          payload publication action recorded trueAction
    exact absent value ((PhaseProposal.mem_archive _ _).mpr ⟨message, input, by
      simp only [PhaseProposal.packetProposal?, call, address]⟩)

/-- Every foreign owner's semantic publication word agrees on both actual
supports, including its first rejecting guard and the suppressed owned suffix. -/
private theorem publication_foreign_word
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (remaining : Nat) (anchor : (app).Execution) (actor owner : Player)
    (different : owner ≠ actor) (responses : Bool → (app).Action)
    (applications : ∀ side, (anchor.respond app actor (responses side)).application =
      anchor.application)
    (starts : ∀ side, ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, anchor.respond app actor (responses side)⟩))
    (checkpoint : RecoverySourceCheckpoint setup mode anchor.application)
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (kind : phase.kind = .reveal) (stored : anchor.application.StoredCheckpoint)
    (proper : ∀ who, who ∉ anchor.application.current.excluded →
      checkpoint.source.BindingsHoldValues who)
    (closing ending : Bool → (app).Control)
    (idle : ∀ side, (ending side).actor = none)
    (priors : ∀ side, ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some (closing side)))
    (joints : Bool → Player → Option (app).Action)
    (legal : ∀ side, ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Legal
        (some (closing side)) (joints side))
    (realized : ∀ side, some (ending side) ∈ ((app).transition initial
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
        (some (closing side)) (joints side)).support)
    (kept : ∀ side, TracePrefix (starts side) (priors side))
    (same : ∀ side, (closing side).execution.application.attempt = anchor.application.attempt)
    (changed : ∀ side, (ending side).execution.application.attempt ≠ anchor.application.attempt)
    (closingInstalled : ∀ side, phase ∈ (closing side).execution.application.phases.head?)
    (raw : Bool → RecoveryState graph)
    (effects : ∀ side, PhaseClosingEffect runtime leaks (closing side).execution
      (ending side).execution (raw side))
    (coverage : ∀ side, (phase.drain (raw side)).FailureCoverage)
    (excluded : ∀ side, (phase.drain (raw side)).excluded =
      (ending side).execution.application.current.excluded)
    (finished : ∀ side, phase.Finished (phase.drain (raw side)))
    (counts : Bool → Nat)
    (paths : ∀ side, (ending side).execution ∈ ((app).runRounds
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) (counts side)
        (anchor.respond app actor (responses side))).support)
    (afterProcessing : ReservedEpoch.packetCapacity runtime ≤ anchor.environmentRecall.length %
      ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime))
    (finals : Bool → ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).History)
    (supports : ∀ side,
      let horizon := ReservedEpoch.executionHorizon runtime
      let scheduler := ReservedEpoch.family runtime leaks
        (ReservedEpoch.packetCapacity runtime) tape
      let start := anchor.respond app actor (responses side)
      let players := ReactiveApplication.anchoredPolicy start
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
      let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
      let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
        match history.state with
        | none => False
        | some control => control.execution.application.attempt ≠ start.application.attempt
      finals side ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded _ horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, start⟩, starts side⟩).support)
    (finalStates : ∀ side, (finals side).state = some (ending side))
    (finalKept : ∀ side, TracePrefix
      ((priors side).extend (joints side) (legal side) (realized side)) (finals side).trace) :
    ∀ event ∈ phase.events, (graph).actor? event = some owner →
      (phase.drain (raw false)).native.config.outputs event =
          (phase.drain (raw true)).native.config.outputs event ∧
      (PhaseService.BindingAccepted runtime leaks ⟨anchor.application.attempt, event⟩ owner
          (ending false).execution ↔
        PhaseService.BindingAccepted runtime leaks ⟨anchor.application.attempt, event⟩ owner
          (ending true).execution) ∧
      (∀ leftAction rightAction,
        (⟨event, leftAction⟩ : (graph).Completion) ∈
          (phase.drain (raw false)).native.config.history →
        (⟨event, rightAction⟩ : (graph).Completion) ∈
          (phase.drain (raw true)).native.config.history →
        PhaseProposal.publicationDiscloses ((graph).outputLayout event) leftAction =
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) rightAction) ∧
      ∀ value : Raw L,
        (⟨anchor.application.attempt, event⟩, value) ∈
            PhaseProposal.archive (ending false).execution.network.inputs ↔
          (⟨anchor.application.attempt, event⟩, value) ∈
            PhaseProposal.archive (ending true).execution.network.inputs := by
  classical
  let horizon := ReservedEpoch.executionHorizon runtime
  let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
  let image := fun side => phase.drain (raw side)
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have anchorRecord : anchor.application.ExclusionRecord := by
    have actual := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
      ((menu).toRawTrace initial horizon scheduler (starts false))
    simpa only [applications false] using actual
  have anchorCoverage : anchor.application.FailureCoverage := by
    have actual := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
      ((menu).toRawTrace initial horizon scheduler (starts false))
    simpa only [applications false] using actual
  obtain ⟨remainingPhases, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have positioned := anchorRecord.frontier.positioned
  rw [phases] at positioned
  have entries : ∀ side, (closing side).execution.application.entry = anchor.application.entry := by
    intro side
    have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized ((menu).toRawTrace initial horizon scheduler (starts side))
    have progress := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon scheduler _ _ (starts side) (priors side) (kept side) firstOrdered).2.2
        (by simpa only [applications side] using (same side).symm)
    exact progress.symm.trans (congrArg PhaseRuntimeState.entry (applications side))
  have closingStores : ∀ side, KeepsStore (closing side).execution.application.current.native
      (image side).native := by
    intro side
    have rawStore : KeepsStore (closing side).execution.application.current.native
        (raw side).native := by
      rcases effects side with ⟨id, message, native, _found, _moved, handled, rawEq⟩ |
          ⟨command, native, _moved, supported, rawEq⟩
      · rw [rawEq]
        exact handle_store_of_some runtime _ native _ handled
      · rw [rawEq]
        exact environmentStep_store_of_some runtime _ native command supported
    exact fun field value present => phase.drain_keepsStore (raw side) field value
      (rawStore field value present)
  have keptStores : ∀ side, KeepsStore anchor.application.current.native (image side).native := by
    intro side
    have first := PhaseProposal.same_attempt_prefix_keeps_store runtime leaks menu initial
      initialized horizon scheduler _ _ (starts side) (priors side) (kept side)
        (by simpa only [applications side] using (same side).symm)
    exact fun field value present => closingStores side field value
      (first field value (by simpa only [applications side] using present))
  have histories : ∀ side, anchor.application.current.native.config.history.IsPrefix
      (image side).native.config.history := by
    intro side
    have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized ((menu).toRawTrace initial horizon scheduler (starts side))
    have retained := phase_prefix_semantic_extension runtime leaks menu initial horizon
      scheduler
      _ _ (starts side) (priors side) (kept side) firstOrdered
        (by simpa only [applications side] using (same side).symm)
    have second := ReservedEpoch.phaseClosingEffect_history_prefix runtime leaks
      (closing side).execution (ending side).execution (raw side) (effects side)
    simpa only [applications side] using
      retained.2.trans (second.trans (phase.drain_history_prefix (raw side)))
  have frames : ∀ side, anchor.application.entry.native.PublicFailureExtension
      (image side).native := by
    intro side
    have rawFrame := phaseClosingEffect_failure_frame setup mode runtime leaks bounds plan
      horizon scheduler (closing side) (ending side) (priors side) (raw side) (effects side)
    change (closing side).execution.application.entry.native.PublicFailureExtension
      (raw side).native at rawFrame
    rw [entries side] at rawFrame
    exact rawFrame.trans
      (phase.drain_publicFailureExtension (raw side))
  have sourceOrders : ∀ side,
      (image side).OrderedPublicFailures phase.low anchor.application.entry.excluded := by
    intro side
    have actual := phaseClosingEffect_publication_order setup mode runtime leaks bounds plan
      horizon scheduler (closing side) (ending side) (priors side) phase
        (Option.mem_def.mp (closingInstalled side)) (raw side) (effects side)
          (by simpa only [same side] using changed side)
    simpa only [entries side] using actual
  have reached : ∀ side,
      (image side).native.config.Reachable (image side).native.config.inputs := by
    intro side
    obtain ⟨draw, actual⟩ := publication_closing_image_reachable runtime leaks plan inputs horizon
      scheduler (closing side) ((menu).toRawTrace initial horizon scheduler (priors side))
        (ending side).execution (raw side) (effects side) phase
    change (phase.drain (raw side)).native.config.Reachable
      (phase.drain (raw side)).native.config.inputs
    rw [actual.inputs_eq]
    exact actual
  have sameInputs : (image false).native.config.inputs = (image true).native.config.inputs := by
    funext input
    exact Option.some.inj ((keptStores false (.inl input) _ rfl).trans
      (keptStores true (.inl input) _ rfl).symm)
  have fixed : ∀ event : (graph).EventId, event.val < phase.low →
      (image false).native.config.outputs event = (image true).native.config.outputs event := by
    intro event below
    obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp
      ((anchor.application.current.native.config.output_available event).mpr
        (positioned.2.1 event below))
    exact (keptStores false (.inr event) value present).trans
      (keptStores true (.inr event) value present).symm
  have rows : ∀ event ∈ phase.events, (graph).actor? event = some owner →
      owner ∉ anchor.application.entry.excluded →
      (¬ ∃ prior ∈ phase.events, prior.val < event.val ∧
        (graph).actor? prior = some owner ∧ (image false).native.PublicFailure prior) →
      (∀ prior ∈ phase.events, prior.val < event.val → (graph).actor? prior = some owner →
        (image false).native.config.outputs prior = (image true).native.config.outputs prior) →
      ∃ leftAction rightAction,
        (⟨event, leftAction⟩ : (graph).Completion) ∈ (image false).native.config.history ∧
        (⟨event, rightAction⟩ : (graph).Completion) ∈ (image true).native.config.history ∧
        PhaseProposal.publicationDiscloses ((graph).outputLayout event) leftAction =
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) rightAction := by
    intro event inside acting inherited noEarlier earlier
    by_cases completed : event ∈ anchor.application.current.native.config.cut.completed
    · obtain ⟨action, leftRecorded, rightRecorded⟩ := publication_completed_row setup mode
        anchor.application.current.native (image false).native (image true).native
          (histories false) (histories true) event completed
      exact ⟨action, action, leftRecorded, rightRecorded, rfl⟩
    have scans : ∀ side, owner ∉ (image side).native.failureOwnersBefore event.val := by
      intro side scanned
      obtain ⟨prior, before, owned, failed⟩ := (Finset.mem_filter.mp scanned).2
      by_cases low : prior.val < phase.low
      · have old := (frames side).failures prior ((positioned.1.2 prior).mpr low)
        exact inherited (anchorCoverage.saved.covered prior owner owned (old.mp failed))
      have priorInside : prior ∈ phase.events := (phase.mem_events prior).mpr ⟨by omega, by
        have upper := ((phase.mem_events event).mp inside).2
        omega⟩
      have leftFailure : (image false).native.PublicFailure prior := by
        cases side with
        | false => exact failed
        | true =>
            obtain ⟨payload, publication⟩ := kind ▸ phase.fields prior
              ((phase.mem_events prior).mp priorInside).1
              ((phase.mem_events prior).mp priorInside).2
            have equalFailure : (image false).native.PublicFailure prior ↔
                (image true).native.PublicFailure prior := by
              simp only [State.PublicFailure, PublicView.missedBinding, publication,
                Bool.false_eq_true, false_or]
              unfold RecoveryState.publicationFailed
              rw [earlier prior priorInside before owned]
            exact equalFailure.mpr failed
      exact noEarlier ⟨prior, priorInside, before, owned, leftFailure⟩
    have active := publication_unfinished_source_active_anchor_active ordered anchor.application
      phase kind (anchorRecord.installed phase installed) positioned.2 (image false).native
        (keptStores false) event owner acting completed inherited (scans false)
    obtain ⟨left, leftRecorded, _leftEvent⟩ := List.mem_map.mp
      (((image false).native.config.history_exact event).mpr (finished false inside))
    rcases left with ⟨leftEvent, leftAction⟩
    change leftEvent = event at _leftEvent
    subst leftEvent
    obtain ⟨right, rightRecorded, _rightEvent⟩ := List.mem_map.mp
      (((image true).native.config.history_exact event).mpr (finished true inside))
    rcases right with ⟨rightEvent, rightAction⟩
    change rightEvent = event at _rightEvent
    subst rightEvent
    let actions := fun (side : Bool) => if side then rightAction else leftAction
    have recorded : ∀ side, (⟨event, actions side⟩ : (graph).Completion) ∈
        (image side).native.config.history := by
      intro side
      cases side
      · exact leftRecorded
      · exact rightRecorded
    have bits := publication_unfinished_foreign_disclosures_eq setup mode runtime leaks bounds plan
      coveredValues maximal values tape activationGap processingGap gaps margin remaining anchor
        actor owner different responses applications starts checkpoint phase installed kind stored
          event inside acting active (proper owner active) closing ending idle priors joints legal
            realized kept same changed closingInstalled raw effects coverage excluded scans actions
              recorded counts paths afterProcessing finals supports finalStates finalKept
    exact ⟨leftAction, rightAction, leftRecorded, rightRecorded, bits⟩
  have outputs := publication_owner_outputs_eq setup mode checkpoint phase installed kind
    (image false) (image true) (reached false) (reached true) sameInputs fixed
      anchor.application.entry.excluded (sourceOrders false) (sourceOrders true)
        (finished false) (finished true) owner rows
  have actionsUnique : ∀ side (event : (graph).EventId)
      (first second : ((graph).outputLayout event).Action),
      (⟨event, first⟩ : (graph).Completion) ∈ (image side).native.config.history →
      (⟨event, second⟩ : (graph).Completion) ∈ (image side).native.config.history →
        first = second := by
    intro side event first second before after
    exact eq_of_heq (EventGraph.Completion.mk.inj
      (List.inj_on_of_nodup_map (image side).native.config.history_nodup before after rfl)).2
  have bits : ∀ event ∈ phase.events, (graph).actor? event = some owner →
      ∀ leftAction rightAction,
        (⟨event, leftAction⟩ : (graph).Completion) ∈ (image false).native.config.history →
        (⟨event, rightAction⟩ : (graph).Completion) ∈ (image true).native.config.history →
        PhaseProposal.publicationDiscloses ((graph).outputLayout event) leftAction =
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) rightAction := by
    intro event inside acting leftAction rightAction leftRecorded rightRecorded
    by_cases completed : event ∈ anchor.application.current.native.config.cut.completed
    · obtain ⟨common, first, second⟩ := publication_completed_row setup mode
        anchor.application.current.native (image false).native (image true).native
          (histories false) (histories true) event completed
      rw [actionsUnique false event leftAction common leftRecorded first,
        actionsUnique true event rightAction common rightRecorded second]
    have earlierFailure : ∀ prior : (graph).EventId, prior.val < event.val →
        (graph).actor? prior = some owner →
        ((image false).native.PublicFailure prior ↔ (image true).native.PublicFailure prior) := by
      intro prior before owned
      by_cases low : prior.val < phase.low
      · exact ((frames false).failures prior ((positioned.1.2 prior).mpr low)).trans
          ((frames true).failures prior ((positioned.1.2 prior).mpr low)).symm
      have priorInside : prior ∈ phase.events := (phase.mem_events prior).mpr ⟨by omega, by
        have upper := ((phase.mem_events event).mp inside).2
        omega⟩
      obtain ⟨payload, publication⟩ := kind ▸ phase.fields prior
        ((phase.mem_events prior).mp priorInside).1 ((phase.mem_events prior).mp priorInside).2
      simp only [State.PublicFailure, PublicView.missedBinding, publication,
        Bool.false_eq_true, false_or]
      unfold RecoveryState.publicationFailed
      rw [outputs prior priorInside owned]
    by_cases suppressed : owner ∈ anchor.application.entry.excluded ∪
        (image false).native.failureOwnersBefore event.val
    · have suppressedRight : owner ∈ anchor.application.entry.excluded ∪
          (image true).native.failureOwnersBefore event.val := by
        rcases Finset.mem_union.mp suppressed with old | scanned
        · exact Finset.mem_union_left _ old
        obtain ⟨prior, before, owned, failed⟩ := (Finset.mem_filter.mp scanned).2
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ owner,
          ⟨prior, before, owned, (earlierFailure prior before owned).mp failed⟩⟩)
      have suppressedWord : ∀ side, ∀ action,
          (⟨event, action⟩ : (graph).Completion) ∈ (image side).native.config.history →
            PhaseProposal.publicationDiscloses ((graph).outputLayout event) action = false := by
        intro side
        have selected : owner ∈ anchor.application.entry.excluded ∪
            (image side).native.failureOwnersBefore event.val := by
          cases side
          · exact suppressed
          · exact suppressedRight
        exact (publication_suppressed_row_word setup mode runtime leaks bounds plan horizon
          scheduler (closing side) (ending side) (priors side) phase (closingInstalled side) kind
            (raw side) (effects side) (by simpa only [same side] using changed side) event inside
              owner acting (by simpa only [entries side] using positioned.1) (closingStores side)
                (by simpa only [entries side] using frames side)
                (by simpa only [entries side] using selected)).2.2
      exact (suppressedWord false leftAction leftRecorded).trans
        (suppressedWord true rightAction rightRecorded).symm
    · have inherited : owner ∉ anchor.application.entry.excluded :=
        fun old => suppressed (Finset.mem_union_left _ old)
      have noEarlier : ¬ ∃ prior ∈ phase.events, prior.val < event.val ∧
          (graph).actor? prior = some owner ∧ (image false).native.PublicFailure prior := by
        rintro ⟨prior, _inside, before, owned, failed⟩
        exact suppressed (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ owner, prior, before, owned, failed⟩))
      obtain ⟨first, second, firstRecorded, secondRecorded, sameBit⟩ := rows event inside acting
        inherited noEarlier (fun prior priorInside _before owned => outputs prior priorInside owned)
      rw [actionsUnique false event leftAction first leftRecorded firstRecorded,
        actionsUnique true event rightAction second rightRecorded secondRecorded]
      exact sameBit
  have ownInputs :
      ((anchor.respond app actor (responses false)).network.inputs.filter
        (fun message => message.sender = owner)) =
      ((anchor.respond app actor (responses true)).network.inputs.filter
        (fun message => message.sender = owner)) := by
    rw [(app).history_inputRecall initial horizon scheduler
      ((menu).toRawTrace initial horizon scheduler (starts false)) owner,
      (app).history_inputRecall initial horizon scheduler
      ((menu).toRawTrace initial horizon scheduler (starts true)) owner,
      (app).respond_recall_other anchor actor owner different (responses false),
      (app).respond_recall_other anchor actor owner different (responses true)]
  have initialAccepted : ∀ coordinate, PhaseService.BindingAccepted runtime leaks coordinate owner
      (anchor.respond app actor (responses false)) ↔
        PhaseService.BindingAccepted runtime leaks coordinate owner
          (anchor.respond app actor (responses true)) := by
    intro coordinate
    constructor
    · rintro ⟨message, input, sender, address, named, receipt⟩
      have listed : message ∈ (anchor.respond app actor (responses true)).network.inputs := by
        have listed : message ∈ ((anchor.respond app actor (responses false)).network.inputs.filter
            (fun packet => packet.sender = owner)) :=
          List.mem_filter.mpr ⟨input, by simp only [sender, decide_true]⟩
        rw [ownInputs] at listed
        exact (List.mem_filter.mp listed).1
      exact ⟨message, listed, sender, address, named, by
        simpa only [(app).respond_receipts] using receipt⟩
    · rintro ⟨message, input, sender, address, named, receipt⟩
      have listed : message ∈ (anchor.respond app actor (responses false)).network.inputs := by
        have listed : message ∈ ((anchor.respond app actor (responses true)).network.inputs.filter
            (fun packet => packet.sender = owner)) :=
          List.mem_filter.mpr ⟨input, by simp only [sender, decide_true]⟩
        rw [← ownInputs] at listed
        exact (List.mem_filter.mp listed).1
      exact ⟨message, listed, sender, address, named, by
        simpa only [(app).respond_receipts] using receipt⟩
  have closingInputs : ∀ side,
      (ending side).execution.network.inputs = (closing side).execution.network.inputs := by
    intro side
    rcases effects side with ⟨id, message, native, _found, moved, _handled, _raw⟩ |
        ⟨command, native, moved, _supported, _raw⟩
    · exact (app).environmentStep_inputs _ _ (.include id) moved
    · exact (app).environmentStep_inputs _ _ (.application command) moved
  have archiveWord : ∀ event ∈ phase.events, (graph).actor? event = some owner →
      ∀ value : Raw L,
        (⟨anchor.application.attempt, event⟩, value) ∈
            PhaseProposal.archive (ending false).execution.network.inputs ↔
          (⟨anchor.application.attempt, event⟩, value) ∈
            PhaseProposal.archive (ending true).execution.network.inputs := by
    intro event inside acting
    have senderOfClaim : ∀ side message, message ∈ (ending side).execution.network.inputs →
        ∀ value, PhaseProposal.packetProposal? message.payload =
          some (⟨anchor.application.attempt, event⟩, value) → message.sender = owner := by
      intro side message input value claim
      have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
        initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state)
          ((priors side).extend (joints side) (legal side) (realized side))
      have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)).2.1
      obtain ⟨_address, candidate, call⟩ := PhaseProposal.opening_of_packetProposal _ _ _ claim
      have owned := countCallCorrect_owned_event _ (PhaseCount.nativeMessage message) correct
        (by change Payload.event? graph message.payload.packet.call = some event; rw [call]; rfl)
      exact Option.some.inj (owned.symm.trans acting)
    by_cases completed : event ∈ anchor.application.current.native.config.cut.completed
    · have origin : ∀ side message, message ∈ (ending side).execution.network.inputs →
          ∀ value, PhaseProposal.packetProposal? message.payload =
            some (⟨anchor.application.attempt, event⟩, value) →
              message ∈ (anchor.respond app actor (responses side)).network.inputs := by
        intro side message input value claim
        have sender := senderOfClaim side message input value claim
        obtain ⟨address, candidate, call⟩ := PhaseProposal.opening_of_packetProposal _ _ _ claim
        exact ReservedEpoch.resolved_counted_packet_origin runtime leaks bounds plan ordered
          inputs
          horizon scheduler ⟨remaining, none, anchor.respond app actor (responses side)⟩
            (ending side) (starts side)
              ((priors side).extend (joints side) (legal side) (realized side))
                (.extend (kept side) _ _ _) rfl owner ⟨anchor.application.attempt, event⟩
                  (Or.inr (Or.inr ⟨by rw [applications side], by
                    simpa only [applications side] using completed⟩)) message input sender
                    (by simp only [PhaseCount.event?, call, Payload.event?, Option.map_some,
                      address])
      intro value
      constructor
      · intro member
        obtain ⟨message, input, claim⟩ := (PhaseProposal.mem_archive _ _).mp member
        have old := origin false message input value claim
        have sender := senderOfClaim false message input value claim
        have listed : message ∈ ((anchor.respond app actor (responses false)).network.inputs.filter
            (fun packet => packet.sender = owner)) :=
          List.mem_filter.mpr ⟨old, by simp only [sender, decide_true]⟩
        rw [ownInputs] at listed
        exact (PhaseProposal.mem_archive _ _).mpr ⟨message,
          ReservedEpoch.input_mem_prefix runtime leaks menu initial horizon scheduler _ _
            (starts true) ((priors true).extend (joints true) (legal true) (realized true))
              (.extend (kept true) _ _ _) message (List.mem_filter.mp listed).1, claim⟩
      · intro member
        obtain ⟨message, input, claim⟩ := (PhaseProposal.mem_archive _ _).mp member
        have old := origin true message input value claim
        have sender := senderOfClaim true message input value claim
        have listed : message ∈ ((anchor.respond app actor (responses true)).network.inputs.filter
            (fun packet => packet.sender = owner)) :=
          List.mem_filter.mpr ⟨old, by simp only [sender, decide_true]⟩
        rw [← ownInputs] at listed
        exact (PhaseProposal.mem_archive _ _).mpr ⟨message,
          ReservedEpoch.input_mem_prefix runtime leaks menu initial horizon scheduler _ _
            (starts false) ((priors false).extend (joints false) (legal false) (realized false))
              (.extend (kept false) _ _ _) message (List.mem_filter.mp listed).1, claim⟩
    have earlierFailure : ∀ prior : (graph).EventId, prior.val < event.val →
        (graph).actor? prior = some owner →
        ((image false).native.PublicFailure prior ↔ (image true).native.PublicFailure prior) := by
      intro prior before owned
      by_cases low : prior.val < phase.low
      · exact ((frames false).failures prior ((positioned.1.2 prior).mpr low)).trans
          ((frames true).failures prior ((positioned.1.2 prior).mpr low)).symm
      have priorInside : prior ∈ phase.events := (phase.mem_events prior).mpr ⟨by omega, by
        have upper := ((phase.mem_events event).mp inside).2
        omega⟩
      obtain ⟨payload, publication⟩ := kind ▸ phase.fields prior
        ((phase.mem_events prior).mp priorInside).1 ((phase.mem_events prior).mp priorInside).2
      simp only [State.PublicFailure, PublicView.missedBinding, publication,
        Bool.false_eq_true, false_or]
      unfold RecoveryState.publicationFailed
      rw [outputs prior priorInside owned]
    have sameScan : owner ∈ (image false).native.failureOwnersBefore event.val ↔
        owner ∈ (image true).native.failureOwnersBefore event.val := by
      constructor
      · intro scanned
        obtain ⟨prior, before, owned, failed⟩ := (Finset.mem_filter.mp scanned).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ owner,
          ⟨prior, before, owned, (earlierFailure prior before owned).mp failed⟩⟩
      · intro scanned
        obtain ⟨prior, before, owned, failed⟩ := (Finset.mem_filter.mp scanned).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ owner,
          ⟨prior, before, owned, (earlierFailure prior before owned).mpr failed⟩⟩
    by_cases suppressed : owner ∈ anchor.application.entry.excluded ∪
        (image false).native.failureOwnersBefore event.val
    · have absent : ∀ side value, (⟨anchor.application.attempt, event⟩, value) ∉
          PhaseProposal.archive (ending side).execution.network.inputs := by
        intro side
        have selected : owner ∈ anchor.application.entry.excluded ∪
            (image side).native.failureOwnersBefore event.val := by
          cases side
          · exact suppressed
          · simpa only [Finset.mem_union, ← sameScan] using suppressed
        have word := publication_suppressed_row_word setup mode runtime leaks bounds plan horizon
          scheduler (closing side) (ending side) (priors side) phase (closingInstalled side) kind
            (raw side) (effects side) (by simpa only [same side] using changed side) event inside
              owner acting (by simpa only [entries side] using positioned.1) (closingStores side)
                (by simpa only [entries side] using frames side)
                (by simpa only [entries side] using selected)
        simpa only [same side] using word.1
      intro value
      exact iff_of_false (absent false value) (absent true value)
    have inherited : owner ∉ anchor.application.entry.excluded :=
      fun old => suppressed (Finset.mem_union_left _ old)
    have scans : ∀ side, owner ∉ (image side).native.failureOwnersBefore event.val := by
      intro side scanned
      have first : owner ∈ (image false).native.failureOwnersBefore event.val := by
        cases side
        · exact scanned
        · exact sameScan.mpr scanned
      exact suppressed (Finset.mem_union_right _ first)
    have active := publication_unfinished_source_active_anchor_active ordered anchor.application
      phase kind (anchorRecord.installed phase installed) positioned.2 (image false).native
        (keptStores false) event owner acting completed inherited (scans false)
    obtain ⟨payload, _name, selected, checks, output, code, value, locked⟩ :=
      checkpoint.publication_binding_row setup mode phase installed kind stored event inside owner
        acting (proper owner active)
    have node := nodeView_eq_resolve output code
    let claimed : Raw L := ⟨payload, value⟩
    have lockedClaim : ∀ side value,
        (⟨anchor.application.attempt, event⟩, value) ∈
          PhaseProposal.archive (ending side).execution.network.inputs → value = claimed := by
      intro side alleged member
      obtain ⟨message, input, claim⟩ := (PhaseProposal.mem_archive _ _).mp member
      rw [closingInputs side] at input
      obtain ⟨actual, rawEq, saved⟩ := PhaseProposal.submitted_proposal_current_binding_meaning
        runtime leaks bounds plan ordered inputs horizon scheduler (closing side) (priors side)
          message input ⟨anchor.application.attempt, event⟩ alleged claim (same side).symm owner
            payload (checkpoint.refs.get selected) checks output code
      have beforeRead := (checkpoint.refs.get selected).get?_preserved
        (closing side).execution.application.current.native.config.store
          (image side).native.config.store (closingStores side) _ saved
      have fixedRead := (checkpoint.refs.get selected).get?_preserved
        anchor.application.current.native.config.store (image side).native.config.store
          (keptStores side) _ locked
      have equal : actual = value := PublicationResult.success.inj
        (Option.some.inj (beforeRead.symm.trans fixedRead))
      subst actual
      exact rawEq
    have commonClaim :
        (⟨anchor.application.attempt, event⟩, claimed) ∈
            PhaseProposal.archive (ending false).execution.network.inputs ↔
          (⟨anchor.application.attempt, event⟩, claimed) ∈
            PhaseProposal.archive (ending true).execution.network.inputs := by
      by_cases request : anchor.application.SeedRequest owner ⟨anchor.application.attempt, event⟩
      · obtain ⟨draw, invariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
          scheduler ((menu).toRawTrace initial horizon scheduler (starts false))
        have native : anchor.application.current.native.Invariant draw := by
          simpa only [applications false] using invariant.active
        obtain ⟨entered, stamp⟩ := native.activatedAt_eq_some_of_ready_actor event request.2.2.1
          (by simp only [acting, Option.isSome_some])
        have positive : 0 < runtime.deadline event := by
          have room := margin event (by simp only [acting, Option.isSome_some])
          omega
        have bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values := by
          have covered := coveredValues event
          rw [output] at covered
          exact covered value
        have word : ∀ side,
            (⟨anchor.application.attempt, event⟩, claimed) ∈
                PhaseProposal.archive (ending side).execution.network.inputs ↔
              ReservedEpoch.openingFrontierEmission runtime leaks tape anchor owner event := by
          intro side
          have actual := publication_old_emission_word setup mode runtime leaks bounds plan values
            tape remaining (counts side) owner (anchor.respond app actor (responses side))
              (ending side) (idle side) (starts side)
                ((priors side).extend (joints side) (legal side) (realized side))
                (.extend (kept side) _ _ _) (by simpa only [applications side] using changed side)
                event payload (checkpoint.refs.get selected) checks output code node value
                  (by simpa only [applications side] using locked) bounded
                  (by simpa only [applications side] using request) entered
                  (by simpa only [applications side] using stamp) positive (paths side)
          have emitted :
              (⟨anchor.application.attempt, event⟩, claimed) ∈
                  PhaseProposal.archive (ending side).execution.network.inputs ↔
              ∃ message ∈ (ending side).execution.network.inputs, message.sender = owner ∧
                PhaseProposal.packetProposal? message.payload =
                  some (⟨anchor.application.attempt, event⟩, claimed) := by
            constructor
            · intro member
              obtain ⟨message, input, claim⟩ := (PhaseProposal.mem_archive _ _).mp member
              exact ⟨message, input, senderOfClaim side message input claimed claim, claim⟩
            · rintro ⟨message, input, _sender, claim⟩
              exact (PhaseProposal.mem_archive _ _).mpr ⟨message, input, claim⟩
          have actualWord :
              (∃ message ∈ (ending side).execution.network.inputs, message.sender = owner ∧
                PhaseProposal.packetProposal? message.payload =
                  some (⟨anchor.application.attempt, event⟩, claimed)) ↔
              ReservedEpoch.openingFrontierEmission runtime leaks tape
                (anchor.respond app actor (responses side)) owner event := by
            simpa only [applications side] using actual
          exact emitted.trans (actualWord.trans
            (ReservedEpoch.openingFrontierEmission_respond_foreign runtime leaks tape anchor actor
              owner different (responses side) event))
        exact (word false).trans (word true).symm
      · have noEarlier : ¬ ∃ prior ∈ phase.events, prior.val < event.val ∧
            (graph).actor? prior = some owner ∧ (image false).native.PublicFailure prior := by
          rintro ⟨prior, _inside, before, owned, failed⟩
          exact scans false (Finset.mem_filter.mpr ⟨Finset.mem_univ owner,
            prior, before, owned, failed⟩)
        obtain ⟨leftAction, rightAction, leftRecorded, rightRecorded, _bits⟩ := rows event inside
          acting inherited noEarlier
            (fun prior priorInside _before owned => outputs prior priorInside owned)
        let actions := fun (side : Bool) => if side then rightAction else leftAction
        have recorded : ∀ side, (⟨event, actions side⟩ : (graph).Completion) ∈
            (image side).native.config.history := by
          intro side
          cases side
          · exact leftRecorded
          · exact rightRecorded
        have disclosed : ∀ side,
            cast (congrArg EventField.Action output) (actions side) = true := by
          intro side
          exact phaseProposalUnflagged_fresh_opening_disclosure setup mode runtime leaks bounds plan
            coveredValues maximal ordered values tape activationGap processingGap gaps margin
              remaining (anchor.respond app actor (responses side)) (starts side) (closing side)
                (ending side) (priors side) (joints side) (legal side) (realized side) (kept side)
                  (by simpa only [applications side] using same side)
                  (by simpa only [applications side] using changed side) phase
                  (by simpa only [applications side] using installed) kind (raw side) (effects side)
                  (coverage side) (excluded side) event inside owner acting
                  (by simpa only [applications side] using active) payload
                  (checkpoint.refs.get selected) checks output code node value
                  (by simpa only [applications side] using locked) (scans side) (actions side)
                  (recorded side) (fun old => request (by
                    simpa only [applications side] using old.1)) (finals side) (by
                    convert supports side using 1
                    congr 2
                    funext history
                    cases history.state <;> rfl) (finalStates side) (finalKept side)
        have emitted : ∀ side, (⟨anchor.application.attempt, event⟩, claimed) ∈
            PhaseProposal.archive (ending side).execution.network.inputs := by
          intro side
          obtain ⟨message, candidate, alleged, input, address, call, _receipt⟩ :=
            ReservedEpoch.closing_disclosure_has_receipt runtime leaks bounds plan ordered inputs
              horizon scheduler (closing side) (priors side) (ending side).execution (raw side)
                (by simpa only [same side] using changed side) (effects side) phase
                  (closingInstalled side) event inside payload output (actions side) (recorded side)
                    (disclosed side)
          have member : (⟨anchor.application.attempt, event⟩, alleged) ∈
              PhaseProposal.archive (ending side).execution.network.inputs :=
            (PhaseProposal.mem_archive _ _).mpr ⟨message, input, by
              simp only [PhaseProposal.packetProposal?, call, address, same side]⟩
          exact (lockedClaim side alleged member) ▸ member
        exact iff_of_true (emitted false) (emitted true)
    intro alleged
    by_cases equal : alleged = claimed
    · subst alleged
      exact commonClaim
    · exact iff_of_false (fun member => equal (lockedClaim false alleged member))
        (fun member => equal (lockedClaim true alleged member))
  intro event inside acting
  refine ⟨outputs event inside acting, ?_, bits event inside acting,
    archiveWord event inside acting⟩
  by_cases completed : event ∈ anchor.application.current.native.config.cut.completed
  · have stable : ∀ side, PhaseService.BindingAccepted runtime leaks
        ⟨anchor.application.attempt, event⟩ owner (ending side).execution ↔
          PhaseService.BindingAccepted runtime leaks ⟨anchor.application.attempt, event⟩ owner
            (anchor.respond app actor (responses side)) := by
      intro side
      exact publication_resolved_receipt_word setup mode runtime leaks bounds plan horizon scheduler
        ⟨remaining, none, anchor.respond app actor (responses side)⟩ (ending side) (starts side)
          ((priors side).extend (joints side) (legal side) (realized side))
          (.extend (kept side) _ _ _) ⟨anchor.application.attempt, event⟩
            (Or.inr (Or.inr ⟨by rw [applications side], by
              simpa only [applications side] using completed⟩)) owner
    exact (stable false).trans ((initialAccepted _).trans (stable true).symm)
  · have exactBit : ∀ side, ∀ action,
        (⟨event, action⟩ : (graph).Completion) ∈ (image side).native.config.history →
        (PhaseService.BindingAccepted runtime leaks ⟨anchor.application.attempt, event⟩ owner
            (ending side).execution ↔
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) action = true) := by
      intro side action recorded
      obtain ⟨payload, publication⟩ := kind ▸ phase.fields event
        ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
      have unresolved : ¬ (⟨anchor.application.attempt, event⟩ : CommitAttemptEvent graph).Resolved
          (anchor.respond app actor (responses side)).application := by
        rintro (generation | phase | ⟨_same, finished⟩)
        · exact Nat.lt_irrefl _ (by simpa only [applications side] using generation)
        · exact Nat.lt_irrefl _ (by simpa only [applications side] using phase)
        · exact completed (by simpa only [applications side] using finished)
      have physical := ReservedEpoch.publication_unresolved_receipt_iff_recorded runtime leaks
        bounds plan inputs horizon scheduler
          ⟨remaining, none, anchor.respond app actor (responses side)⟩ (closing side) (ending side)
            (starts side) (priors side) (joints side) (legal side) (realized side) (kept side)
              (by simpa only [applications side] using (same side).symm) (raw side) (effects side)
              event phase (closingInstalled side) inside payload publication ordered
                (by simpa only [same side] using changed side) action recorded owner
                  (by simpa only [applications side] using unresolved) acting
      have sameBit : cast (congrArg EventField.Action publication) action =
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) action :=
        PhaseProposal.publicationDiscloses_cast publication action
      rw [sameBit] at physical
      simpa only [applications side] using physical
    obtain ⟨left, leftRecorded, leftAt⟩ := List.mem_map.mp
      (((image false).native.config.history_exact event).mpr (finished false inside))
    rcases left with ⟨leftEvent, leftAction⟩
    change leftEvent = event at leftAt
    subst leftEvent
    obtain ⟨right, rightRecorded, rightAt⟩ := List.mem_map.mp
      (((image true).native.config.history_exact event).mpr (finished true inside))
    rcases right with ⟨rightEvent, rightAction⟩
    change rightEvent = event at rightAt
    subst rightEvent
    rw [exactBit false leftAction leftRecorded, exactBit true rightAction rightRecorded,
      bits event inside acting leftAction rightAction leftRecorded rightRecorded]

/-- The actual reserved processing frontier preserves a successful old
focal opening when its current available SEND replaces WAIT. -/
private theorem publication_old_focal_receipt_wait_imp_send
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (remaining : Nat) (active : (app).Execution) (actor : Player)
    (leftResponse rightResponse : (app).Action)
    (leftApplication : (active.respond app actor leftResponse).application = active.application)
    (rightApplication : (active.respond app actor rightResponse).application = active.application)
    (leftStart : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, active.respond app actor leftResponse⟩))
    (rightStart : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, active.respond app actor rightResponse⟩))
    (leftCount rightCount : Nat)
    (leftClosed rightClosed : (app).Control)
    (leftIdle : leftClosed.actor = none) (rightIdle : rightClosed.actor = none)
    (leftTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some leftClosed))
    (rightTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some rightClosed))
    (leftKept : TracePrefix leftStart leftTrace) (rightKept : TracePrefix rightStart rightTrace)
    (leftRetired : leftClosed.execution.application.attempt ≠ active.application.attempt)
    (rightRetired : rightClosed.execution.application.attempt ≠ active.application.attempt)
    (event : (graph).EventId) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding actor payload))
    (checks : List (GuardCheck (graph).layout payload))
    (output : (graph).outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode (graph).layout) output) ((graph).nodes event) =
      .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks output code)
    (value : L.Val payload)
    (locked : binding.get? active.application.current.native.config.store = some (.success value))
    (bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (request : active.application.SeedRequest actor ⟨active.application.attempt, event⟩)
    (entered : Nat) (stamp : active.application.current.native.activatedAt event = some entered)
    (positive : 0 < runtime.deadline event)
    (candidate : Handle graph) (claimed : Raw L) (material : WitnessedSubmission graph)
    (call : material.call.packet = .opening event candidate claimed)
    (sent : leftResponse = ⟨some material⟩) (waited : rightResponse = ⟨none⟩)
    (unsent : ∀ message ∈ (app).outputs (active.recall actor),
      PhaseCount.event? message.payload ≠ some ⟨active.application.attempt, event⟩)
    (afterProcessing : ReservedEpoch.packetCapacity runtime ≤ active.environmentRecall.length %
      ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime))
    (leftPath : leftClosed.execution ∈ ((app).runRounds
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) leftCount
        (active.respond app actor leftResponse)).support)
    (rightPath : rightClosed.execution ∈ ((app).runRounds
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) rightCount
        (active.respond app actor rightResponse)).support) :
    PhaseService.BindingAccepted runtime leaks ⟨active.application.attempt, event⟩ actor
        rightClosed.execution →
      PhaseService.BindingAccepted runtime leaks ⟨active.application.attempt, event⟩ actor
        leftClosed.execution := by
  rcases leftClosed with ⟨leftRemaining, leftActor, leftClosed⟩
  change leftActor = none at leftIdle
  subst leftActor
  rcases rightClosed with ⟨rightRemaining, rightActor, rightClosed⟩
  change rightActor = none at rightIdle
  subst rightActor
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  have leftWord := phaseProposalUnflagged_stopped_old_opening_receipt_word setup mode runtime
    leaks bounds plan ordered values tape remaining leftRemaining leftCount actor
      (active.respond app actor leftResponse) leftClosed leftStart leftTrace leftKept
        (by simpa only [leftApplication] using leftRetired) event payload binding checks output
          code node value (by simpa only [leftApplication] using locked) bounded
            (by simpa only [leftApplication] using request) entered
              (by simpa only [leftApplication] using stamp) positive
                (by simpa only [(app).respond_environmentRecall] using afterProcessing) leftPath
  have rightWord := phaseProposalUnflagged_stopped_old_opening_receipt_word setup mode runtime
    leaks bounds plan ordered values tape remaining rightRemaining rightCount actor
      (active.respond app actor rightResponse) rightClosed rightStart rightTrace rightKept
        (by simpa only [rightApplication] using rightRetired) event payload binding checks output
          code node value (by simpa only [rightApplication] using locked) bounded
            (by simpa only [rightApplication] using request) entered
              (by simpa only [rightApplication] using stamp) positive
                (by simpa only [(app).respond_environmentRecall] using afterProcessing) rightPath
  intro received
  have waiting : ReservedEpoch.openingFrontierReceipt runtime leaks tape
      (active.respond app actor ⟨none⟩) actor event := by
    have qualified := rightWord.mp (by simpa only [rightApplication] using received)
    simpa only [waited] using qualified
  have sending := ReservedEpoch.openingFrontierReceipt_wait_imp_send runtime leaks tape active
    actor event candidate claimed material call unsent waiting
  have received := leftWord.mpr (by simpa only [sent] using sending)
  simpa only [leftApplication] using received

/-- Focal WAIT survival gives the SAME owned semantic and proposal word,
and forces prompt survival through the original exclusion record. -/
private theorem publication_focal_word
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (remaining : Nat) (anchor : (app).Execution) (actor : Player)
    (responses : Bool → (app).Action)
    (applications : ∀ side, (anchor.respond app actor (responses side)).application =
      anchor.application)
    (starts : ∀ side, ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, anchor.respond app actor (responses side)⟩))
    (checkpoint : RecoverySourceCheckpoint setup mode anchor.application)
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (kind : phase.kind = .reveal) (stored : anchor.application.StoredCheckpoint)
    (proper : checkpoint.source.BindingsHoldValues actor)
    (closing ending : Bool → (app).Control)
    (idle : ∀ side, (ending side).actor = none)
    (priors : ∀ side, ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some (closing side)))
    (joints : Bool → Player → Option (app).Action)
    (legal : ∀ side, ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Legal
        (some (closing side)) (joints side))
    (realized : ∀ side, some (ending side) ∈ ((app).transition initial
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
        (some (closing side)) (joints side)).support)
    (kept : ∀ side, TracePrefix (starts side) (priors side))
    (same : ∀ side, (closing side).execution.application.attempt = anchor.application.attempt)
    (changed : ∀ side, (ending side).execution.application.attempt ≠ anchor.application.attempt)
    (closingInstalled : ∀ side, phase ∈ (closing side).execution.application.phases.head?)
    (raw : Bool → RecoveryState graph)
    (effects : ∀ side, PhaseClosingEffect runtime leaks (closing side).execution
      (ending side).execution (raw side))
    (coverage : ∀ side, (phase.drain (raw side)).FailureCoverage)
    (excluded : ∀ side, (phase.drain (raw side)).excluded =
      (ending side).execution.application.current.excluded)
    (finished : ∀ side, phase.Finished (phase.drain (raw side)))
    (counts : Bool → Nat)
    (paths : ∀ side, (ending side).execution ∈ ((app).runRounds
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) (counts side)
        (anchor.respond app actor (responses side))).support)
    (afterProcessing : ReservedEpoch.packetCapacity runtime ≤ anchor.environmentRecall.length %
      ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime))
    (finals : Bool → ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).History)
    (supports : ∀ side,
      let horizon := ReservedEpoch.executionHorizon runtime
      let scheduler := ReservedEpoch.family runtime leaks
        (ReservedEpoch.packetCapacity runtime) tape
      let start := anchor.respond app actor (responses side)
      let players := ReactiveApplication.anchoredPolicy start
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
      let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
      let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
        match history.state with
        | none => False
        | some control => control.execution.application.attempt ≠ start.application.attempt
      finals side ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded _ horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, start⟩, starts side⟩).support)
    (finalStates : ∀ side, (finals side).state = some (ending side))
    (finalKept : ∀ side, TracePrefix
      ((priors side).extend (joints side) (legal side) (realized side)) (finals side).trace)
    (frontier : (graph).EventId)
    (request : anchor.application.SeedRequest actor ⟨anchor.application.attempt, frontier⟩)
    (candidate : Handle graph) (claimed : Raw L) (material : WitnessedSubmission graph)
    (call : material.call.packet = .opening frontier candidate claimed)
    (sent : responses false = ⟨some material⟩) (waited : responses true = ⟨none⟩)
    (unsent : ∀ message ∈ (app).outputs (anchor.recall actor),
      PhaseCount.event? message.payload ≠ some ⟨anchor.application.attempt, frontier⟩)
    (survives : actor ∉ (phase.drain (raw true)).excluded) :
    actor ∉ (phase.drain (raw false)).excluded ∧
    ∀ event ∈ phase.events, (graph).actor? event = some actor →
      (phase.drain (raw false)).native.config.outputs event =
          (phase.drain (raw true)).native.config.outputs event ∧
      (∀ leftAction rightAction,
        (⟨event, leftAction⟩ : (graph).Completion) ∈
          (phase.drain (raw false)).native.config.history →
        (⟨event, rightAction⟩ : (graph).Completion) ∈
          (phase.drain (raw true)).native.config.history →
        PhaseProposal.publicationDiscloses ((graph).outputLayout event) leftAction = true ∧
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) rightAction = true) ∧
      ∀ value : Raw L,
        (⟨anchor.application.attempt, event⟩, value) ∈
            PhaseProposal.archive (ending false).execution.network.inputs ↔
          (⟨anchor.application.attempt, event⟩, value) ∈
            PhaseProposal.archive (ending true).execution.network.inputs := by
  classical
  let horizon := ReservedEpoch.executionHorizon runtime
  let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
  let image := fun side => phase.drain (raw side)
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have anchorRecord : anchor.application.ExclusionRecord := by
    have actual := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
      ((menu).toRawTrace initial horizon scheduler (starts false))
    simpa only [applications false] using actual
  have anchorCoverage : anchor.application.FailureCoverage := by
    have actual := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
      ((menu).toRawTrace initial horizon scheduler (starts false))
    simpa only [applications false] using actual
  obtain ⟨remainingPhases, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have positioned := anchorRecord.frontier.positioned
  rw [phases] at positioned
  have entries : ∀ side, (closing side).execution.application.entry = anchor.application.entry := by
    intro side
    have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized ((menu).toRawTrace initial horizon scheduler (starts side))
    have progress := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon scheduler _ _ (starts side) (priors side) (kept side) firstOrdered).2.2
        (by simpa only [applications side] using (same side).symm)
    exact progress.symm.trans (congrArg PhaseRuntimeState.entry (applications side))
  have closingStores : ∀ side, KeepsStore (closing side).execution.application.current.native
      (image side).native := by
    intro side
    have rawStore : KeepsStore (closing side).execution.application.current.native
        (raw side).native := by
      rcases effects side with ⟨id, message, native, _found, _moved, handled, rawEq⟩ |
          ⟨command, native, _moved, supported, rawEq⟩
      · rw [rawEq]
        exact handle_store_of_some runtime _ native _ handled
      · rw [rawEq]
        exact environmentStep_store_of_some runtime _ native command supported
    exact fun field value present => phase.drain_keepsStore (raw side) field value
      (rawStore field value present)
  have keptStores : ∀ side, KeepsStore anchor.application.current.native (image side).native := by
    intro side
    have first := PhaseProposal.same_attempt_prefix_keeps_store runtime leaks menu initial
      initialized horizon scheduler _ _ (starts side) (priors side) (kept side)
        (by simpa only [applications side] using (same side).symm)
    exact fun field value present => closingStores side field value
      (first field value (by simpa only [applications side] using present))
  have histories : ∀ side, anchor.application.current.native.config.history.IsPrefix
      (image side).native.config.history := by
    intro side
    have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized ((menu).toRawTrace initial horizon scheduler (starts side))
    have retained := phase_prefix_semantic_extension runtime leaks menu initial horizon
      scheduler
      _ _ (starts side) (priors side) (kept side) firstOrdered
        (by simpa only [applications side] using (same side).symm)
    have second := ReservedEpoch.phaseClosingEffect_history_prefix runtime leaks
      (closing side).execution (ending side).execution (raw side) (effects side)
    simpa only [applications side] using
      retained.2.trans (second.trans (phase.drain_history_prefix (raw side)))
  have frames : ∀ side, anchor.application.entry.native.PublicFailureExtension
      (image side).native := by
    intro side
    have rawFrame := phaseClosingEffect_failure_frame setup mode runtime leaks bounds plan
      horizon scheduler (closing side) (ending side) (priors side) (raw side) (effects side)
    change (closing side).execution.application.entry.native.PublicFailureExtension
      (raw side).native at rawFrame
    rw [entries side] at rawFrame
    exact rawFrame.trans
      (phase.drain_publicFailureExtension (raw side))
  have sourceOrders : ∀ side,
      (image side).OrderedPublicFailures phase.low anchor.application.entry.excluded := by
    intro side
    have actual := phaseClosingEffect_publication_order setup mode runtime leaks bounds plan
      horizon scheduler (closing side) (ending side) (priors side) phase
        (Option.mem_def.mp (closingInstalled side)) (raw side) (effects side)
          (by simpa only [same side] using changed side)
    simpa only [entries side] using actual
  have reached : ∀ side,
      (image side).native.config.Reachable (image side).native.config.inputs := by
    intro side
    obtain ⟨draw, actual⟩ := publication_closing_image_reachable runtime leaks plan inputs horizon
      scheduler (closing side) ((menu).toRawTrace initial horizon scheduler (priors side))
        (ending side).execution (raw side) (effects side) phase
    change (phase.drain (raw side)).native.config.Reachable
      (phase.drain (raw side)).native.config.inputs
    rw [actual.inputs_eq]
    exact actual
  have sameInputs : (image false).native.config.inputs = (image true).native.config.inputs := by
    funext input
    exact Option.some.inj ((keptStores false (.inl input) _ rfl).trans
      (keptStores true (.inl input) _ rfl).symm)
  have fixed : ∀ event : (graph).EventId, event.val < phase.low →
      (image false).native.config.outputs event = (image true).native.config.outputs event := by
    intro event below
    obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp
      ((anchor.application.current.native.config.output_available event).mpr
        (positioned.2.1 event below))
    exact (keptStores false (.inr event) value present).trans
      (keptStores true (.inr event) value present).symm
  have noWaitingFailure : ∀ event, (graph).actor? event = some actor →
      ¬ (image true).native.PublicFailure event := by
    intro event acting failed
    exact survives ((coverage true).covered event actor acting failed)
  have rows : ∀ event ∈ phase.events, (graph).actor? event = some actor →
      actor ∉ anchor.application.entry.excluded →
      (¬ ∃ prior ∈ phase.events, prior.val < event.val ∧
        (graph).actor? prior = some actor ∧ (image false).native.PublicFailure prior) →
      (∀ prior ∈ phase.events, prior.val < event.val → (graph).actor? prior = some actor →
        (image false).native.config.outputs prior = (image true).native.config.outputs prior) →
      ∃ leftAction rightAction,
        (⟨event, leftAction⟩ : (graph).Completion) ∈ (image false).native.config.history ∧
        (⟨event, rightAction⟩ : (graph).Completion) ∈ (image true).native.config.history ∧
        PhaseProposal.publicationDiscloses ((graph).outputLayout event) leftAction =
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) rightAction := by
    intro event inside acting inherited noEarlier _earlier
    by_cases completed : event ∈ anchor.application.current.native.config.cut.completed
    · obtain ⟨action, first, second⟩ := publication_completed_row setup mode
        anchor.application.current.native (image false).native (image true).native
          (histories false) (histories true) event completed
      exact ⟨action, action, first, second, rfl⟩
    obtain ⟨payload, _name, selected, checks, output, code, value, locked⟩ :=
      checkpoint.publication_binding_row setup mode phase installed kind stored event inside actor
        acting proper
    have node := nodeView_eq_resolve output code
    obtain ⟨first, firstRecorded, firstAt⟩ := List.mem_map.mp
      (((image false).native.config.history_exact event).mpr (finished false inside))
    rcases first with ⟨firstEvent, leftAction⟩
    change firstEvent = event at firstAt
    subst firstEvent
    obtain ⟨second, secondRecorded, secondAt⟩ := List.mem_map.mp
      (((image true).native.config.history_exact event).mpr (finished true inside))
    rcases second with ⟨secondEvent, rightAction⟩
    change secondEvent = event at secondAt
    subst secondEvent
    have waitingTrue := publication_survivor_disclosure_true (image true) (reached true)
      (coverage true) event actor acting survives payload (checkpoint.refs.get selected) checks
        output code rightAction secondRecorded
    have promptTrue : cast (congrArg EventField.Action output) leftAction = true := by
      by_cases old : anchor.application.SeedRequest actor ⟨anchor.application.attempt, event⟩
      · have sole : event = frontier := ordered.ready_actor_unique
          anchor.application.current.native.config.cut request.2.2.1 old.2.2.1 request.2.2.2.1
            acting
        obtain ⟨draw, invariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
          scheduler ((menu).toRawTrace initial horizon scheduler (starts false))
        have native : anchor.application.current.native.Invariant draw := by
          simpa only [applications false] using invariant.active
        obtain ⟨entered, stamp⟩ := native.activatedAt_eq_some_of_ready_actor event old.2.2.1
          (by simp only [acting, Option.isSome_some])
        have positive : 0 < runtime.deadline event := by
          have room := margin event (by simp only [acting, Option.isSome_some])
          omega
        have bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values := by
          have covered := coveredValues event
          rw [output] at covered
          exact covered value
        let actions := fun (side : Bool) => if side then rightAction else leftAction
        have recorded : ∀ side, (⟨event, actions side⟩ : (graph).Completion) ∈
            (image side).native.config.history := by
          intro side
          cases side
          · exact firstRecorded
          · exact secondRecorded
        have exactBit : ∀ side, PhaseService.BindingAccepted runtime leaks
            ⟨anchor.application.attempt, event⟩ actor (ending side).execution ↔
              cast (congrArg EventField.Action output) (actions side) = true := by
          intro side
          have physical := ReservedEpoch.publication_unresolved_receipt_iff_recorded runtime leaks
            bounds plan inputs horizon scheduler
              ⟨remaining, none, anchor.respond app actor (responses side)⟩
                (closing side) (ending side)
                (starts side) (priors side) (joints side) (legal side) (realized side) (kept side)
                  (by simpa only [applications side] using (same side).symm)
                    (raw side) (effects side)
                  event phase (closingInstalled side) inside payload output ordered
                    (by simpa only [same side] using changed side) (actions side) (recorded side)
                      actor (fun resolved => resolved.not_request _ _ actor
                        (by simpa only [applications side] using old)) acting
          simpa only [applications side] using physical
        have monotone := publication_old_focal_receipt_wait_imp_send setup mode runtime leaks bounds
          plan values tape remaining anchor actor (responses false) (responses true)
            (applications false) (applications true) (starts false) (starts true)
              (counts false) (counts true) (ending false) (ending true) (idle false) (idle true)
                ((priors false).extend (joints false) (legal false) (realized false))
                ((priors true).extend (joints true) (legal true) (realized true))
                (.extend (kept false) _ _ _) (.extend (kept true) _ _ _)
                (by simpa only [applications false] using changed false)
                (by simpa only [applications true] using changed true)
                event payload (checkpoint.refs.get selected) checks output code node value locked
                  bounded old entered stamp positive candidate claimed material
                    (by simpa only [sole] using call) sent waited
                    (by simpa only [sole] using unsent) afterProcessing (paths false) (paths true)
        exact (exactBit false).mp (monotone ((exactBit true).mpr waitingTrue))
      · have scan : actor ∉ (image false).native.failureOwnersBefore event.val := by
          intro scanned
          obtain ⟨prior, before, owned, failed⟩ := (Finset.mem_filter.mp scanned).2
          by_cases low : prior.val < phase.low
          · exact inherited (anchorCoverage.saved.covered prior actor owned
              (((frames false).failures prior ((positioned.1.2 prior).mpr low)).mp failed))
          exact noEarlier ⟨prior, (phase.mem_events prior).mpr ⟨by omega, by
            have upper := ((phase.mem_events event).mp inside).2
            omega⟩, before, owned, failed⟩
        exact phaseProposalUnflagged_fresh_opening_disclosure setup mode runtime leaks bounds plan
          coveredValues maximal ordered values tape activationGap processingGap gaps margin
            remaining (anchor.respond app actor (responses false)) (starts false) (closing false)
              (ending false) (priors false) (joints false) (legal false) (realized false)
                (kept false)
                (by simpa only [applications false] using same false)
                (by simpa only [applications false] using changed false) phase
                (by simpa only [applications false] using installed) kind (raw false)
                  (effects false)
                (coverage false) (excluded false) event inside actor acting
                (by simpa only [applications false] using request.2.2.2.2) payload
                  (checkpoint.refs.get selected) checks output code node value
                  (by simpa only [applications false] using locked) scan leftAction firstRecorded
                  (fun prior => old (by simpa only [applications false] using prior.1))
                  (finals false) (by
                    convert supports false using 1
                    congr 2
                    funext history
                    cases history.state <;> rfl) (finalStates false) (finalKept false)
    exact ⟨leftAction, rightAction, firstRecorded, secondRecorded,
      (PhaseProposal.publicationDiscloses_cast output leftAction).symm.trans
        (promptTrue.trans (waitingTrue.symm.trans
          (PhaseProposal.publicationDiscloses_cast output rightAction)))⟩
  have outputs := publication_owner_outputs_eq setup mode checkpoint phase installed kind
    (image false) (image true) (reached false) (reached true) sameInputs fixed
      anchor.application.entry.excluded (sourceOrders false) (sourceOrders true)
        (finished false) (finished true) actor rows
  obtain ⟨_valid, _binding, receipts, _stored, _remembered, _coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      (closing false) (ending false) (priors false) (raw false) (effects false)
        (by simpa only [same false] using changed false)
  have imageRecord : SuffixExclusionRecord phase.low anchor.application.entry.excluded
      (image false) := by
    have record := (receipts.exclusion.installed phase (closingInstalled false)).phase_drain phase
    simpa only [entries false] using record
  obtain ⟨closingRest, closingPhases⟩ :=
    List.head?_eq_some_iff.mp (Option.mem_def.mp (closingInstalled false))
  have rawPositioned := receipts.exclusion.frontier.positioned
  change PhaseRuntimeState.Positioned (closing false).execution.application.phases
    (closing false).execution.application.entry (raw false) at rawPositioned
  rw [closingPhases] at rawPositioned
  have imageWithin := phase.drain_within (raw false) rawPositioned.2
  have promptSurvives : actor ∉ (image false).excluded := by
    intro lost
    rcases (imageRecord.excluded actor).mp lost with inherited | ⟨event, lower, acting, failed⟩
    · exact request.2.2.2.2 (anchorCoverage.inherited inherited)
    have inside : event ∈ phase.events := (phase.mem_events event).mpr
      ⟨lower, imageWithin.2 event failed.completed⟩
    obtain ⟨payload, publication⟩ := kind ▸ phase.fields event lower
      (imageWithin.2 event failed.completed)
    have sameFailure : (image false).native.PublicFailure event ↔
        (image true).native.PublicFailure event := by
      simp only [State.PublicFailure, PublicView.missedBinding, publication,
        Bool.false_eq_true, false_or]
      unfold RecoveryState.publicationFailed
      rw [outputs event inside acting]
    exact noWaitingFailure event acting (sameFailure.mp failed)
  refine ⟨promptSurvives, ?_⟩
  intro event inside acting
  obtain ⟨payload, _name, selected, checks, output, code, value, locked⟩ :=
    checkpoint.publication_binding_row setup mode phase installed kind stored event inside actor
      acting proper
  have nativeTrue : ∀ side action,
      (⟨event, action⟩ : (graph).Completion) ∈ (image side).native.config.history →
        PhaseProposal.publicationDiscloses ((graph).outputLayout event) action = true := by
    intro side action recorded
    have safe : actor ∉ (image side).excluded := by
      cases side
      · exact promptSurvives
      · exact survives
    exact (PhaseProposal.publicationDiscloses_cast output action).symm.trans
      (publication_survivor_disclosure_true (image side) (reached side) (coverage side) event actor
        acting safe payload (checkpoint.refs.get selected) checks output code action recorded)
  refine ⟨outputs event inside acting, fun left right first second =>
    ⟨nativeTrue false left first, nativeTrue true right second⟩, ?_⟩
  let fixedValue : Raw L := ⟨payload, value⟩
  have closingInputs : ∀ side,
      (ending side).execution.network.inputs = (closing side).execution.network.inputs := by
    intro side
    rcases effects side with ⟨id, message, native, _found, moved, _handled, _raw⟩ |
        ⟨command, native, moved, _supported, _raw⟩
    · exact (app).environmentStep_inputs _ _ (.include id) moved
    · exact (app).environmentStep_inputs _ _ (.application command) moved
  have lockedClaim : ∀ side alleged,
      (⟨anchor.application.attempt, event⟩, alleged) ∈
        PhaseProposal.archive (ending side).execution.network.inputs → alleged = fixedValue := by
    intro side alleged member
    obtain ⟨message, input, claim⟩ := (PhaseProposal.mem_archive _ _).mp member
    rw [closingInputs side] at input
    obtain ⟨actual, rawEq, saved⟩ := PhaseProposal.submitted_proposal_current_binding_meaning
      runtime leaks bounds plan ordered inputs horizon scheduler (closing side) (priors side)
        message input ⟨anchor.application.attempt, event⟩ alleged claim (same side).symm actor
          payload (checkpoint.refs.get selected) checks output code
    have beforeRead := (checkpoint.refs.get selected).get?_preserved
      (closing side).execution.application.current.native.config.store
        (image side).native.config.store (closingStores side) _ saved
    have fixedRead := (checkpoint.refs.get selected).get?_preserved
      anchor.application.current.native.config.store (image side).native.config.store
        (keptStores side) _ locked
    have equal : actual = value := PublicationResult.success.inj
      (Option.some.inj (beforeRead.symm.trans fixedRead))
    subst actual
    exact rawEq
  have emitted : ∀ side, (⟨anchor.application.attempt, event⟩, fixedValue) ∈
      PhaseProposal.archive (ending side).execution.network.inputs := by
    intro side
    obtain ⟨completion, recorded, atEvent⟩ := List.mem_map.mp
      (((image side).native.config.history_exact event).mpr (finished side inside))
    rcases completion with ⟨actual, action⟩
    change actual = event at atEvent
    subst actual
    obtain ⟨message, candidate, alleged, input, address, call, _receipt⟩ :=
      ReservedEpoch.closing_disclosure_has_receipt runtime leaks bounds plan ordered inputs horizon
        scheduler (closing side) (priors side) (ending side).execution (raw side)
          (by simpa only [same side] using changed side) (effects side) phase
            (closingInstalled side) event inside payload output action recorded
              ((PhaseProposal.publicationDiscloses_cast output action).trans
                (nativeTrue side action recorded))
    have member : (⟨anchor.application.attempt, event⟩, alleged) ∈
        PhaseProposal.archive (ending side).execution.network.inputs :=
      (PhaseProposal.mem_archive _ _).mpr ⟨message, input, by
        simp only [PhaseProposal.packetProposal?, call, address, same side]⟩
    exact (lockedClaim side alleged member) ▸ member
  intro alleged
  constructor
  · intro member
    rw [lockedClaim false alleged member]
    exact emitted true
  · intro member
    rw [lockedClaim true alleged member]
    exact emitted false

/-- Every pair of actual stopped publication supports has the same complete
foreign word. Focal WAIT survival gives prompt survival and identical complete
semantic and archive-lifted source histories at the original boundary. -/
theorem phaseProposalUnflagged_paired_publication_boundary
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (remaining : Nat) (active : (app).Execution) (actor : Player)
    (material : WitnessedSubmission graph)
    (activeTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, some actor, active⟩))
    (offered : (⟨some material⟩ : (app).Action) ∈ (menu).actions actor
      (active.recall actor) (active.observe app actor))
    (phase : RuntimePhase graph) (installed : phase ∈ active.application.phases.head?)
    (kind : phase.kind = .reveal)
    (checkpoint : RecoverySourceCheckpoint setup mode active.application)
    (proper : ∀ who, who ∉ active.application.current.excluded →
      checkpoint.source.BindingsHoldValues who) :
    PairedPublicationBoundary setup mode runtime leaks bounds plan values tape remaining active
      actor material activeTrace phase checkpoint := by
  classical
  let horizon := ReservedEpoch.executionHorizon runtime
  let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
  let ordered := serviceGraph_revealRelaxedOrdered setup mode
  let responses : Bool → (app).Action := fun side => if side then ⟨none⟩ else ⟨some material⟩
  let anchor := fun side => active.respond app actor (responses side)
  let responseJoint := fun side who => if who = actor then some (responses side) else none
  have available : ∀ side, responses side ∈ (menu).actions actor
      (active.recall actor) (active.observe app actor) := by
    intro side
    cases side
    · exact offered
    · exact PhaseCount.silence_onePacket runtime leaks bounds actor _ _
  have legal : ∀ side, ((menu).protocol initial horizon scheduler).Legal
      (some ⟨remaining, some actor, active⟩) (responseJoint side) := by
    intro side
    constructor
    · simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal]
    · intro who
      by_cases same : who = actor
      · subst who
        simpa [responseJoint, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor, ReactiveApplication.ResponseMenu.available]
          using available side
      · simp [responseJoint, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor, same, Ne.symm same]
  have realized : ∀ side, some (⟨remaining, none, anchor side⟩ : (app).Control) ∈
      ((app).transition initial horizon scheduler (some ⟨remaining, some actor, active⟩)
        (responseJoint side)).support := by
    intro side
    change _ ∈ (PMF.pure _).support
    simp only [responseJoint, ↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff _ _]
    rfl
  let starts := fun side => activeTrace.extend (responseJoint side) (legal side) (realized side)
  have responsePrefix : ∀ side, TracePrefix activeTrace (starts side) := by
    intro side
    exact .extend .refl _ _ _
  have lengths : ∀ side, (starts side).length = activeTrace.length + 1 := fun _ => rfl
  obtain ⟨coordinate, requested⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds
    plan inputs horizon scheduler remaining actor active activeTrace material offered
  obtain ⟨actualPhase, actualInstalled, inside⟩ := requested.2.1
  have phaseEq : actualPhase = phase := Option.some.inj
    ((Option.mem_def.mp actualInstalled).symm.trans (Option.mem_def.mp installed))
  subst actualPhase
  have request : active.application.SeedRequest actor
      ⟨active.application.attempt, coordinate.event⟩ := by
    exact ⟨rfl, requested.2⟩
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
    ((menu).toRawTrace initial horizon scheduler activeTrace)
  obtain ⟨payload, publication⟩ := kind ▸ phase.fields coordinate.event
    ((phase.mem_events coordinate.event).mp inside).1
    ((phase.mem_events coordinate.event).mp inside).2
  obtain ⟨candidate, claimed, call⟩ := PhaseCount.submitted_opening_packet runtime leaks bounds
    plan ordered inputs horizon scheduler remaining actor active activeTrace coordinate.event
      payload publication request material offered
  have applications : ∀ side, (anchor side).application = active.application := by
    intro side
    cases side with
    | true => rfl
    | false =>
        change active.application.submit actor material = active.application
        simp only [PhaseRuntimeState.submit, RecoveryState.submit, call,
          Submission.register, submitStep]
        rfl
  have afterProcessing := ReservedEpoch.active_after_processing runtime leaks
    (ReservedEpoch.packetCapacity runtime) tape initial horizon ⟨remaining, some actor, active⟩
      ((menu).toRawTrace initial horizon scheduler activeTrace) actor rfl
  have unsent : ∀ message ∈ (app).outputs (active.recall actor),
      PhaseCount.event? message.payload ≠ some ⟨active.application.attempt, coordinate.event⟩ := by
    exact PhaseCount.unsent_of_nonsilent runtime leaks bounds plan ordered inputs
      horizon scheduler remaining actor active activeTrace _ request material offered
  have installedAfter : ∀ side, phase ∈ (anchor side).application.phases.head? := by
    intro side
    simpa only [applications side] using installed
  let contract : PhaseService.AsyncContract runtime leaks initial horizon scheduler
      (fun _ => activationGap + 1) (fun _ => processingGap + 1) := {
    opportunity := ReservedEpoch.family_opportunity runtime leaks
      (ReservedEpoch.packetCapacity runtime) (ReservedEpoch.completionCycles runtime) tape
      activationGap processingGap gaps plan ordered maximal inputs
    inclusion := ReservedEpoch.family_protectedInclusion runtime leaks
      (ReservedEpoch.completionCycles runtime) tape activationGap processingGap gaps plan inputs
    completes := ReservedEpoch.family_completesPlay runtime leaks tape plan ordered maximal inputs }
  unfold PairedPublicationBoundary
  refine ⟨starts false, starts true, responsePrefix false, responsePrefix true,
    lengths false, lengths true,
    ⟨legal false, realized false, rfl⟩, ⟨legal true, realized true, rfl⟩, ?_⟩
  intro law leftFinal leftSupported rightFinal rightSupported
  let finals := fun (side : Bool) => if side then rightFinal else leftFinal
  let players := fun side => ReactiveApplication.anchoredPolicy (anchor side)
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
  let profiles := fun side who => (menu).restrictPolicy initial horizon scheduler who
    (players side who)
  have supported : ∀ side, finals side ∈ (law (anchor side) (starts side)).support := by
    intro side
    cases side
    · exact leftSupported
    · exact rightSupported
  dsimp only [law] at supported
  have snapshots := fun side => phase_attempt_stopped_receipt_snapshot runtime leaks menu plan
    inputs horizon scheduler (fun _ => activationGap + 1) (fun _ => processingGap + 1) contract
      (profiles side) ⟨remaining, none, anchor side⟩ (starts side) phase (installedAfter side)
        (finals side) (by
          convert supported side using 1
          congr 2
          funext history
          cases history.state <;> rfl)
  choose endings finalStates changes idle images finished invariant coverage excluded receipts
    closings priors joints closureLegal closureRealized raw kept finalKept same closingInstalled
    imageEq normalized effects using snapshots
  have counts : ∀ side, ∃ count, (endings side).execution ∈ ((app).runRounds scheduler
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) count
        (anchor side)).support := by
    intro side
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ (anchor side).application.attempt
    have rounds := stopped_prefix_roundsSupported menu initial horizon scheduler (profiles side)
      remaining (anchor side) (starts side) stopped (finals side) (by
          convert supported side using 1
          congr 2
          funext history
          dsimp only [stopped]
          cases history.state <;> rfl)
        ⟨some (endings side), (priors side).extend (joints side) (closureLegal side)
          (closureRealized side)⟩ (.extend (kept side) _ _ _) (finalKept side)
    have decoded : (menu).decodeProfile initial horizon scheduler (profiles side) =
        players side := by
      funext who
      exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler who
        (players side who) ((menu).anchoredPolicy_covered initial horizon scheduler
          ⟨remaining, none, anchor side⟩ (starts side)
          (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who
            (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values who))
    rw [decoded] at rounds
    change (app).RunRoundsSupported scheduler (players side) (anchor side)
      (some (endings side)) at rounds
    simp only [ReactiveApplication.RunRoundsSupported, idle side] at rounds
    obtain ⟨count, reached⟩ := rounds
    rw [ReactiveApplication.runRounds_anchoredPolicy] at reached
    exact ⟨count, reached⟩
  choose counts paths using counts
  have foreign := fun owner different => publication_foreign_word setup mode runtime leaks bounds
    plan coveredValues maximal values tape activationGap processingGap gaps margin remaining active
      actor owner different responses applications starts checkpoint phase installed kind stored
        proper closings endings idle priors joints closureLegal closureRealized kept
          (by simpa only [applications] using same) (by simpa only [applications] using changes)
          closingInstalled raw effects (by simpa only [imageEq] using coverage)
          (by simpa only [imageEq] using excluded) (by simpa only [imageEq] using finished)
          counts paths afterProcessing finals (by
          intro side
          convert supported side using 1
          congr 2
          funext history
          cases history.state <;> rfl) finalStates finalKept
  have focal := fun survives => publication_focal_word setup mode runtime leaks bounds plan
    coveredValues maximal values tape activationGap processingGap gaps margin remaining active
      actor responses applications starts checkpoint phase installed kind stored
        (proper actor request.2.2.2.2) closings endings idle priors joints closureLegal
        closureRealized kept (by simpa only [applications] using same)
        (by simpa only [applications] using changes) closingInstalled raw effects
        (by simpa only [imageEq] using coverage) (by simpa only [imageEq] using excluded)
        (by simpa only [imageEq] using finished) counts paths afterProcessing finals (by
          intro side
          convert supported side using 1
          congr 2
          funext history
          cases history.state <;> rfl)
        finalStates finalKept coordinate.event request candidate claimed material
        call rfl rfl unsent survives
  have sameAnchor : ∀ side, (closings side).execution.application.attempt =
      active.application.attempt := by
    intro side
    exact (same side).trans (congrArg PhaseRuntimeState.attempt (applications side))
  have changedAnchor : ∀ side, (endings side).execution.application.attempt ≠
      active.application.attempt := by
    intro side equal
    exact changes side (equal.trans (congrArg PhaseRuntimeState.attempt (applications side)).symm)
  have finishedRaw : ∀ side, phase.Finished (phase.drain (raw side)) := by
    intro side
    simpa only [imageEq side] using finished side
  refine ⟨endings false, endings true, closings false, closings true, priors false, priors true,
    joints false, joints true, closureLegal false, closureLegal true,
    closureRealized false, closureRealized true, raw false, raw true,
    finalStates false, finalStates true, idle false, idle true,
    normalized false, normalized true, kept false, kept true, finalKept false, finalKept true,
    sameAnchor false, sameAnchor true, changedAnchor false, changedAnchor true,
    effects false, effects true, closingInstalled false, closingInstalled true,
    finishedRaw false, finishedRaw true, by simpa only [imageEq false] using coverage false,
    by simpa only [imageEq true] using coverage true,
    by simpa only [imageEq false] using excluded false,
    by simpa only [imageEq true] using excluded true, ?_, ?_⟩
  · intro event member owner different acting
    have row := foreign owner different event member acting
    exact ⟨row.2.1, row.1, row.2.2.1, row.2.2.2⟩
  · intro survives
    obtain ⟨promptSurvives, focalRows⟩ := focal survives
    let image := fun side => phase.drain (raw side)
    have initialized : ∀ state ∈ (initial).support, state.Ordered := by
      intro state supported
      obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan draw
    have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized ((menu).toRawTrace initial horizon scheduler activeTrace)
    have retained : ∀ side, TracePrefix activeTrace (priors side) :=
      fun side => (responsePrefix side).trans (kept side)
    have metadata := fun side => phaseProposal_same_attempt_archive_metadata setup mode runtime
      leaks bounds
      plan horizon scheduler ⟨remaining, some actor, active⟩ (closings side)
        activeTrace (priors side) (retained side) (sameAnchor side).symm
    have entries : ∀ side, (closings side).execution.application.entry =
        active.application.entry := by
      intro side
      exact ((phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
        scheduler ⟨remaining, some actor, active⟩ (closings side) activeTrace (priors side)
          (retained side) firstOrdered).2.2 (sameAnchor side).symm).symm
    have generations : ∀ side, (closings side).execution.application.generation =
        active.application.generation :=
      fun side => congrArg CommitAttemptId.generation (sameAnchor side)
    obtain ⟨remainingPhases, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
    let rawState := fun side =>
      ({active.application with current := raw side} : PhaseRuntimeState graph)
    have actualRaw : ∀ side,
        ({(closings side).execution.application with current := raw side} :
          PhaseRuntimeState graph) = rawState side := by
      intro side
      have controls := metadata side
      have generation := generations side
      have entry := entries side
      cases beforeEq : (closings side).execution.application
      cases anchorEq : active.application
      simp_all only [rawState]
    let nextState := fun side =>
      (⟨remainingPhases, active.application.generation, image side, image side,
        active.application.retired⟩ : PhaseRuntimeState graph)
    have replayEach : ∀ side, ∃ next : RecoverySourceCheckpoint setup mode (nextState side),
        (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩) ∧
        Relation.ReflTransGen (NativePublicSourceStep (image side).native 0 setup.program)
          (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail
            checkpoint.source), active.application.entry.excluded)
          (next.residual.lift (ProtocolState.entry next.residual.tail next.source),
            (image side).excluded) ∧
        (∃ states : List (ProtocolState setup.program × Finset Player),
          ((checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
            active.application.entry.excluded) :: states).IsChain
              (NativePublicSourceStep (image side).native 0 setup.program) ∧
          ((checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
            active.application.entry.excluded) :: states).getLast (List.cons_ne_nil _ _) =
              (next.residual.lift (ProtocolState.entry next.residual.tail next.source),
                (image side).excluded) ∧
          setup.recoveryAddressWord next.trace = setup.recoveryAddressWord checkpoint.trace ++
            states.map (fun point => (CommitRecoveryState.atPoint point.1 point.2
              active.application.generation).publicAddress)) ∧
        (∀ owner, owner ∉ (image side).excluded → next.source.history owner =
          checkpoint.source.history owner ++
            (decodeHistory setup.program ((image side).native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
                (decodeHistory setup.program (active.application.entry.native.config.history.map
                  ((toEventGraph setup.program).fromModeCompletion mode)) owner).length) ∧
        NativeSourceReplayExtension setup (image side).native active.application.generation
          checkpoint.trace next.trace := by
      intro side
      obtain ⟨⟨draw, native⟩, _binding, receipt, rawStored, remembered, _coverage⟩ :=
        phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
          (closings side) (endings side) (priors side) (raw side) (effects side)
            (by simpa only [sameAnchor side] using changedAnchor side)
      have exclusion : (rawState side).ExclusionRecord := by
        rw [← actualRaw side]
        exact receipt.exclusion
      have saved : (rawState side).StoredCheckpoint := by
        rw [← actualRaw side]
        exact rawStored
      have savedHistory : (rawState side).HistoryCheckpoint := by
        rw [← actualRaw side]
        exact remembered
      have order := phaseClosingEffect_publication_order setup mode runtime leaks bounds plan
        horizon scheduler (closings side) (endings side) (priors side) phase
          (Option.mem_def.mp (closingInstalled side)) (raw side) (effects side)
            (by simpa only [sameAnchor side] using changedAnchor side)
      rw [entries side] at order
      let cp : RecoverySourceCheckpoint setup mode (rawState side) :=
        checkpoint.transfer rfl rfl rfl
      obtain ⟨next, reaches, path, addresses, own, _intended, extension⟩ :=
        cp.after_reveal phase remainingPhases phases kind exclusion saved savedHistory
          (phase.drain_reachable (raw side) native.active.reachable) order (finishedRaw side)
      exact ⟨next, reaches, path, addresses, own, extension⟩
    choose next reaches paths addresses own extension using replayEach
    have frontier := (phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
      ((menu).toRawTrace initial horizon scheduler activeTrace)).frontier
    have low : active.application.attempt.phase = phase.low := by
      simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
        Option.getD_some]
    have high : ∀ side, (nextState side).attempt.phase = phase.high := by
      intro side
      have adjacent := frontier.adjacent
      have last := frontier.last
      rw [phases] at adjacent last
      cases remainingPhases with
      | nil =>
          have ending := last phase (by simp only [List.getLast?_singleton, Option.mem_some_iff])
          simpa only [nextState, PhaseRuntimeState.attempt, List.head?_nil, Option.map_none,
            Option.getD_none] using ending.symm
      | cons after remaining =>
          have boundary := adjacent.rel_head? (y := after) (by simp)
          simpa only [nextState, PhaseRuntimeState.attempt, List.head?_cons, Option.map_some,
            Option.getD_some] using boundary.symm
    have priorRank := checkpoint.saved_position.trans low
    have lastRank := fun side => (next side).saved_position.trans (high side)
    have nativePrefixes : ∀ side, (image side).native.config.cut.IsPrefix phase.high := by
      intro side
      obtain ⟨_valid, _binding, receipt, _stored, _remembered, _coverage⟩ :=
        phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
          (closings side) (endings side) (priors side) (raw side) (effects side)
            (by simpa only [sameAnchor side] using changedAnchor side)
      have within := receipt.exclusion.frontier.positioned
      change PhaseRuntimeState.Positioned (closings side).execution.application.phases
        (closings side).execution.application.entry (raw side) at within
      rw [(metadata side).1, phases] at within
      exact phase.finished_prefix (image side) (phase.drain_within (raw side) within.2)
        (finishedRaw side)
    have nativeHistories : ∀ side, active.application.current.native.config.history.IsPrefix
        (image side).native.config.history := by
      intro side
      have first := phase_prefix_semantic_extension runtime leaks menu initial horizon scheduler
        ⟨remaining, some actor, active⟩ (closings side) activeTrace (priors side) (retained side)
          firstOrdered (sameAnchor side).symm
      have second := ReservedEpoch.phaseClosingEffect_history_prefix runtime leaks
        (closings side).execution (endings side).execution (raw side) (effects side)
      exact first.2.trans (second.trans (phase.drain_history_prefix (raw side)))
    have nativeBits : ∀ event : (graph).EventId, ∀ leftAction rightAction,
        (⟨event, leftAction⟩ : (graph).Completion) ∈ (image false).native.config.history →
        (⟨event, rightAction⟩ : (graph).Completion) ∈ (image true).native.config.history →
        PhaseProposal.publicationDiscloses ((graph).outputLayout event) leftAction =
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) rightAction := by
      intro event leftAction rightAction leftRecorded rightRecorded
      by_cases before : event.val < phase.low
      · have positioned := frontier.positioned
        rw [phases] at positioned
        obtain ⟨action, first, second⟩ := publication_completed_row setup mode
          active.application.current.native (image false).native (image true).native
            (nativeHistories false) (nativeHistories true) event (positioned.2.1 event before)
        have leftEq : leftAction = action := eq_of_heq (EventGraph.Completion.mk.inj
          (List.inj_on_of_nodup_map (image false).native.config.history_nodup
            leftRecorded first rfl)).2
        have rightEq : rightAction = action := eq_of_heq (EventGraph.Completion.mk.inj
          (List.inj_on_of_nodup_map (image true).native.config.history_nodup
            rightRecorded second rfl)).2
        rw [leftEq, rightEq]
      by_cases during : event.val < phase.high
      · have inside := (phase.mem_events event).mpr ⟨by omega, during⟩
        obtain ⟨payload, publication⟩ := kind ▸ phase.fields event (by omega) during
        cases acting : (graph).actor? event with
        | none =>
            have isPublication : ((graph).outputLayout event).IsPublication := by
              rw [publication]
              trivial
            exact False.elim (absurd isPublication
              (EventCode.not_publication_of_actor_none ((graph).nodes event) acting))
        | some owner =>
            by_cases sameOwner : owner = actor
            · subst owner
              have row := focalRows event inside acting
              have bits := row.2.1 leftAction rightAction leftRecorded rightRecorded
              exact bits.1.trans bits.2.symm
            · exact (foreign owner sameOwner event inside acting).2.2.1
                leftAction rightAction leftRecorded rightRecorded
      · have completed := ((image false).native.config.history_exact event).mp
          (List.mem_map.mpr ⟨⟨event, leftAction⟩, leftRecorded, rfl⟩)
        exact (during (((nativePrefixes false).2 event).mp completed)).elim
    have histories := publication_phase_histories_eq setup mode phase kind
      (image false).native (image true).native active.application.generation
        (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
          active.application.entry.excluded)
        ((next false).residual.lift
          (ProtocolState.entry (next false).residual.tail (next false).source),
          (image false).excluded)
        ((next true).residual.lift
          (ProtocolState.entry (next true).residual.tail (next true).source), (image true).excluded)
        checkpoint.trace
        (next false).trace (next true).trace priorRank (lastRank false) (lastRank true)
          (reaches false).choose_spec.tracePrefix (reaches true).choose_spec.tracePrefix
          (extension false) (extension true) nativeBits
    have endpoint := congrArg History.state histories
    have point : (next false).residual.lift
        (ProtocolState.entry (next false).residual.tail (next false).source) =
      (next true).residual.lift
        (ProtocolState.entry (next true).residual.tail (next true).source) := by
      exact Option.some.inj (congrArg (Option.map CommitRecoveryState.point) endpoint)
    have exclusions : (image false).excluded = (image true).excluded := by
      exact Option.some.inj (congrArg (Option.map CommitRecoveryState.excluded) endpoint)
    have address : setup.recoveryAddressWord (next false).trace =
        setup.recoveryAddressWord (next true).trace := by
      exact congrArg (fun history : setup.commitRecoveryProtocol.History =>
        setup.recoveryAddressWord history.trace) histories
    have live : ∀ owner, owner ∉ (image false).excluded → ProtocolState.BindingsHoldValues owner
        setup.program ((next false).residual.lift
          (ProtocolState.entry (next false).residual.tail (next false).source)) := by
      intro owner surviving
      have initialActive : owner ∉ active.application.current.excluded := by
        let monotone := phaseApplication_exclusion_monotone runtime leaks
        let predicate := fun state : (app).State =>
          active.application.current.excluded ⊆ state.current.excluded
        have invariant : (app).Invariant predicate := {
          submit := fun state who submission before =>
            before.trans (monotone.submit state who submission)
          handle := fun state message after before accepted =>
            before.trans (monotone.handle state message after accepted)
          environment := fun state command after before reached =>
            before.trans (monotone.environment state command after reached) }
        have grows := invariant.tracePrefix menu initial horizon scheduler
          ⟨remaining, some actor, active⟩ (endings false) activeTrace
            ((priors false).extend (joints false) (closureLegal false) (closureRealized false))
              (.extend (retained false) _ _ _) (Finset.Subset.refl _)
        intro absent
        apply surviving
        change owner ∈ (phase.drain (raw false)).excluded
        rw [← imageEq false, excluded false]
        exact grows absent
      apply ProtocolState.noncommit_path_bindingsHoldValues setup.program
        (fun first last moved => ⟨moved.1.2.1, moved.1.2.2⟩) _ _ (paths false) owner
          (fun _ => (checkpoint.origin.bindingsHoldValues_lift owner _).mpr
            ((ProtocolState.bindingsHoldValues_entry owner _ _).mpr (proper owner initialActive)))
          surviving
    have archives : PhaseProposal.sourceArchive (endings false).execution.network.inputs =
        PhaseProposal.sourceArchive (endings true).execution.network.inputs := by
      have closingInputs : ∀ side, (endings side).execution.network.inputs =
          (closings side).execution.network.inputs := by
        intro side
        rcases effects side with ⟨id, message, native, _found, moved, _handled, _raw⟩ |
            ⟨command, native, moved, _supported, _raw⟩
        · exact (app).environmentStep_inputs _ _ (.«include» id) moved
        · exact (app).environmentStep_inputs _ _ (.application command) moved
      have oldArchive : ∀ side,
          (PhaseProposal.sourceArchive (endings side).execution.network.inputs).filter
              (fun proposal => proposal.address.phase < active.application.attempt.phase) =
            (PhaseProposal.sourceArchive active.network.inputs).filter
              (fun proposal => proposal.address.phase < active.application.attempt.phase) := by
        intro side
        rw [closingInputs side]
        exact (metadata side).2.2
      have bounded : ∀ side proposal, proposal ∈
          PhaseProposal.sourceArchive (endings side).execution.network.inputs →
          proposal.address.phase ≤ active.application.attempt.phase := by
        intro side proposal member
        rw [closingInputs side] at member
        have bound := PhaseProposal.sourceArchive_phase_le runtime leaks plan inputs horizon
          scheduler (closings side) ((menu).toRawTrace initial horizon scheduler (priors side))
            proposal member
        simpa only [sameAnchor side] using bound
      have currentWord : ∀ side event, event ∈ phase.events → ∀ owner,
          (graph).actor? event = some owner → ∀ raw : Raw L,
          (⟨active.application.attempt, event⟩, raw) ∈
              PhaseProposal.archive (endings side).execution.network.inputs ↔
            (⟨active.application.attempt, event⟩, raw) ∈
              PhaseProposal.archive (endings (!side)).execution.network.inputs := by
        intro side event inside owner acting raw
        have row : (⟨active.application.attempt, event⟩, raw) ∈
            PhaseProposal.archive (endings false).execution.network.inputs ↔
          (⟨active.application.attempt, event⟩, raw) ∈
            PhaseProposal.archive (endings true).execution.network.inputs := by
          by_cases equal : owner = actor
          · subst owner
            exact (focalRows event inside acting).2.2 raw
          · exact (foreign owner equal event inside acting).2.2.2 raw
        cases side
        · exact row
        · exact row.symm
      have transfer : ∀ side,
          PhaseProposal.sourceArchive (endings side).execution.network.inputs ⊆
            PhaseProposal.sourceArchive (endings (!side)).execution.network.inputs := by
        intro side proposal member
        by_cases earlier : proposal.address.phase < active.application.attempt.phase
        · have old : proposal ∈
              (PhaseProposal.sourceArchive (endings side).execution.network.inputs).filter
                (fun proposal => proposal.address.phase < active.application.attempt.phase) :=
            Finset.mem_filter.mpr ⟨member, earlier⟩
          rw [oldArchive side, ← oldArchive (!side)] at old
          exact (Finset.mem_filter.mp old).1
        have equalPhase : proposal.address.phase = active.application.attempt.phase :=
          Nat.le_antisymm (bounded side proposal member) (Nat.le_of_not_gt earlier)
        obtain ⟨event, inside, address⟩ := PhaseProposal.archived_proposal_in_installed_phase
          runtime leaks bounds plan ordered inputs horizon scheduler (closings side) (priors side)
            phase (Option.mem_def.mp (closingInstalled side)) proposal
            (by simpa only [closingInputs side] using member)
            (by simpa only [sameAnchor side] using equalPhase)
        have fixedAddress : proposal.address =
            PhaseProposal.sourceAddress ⟨active.application.attempt, event⟩ := by
          simpa only [sameAnchor side] using address
        obtain ⟨raw, archived, decoded⟩ := (PhaseProposal.mem_sourceArchive _ _).mp member
        have coordinate : raw.1 = ⟨active.application.attempt, event⟩ :=
          PhaseProposal.sourceAddress_injective
            ((PhaseProposal.sourceProposal?_address raw proposal decoded).symm.trans fixedAddress)
        obtain ⟨payload, publication⟩ := kind ▸ phase.fields event
          ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
        have acting : ∃ owner, (graph).actor? event = some owner := by
          cases actorEq : (graph).actor? event with
          | none =>
              have isPublication : ((graph).outputLayout event).IsPublication := by
                rw [publication]
                trivial
              exact False.elim (absurd isPublication
                (EventCode.not_publication_of_actor_none ((graph).nodes event) actorEq))
          | some owner => exact ⟨owner, rfl⟩
        obtain ⟨owner, acting⟩ := acting
        have other : raw ∈ PhaseProposal.archive (endings (!side)).execution.network.inputs := by
          rw [show raw = (⟨active.application.attempt, event⟩, raw.2) from
            Prod.ext coordinate rfl] at archived ⊢
          exact (currentWord side event inside owner acting raw.2).mp archived
        exact (PhaseProposal.mem_sourceArchive _ _).mpr ⟨raw, other, decoded⟩
      exact Finset.Subset.antisymm (transfer false) (transfer true)
    have retired : ∀ side, (endings side).execution.application.retired =
        active.application.retired := by
      intro side
      rw [normalized side]
      change (PhaseRuntimeState.settle (closings side).execution.application.phases
        (closings side).execution.application.generation
        (closings side).execution.application.entry (raw side)
        (closings side).execution.application.retired).retired = _
      rw [(metadata side).1, phases]
      have notCommit : phase.kind ≠ .commitment := by rw [kind]; decide
      simp only [PhaseRuntimeState.settle, finishedRaw side, notCommit, false_and, ↓reduceIte]
      exact (PhaseRuntimeState.settle_generation_archive_of_same_excluded remainingPhases
        (closings side).execution.application.generation (image side) (image side)
          (closings side).execution.application.retired rfl).2.trans (metadata side).2.1
    have controls : PhaseRuntimeState.sourceControlRecords
        (endings false).execution.application.retired =
      PhaseRuntimeState.sourceControlRecords (endings true).execution.application.retired := by
      rw [retired false, retired true]
    have lifted : (⟨_, setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive
          (endings false).execution.network.inputs)) (next false).trace⟩ :
        setup.proposalRecoveryProtocol.History) =
      ⟨_, setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive
          (endings true).execution.network.inputs)) (next true).trace⟩ := by
      rw [archives]
      exact congrArg (fun history : setup.commitRecoveryProtocol.History =>
        (⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive
            (endings true).execution.network.inputs)) history.trace⟩ :
          setup.proposalRecoveryProtocol.History)) histories
    have stores : ∀ side, KeepsStore active.application.current.native (image side).native := by
      intro side
      have prefixStore := PhaseProposal.same_attempt_prefix_keeps_store runtime leaks menu initial
        initialized horizon scheduler ⟨remaining, some actor, active⟩ (closings side) activeTrace
          (priors side) (retained side) (sameAnchor side).symm
      have primitive : KeepsStore (closings side).execution.application.current.native
          (raw side).native := by
        rcases effects side with ⟨id, message, native, _found, _moved, handled, rawEq⟩ |
            ⟨command, native, _moved, supported, rawEq⟩
        · rw [rawEq]
          exact handle_store_of_some runtime _ native _ handled
        · rw [rawEq]
          exact environmentStep_store_of_some runtime _ native command supported
      exact fun field value present => phase.drain_keepsStore (raw side) field value
        (primitive field value (prefixStore field value present))
    have sameInputs : (image false).native.config.inputs = (image true).native.config.inputs := by
      funext input
      exact Option.some.inj ((stores false (.inl input) _ rfl).trans
        (stores true (.inl input) _ rfl).symm)
    refine ⟨promptSurvives, exclusions, sameInputs, archives, controls, ?_⟩
    rw [phases]
    change ∃ promptNext : RecoverySourceCheckpoint setup mode (nextState false),
        ∃ waitingNext : RecoverySourceCheckpoint setup mode (nextState true),
          (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
            ⟨_, checkpoint.trace⟩ ⟨_, promptNext.trace⟩) ∧
          Relation.ReflTransGen (NativePublicSourceStep (image false).native 0 setup.program)
            (checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded)
            (promptNext.residual.lift (ProtocolState.entry promptNext.residual.tail
              promptNext.source), (image false).excluded) ∧
          (∃ states : List (ProtocolState setup.program × Finset Player),
            ((checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded) :: states).IsChain
              (NativePublicSourceStep (image false).native 0 setup.program) ∧
            ((checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded) :: states).getLast
              (List.cons_ne_nil _ _) = (promptNext.residual.lift (ProtocolState.entry
                promptNext.residual.tail promptNext.source), (image false).excluded) ∧
            setup.recoveryAddressWord promptNext.trace = setup.recoveryAddressWord checkpoint.trace
              ++
              states.map (fun point => (CommitRecoveryState.atPoint point.1 point.2
                active.application.generation).publicAddress)) ∧
          (∀ owner, owner ∉ (image false).excluded → promptNext.source.history owner =
            checkpoint.source.history owner ++
              (decodeHistory setup.program ((image false).native.config.history.map
                ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
                  (decodeHistory setup.program (active.application.entry.native.config.history.map
                    ((toEventGraph setup.program).fromModeCompletion mode)) owner).length) ∧
          (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
            ⟨_, checkpoint.trace⟩ ⟨_, waitingNext.trace⟩) ∧
          Relation.ReflTransGen (NativePublicSourceStep (image true).native 0 setup.program)
            (checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded)
            (waitingNext.residual.lift (ProtocolState.entry waitingNext.residual.tail
              waitingNext.source), (image true).excluded) ∧
          (∃ states : List (ProtocolState setup.program × Finset Player),
            ((checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded) :: states).IsChain
              (NativePublicSourceStep (image true).native 0 setup.program) ∧
            ((checkpoint.residual.lift
              (ProtocolState.entry checkpoint.residual.tail checkpoint.source),
                active.application.entry.excluded) :: states).getLast
              (List.cons_ne_nil _ _) = (waitingNext.residual.lift (ProtocolState.entry
                waitingNext.residual.tail waitingNext.source), (image true).excluded) ∧
            setup.recoveryAddressWord waitingNext.trace = setup.recoveryAddressWord checkpoint.trace
              ++
              states.map (fun point => (CommitRecoveryState.atPoint point.1 point.2
                active.application.generation).publicAddress)) ∧
          (∀ owner, owner ∉ (image true).excluded → waitingNext.source.history owner =
            checkpoint.source.history owner ++
              (decodeHistory setup.program ((image true).native.config.history.map
                ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
                  (decodeHistory setup.program (active.application.entry.native.config.history.map
                    ((toEventGraph setup.program).fromModeCompletion mode)) owner).length) ∧
          NativeSourceReplayExtension setup (image false).native active.application.generation
            checkpoint.trace promptNext.trace ∧
          NativeSourceReplayExtension setup (image true).native active.application.generation
            checkpoint.trace waitingNext.trace ∧
          promptNext.residual.lift (ProtocolState.entry promptNext.residual.tail
            promptNext.source) =
            waitingNext.residual.lift
              (ProtocolState.entry waitingNext.residual.tail waitingNext.source) ∧
          (⟨_, promptNext.trace⟩ : setup.commitRecoveryProtocol.History) = ⟨_, waitingNext.trace⟩ ∧
          (⟨_, setup.proposalRecoveryLiftTrace
            (nativeArchiveLabels setup (PhaseProposal.sourceArchive
              (endings false).execution.network.inputs)) promptNext.trace⟩ :
              setup.proposalRecoveryProtocol.History) =
            ⟨_, setup.proposalRecoveryLiftTrace
              (nativeArchiveLabels setup (PhaseProposal.sourceArchive
                (endings true).execution.network.inputs)) waitingNext.trace⟩ ∧
          setup.recoveryAddressWord promptNext.trace = setup.recoveryAddressWord waitingNext.trace ∧
          ∀ owner, owner ∉ (image false).excluded → ProtocolState.BindingsHoldValues owner
            setup.program (promptNext.residual.lift
              (ProtocolState.entry promptNext.residual.tail promptNext.source))
    exact ⟨next false, next true, reaches false, paths false, addresses false, own false,
      reaches true, paths true, addresses true, own true, extension false, extension true, point,
      histories, lifted, address, live⟩


end Vegas
