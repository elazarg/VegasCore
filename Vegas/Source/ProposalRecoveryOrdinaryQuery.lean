/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryOrdinaryView
import Vegas.Source.ProposalRecoveryVirtualLift
import Vegas.Source.CommitRecoveryNoMissRepresentative

/-! # Ordinary current queries on the same paired source history

The actual paired event list already retains both endpoint repairs. Its target
signals reconstruct public recall; no extra repaired witness is selected.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem virtualEvent_publicSignal (who observer : Player)
    (left right : setup.commitRecoveryProtocol.StepEvent)
    (paired : setup.CommitRecoveryVirtualEvent who left right) :
    setup.attemptPublicSignal observer right.target =
      setup.attemptPublicSignal observer left.target := by
  rcases paired with same | ⟨original, repaired, after, last, _leftSource, _rightSource,
    leftTarget, rightTarget, _before, related, _foreign, _survives, _raw⟩
  · rw [same]
  · rw [leftTarget, rightTarget]
    exact setup.commitRecovery_publicSignal_of_focalRepair related.focalRepair observer

private theorem publicRecall_eventTargets (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    setup.attemptPublicRecall who trace =
      (setup.commitRecoveryEventRecall trace).map
        (fun event => setup.attemptPublicSignal who event.target) ++
          [setup.attemptPublicSignal who setup.commitRecoveryProtocol.init] := by
  induction trace with
  | start => rfl
  | @extend before after prior joint legal supported ih =>
      change setup.attemptPublicRecall who (prior.extend joint legal supported) =
        setup.attemptPublicSignal who after :: _
      rw [attemptPublicRecall, InfoSignals.infoOf_extend]
      change setup.attemptPublicSignal who after :: setup.attemptPublicRecall who prior = _
      exact congrArg (List.cons (setup.attemptPublicSignal who after)) ih

private theorem publicRecall_of_virtualEvents (who observer : Player)
    {left right : setup.commitRecoveryProtocol.State}
    (original : setup.commitRecoveryProtocol.Trace left)
    (repaired : setup.commitRecoveryProtocol.Trace right)
    (paired : List.Forall₂ (setup.CommitRecoveryVirtualEvent who)
      (setup.commitRecoveryEventRecall original)
      (setup.commitRecoveryEventRecall repaired)) :
    setup.attemptPublicRecall observer repaired =
      setup.attemptPublicRecall observer original := by
  have mapSignals {left right : List setup.commitRecoveryProtocol.StepEvent}
      (paired : List.Forall₂ (setup.CommitRecoveryVirtualEvent who) left right) :
      right.map (fun event => setup.attemptPublicSignal observer event.target) =
        left.map (fun event => setup.attemptPublicSignal observer event.target) := by
    induction paired with
    | nil => rfl
    | @cons first last left right head _tail ih =>
        simp only [List.map_cons]
        rw [setup.virtualEvent_publicSignal who observer first last head, ih]
  rw [setup.publicRecall_eventTargets observer repaired,
    setup.publicRecall_eventTargets observer original, mapSignals paired]

private theorem virtualEvents_targets (who : Player)
    {left right : setup.commitRecoveryProtocol.State}
    (original : setup.commitRecoveryProtocol.Trace left)
    (repaired : setup.commitRecoveryProtocol.Trace right)
    (paired : List.Forall₂ (setup.CommitRecoveryVirtualEvent who)
      (setup.commitRecoveryEventRecall original)
      (setup.commitRecoveryEventRecall repaired)) :
    left = right ∨ ∃ before after : CommitRecoveryState setup.program,
      left = some before ∧ right = some after ∧ CommitRecoveryState.VirtualRepair
        (setup.context.map Prod.fst).toFinset who before after := by
  cases original with
  | start =>
      cases repaired with
      | start => exact Or.inl rfl
      | extend prior joint legal supported => cases paired
  | @extend before after prior joint legal supported =>
      cases repaired with
      | start => cases paired
      | @extend rightBefore rightAfter rightPrior rightJoint rightLegal rightSupported =>
          have head := (List.forall₂_cons.mp paired).1
          rcases head with same | ⟨first, second, after, last, _leftSource, _rightSource,
            leftTarget, rightTarget, _before, related, _foreign, _survives, _raw⟩
          · exact Or.inl (congrArg
              (fun event : setup.commitRecoveryProtocol.StepEvent => event.target) same)
          · exact Or.inr ⟨after, last, leftTarget, rightTarget, related⟩

private theorem virtualEvents_endpoint (who : Player)
    (original repaired : CommitRecoveryState setup.program)
    (originalTrace : setup.commitRecoveryProtocol.Trace (some original))
    (repairedTrace : setup.commitRecoveryProtocol.Trace (some repaired))
    (paired : List.Forall₂ (setup.CommitRecoveryVirtualEvent who)
      (setup.commitRecoveryEventRecall originalTrace)
      (setup.commitRecoveryEventRecall repairedTrace)) :
    original = repaired ∨ CommitRecoveryState.VirtualRepair
      (setup.context.map Prod.fst).toFinset who original repaired := by
  rcases setup.virtualEvents_targets who originalTrace repairedTrace paired with same |
    ⟨before, after, leftTarget, rightTarget, related⟩
  · exact Or.inl (Option.some.inj same)
  · cases Option.some.inj leftTarget
    cases Option.some.inj rightTarget
    exact Or.inr related

/-- The original annotated event pair determines BOTH current observation and
public recall. Ordinary live values remove only virtual unusable replacements;
all guard debt, prior failure controls and proposal observations remain. -/
theorem commitRecovery_ordinary_virtual_erased_info (who : Player)
    (original repaired : CommitRecoveryState setup.program)
    (originalTrace : setup.commitRecoveryProtocol.Trace (some original))
    (repairedTrace : setup.commitRecoveryProtocol.Trace (some repaired))
    (paired : List.Forall₂ (setup.CommitRecoveryVirtualEvent who)
      (setup.commitRecoveryEventRecall originalTrace)
      (setup.commitRecoveryEventRecall repairedTrace))
    (values : ProtocolState.BindingsHoldValues who setup.program original.point) :
    setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who repairedTrace) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who originalTrace) := by
  have frame : setup.commitRecoveryPublic (some repaired) =
        setup.commitRecoveryPublic (some original) ∧
      ProtocolView.eraseHistory who setup.program
          (ProtocolState.observe who setup.program repaired.point) =
        ProtocolView.eraseHistory who setup.program
          (ProtocolState.observe who setup.program original.point) := by
    rcases setup.virtualEvents_endpoint who original repaired originalTrace repairedTrace paired
      with same | related
    · subst repaired
      exact ⟨rfl, rfl⟩
    · exact ⟨congrArg Prod.snd (setup.commitRecovery_publicSignal_of_focalRepair
          related.focalRepair who),
        ProtocolState.VirtualRepair.observe_eq_of_bindingsHoldValues
          (setup.context.map Prod.fst).toFinset who setup.program original.point repaired.point
            related.point values⟩
  have recall := setup.publicRecall_of_virtualEvents who who originalTrace repairedTrace paired
  rw [setup.erasedInformation_publicRecall who repairedTrace,
    setup.erasedInformation_publicRecall who originalTrace]
  simp only [commitRecoveryPrivate, Option.map_some]
  rw [frame.1, frame.2, recall]

/-- The actual normalized ordinary table key agrees on this SAME annotated
pair. The statement concerns a current getter, not conditional beliefs or
future continuation laws. -/
theorem commitRecovery_ordinary_virtual_normalized_info (who : Player)
    (original repaired : CommitRecoveryState setup.program)
    (originalTrace : setup.commitRecoveryProtocol.Trace (some original))
    (repairedTrace : setup.commitRecoveryProtocol.Trace (some repaired))
    (paired : List.Forall₂ (setup.CommitRecoveryVirtualEvent who)
      (setup.commitRecoveryEventRecall originalTrace)
      (setup.commitRecoveryEventRecall repairedTrace))
    (values : ProtocolState.BindingsHoldValues who setup.program original.point) :
    setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryModel.infoOf who repairedTrace)) =
      setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryModel.infoOf who originalTrace)) := by
  rw [setup.commitRecoveryNoMissInformation_erased,
    setup.commitRecoveryNoMissInformation_erased,
    setup.commitRecovery_ordinary_virtual_erased_info who original repaired
      originalTrace repairedTrace paired values]

end Vegas.SourceProgram.Setup
