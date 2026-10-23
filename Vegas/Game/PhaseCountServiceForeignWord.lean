/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseObservableDomainWord
import Vegas.Game.PhaseSourcePolicy
import Vegas.Pending.PhaseCountServiceReference
import Vegas.Pending.PhasePrivateService
import Vegas.Pending.PhaseBindingMemoryCallback
import Interaction.ReactiveResponseKernel
import Interaction.ReactiveAnchoredStopped
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom
import Vegas.Pending.PhaseAttemptReceiptSnapshot
import Interaction.ReactiveMenuLikelihood
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay
import Vegas.Source.CommitRecoveryValueTremble
import Vegas.Source.CommitRecoveryErasedModel
import Vegas.Game.CommitRecoveryReference
import Vegas.Pending.PhaseReadyBindingDeclaration
import Vegas.Pending.PhaseProposalEmissionOrder
import GameTheory.Analysis.Protocol.ExtensiveFormPerfection
import GameTheory.Math.Probability.Product
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.TremblingPlans

/-! # Original domain declarations in the counted service experiment

A non-RAW sending atom retains the exact domain-table answer, independently
of its physical fresh slot. The original domain table is fixed throughout;
neither a later binding request nor a retry initializes another source draw.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

private theorem same_attempt_metadata :
    (phaseApplication runtime leaks).StepRelation (fun before after => before.Ordered →
      before.attempt = after.attempt →
      (after.phases, after.retired) = (before.phases, before.retired)) where
  refl _ _ _ := rfl
  submit _ _ _ _ _ := rfl
  handle state message next accepted ordered same := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have settled := PhaseRuntimeState.settle_of_same_namespace
        state.phases state.generation state.entry
        (state.current.inclusionResult message.payload.packet.call native) state.retired ordered
        same
      have archived := congrArg (fun state => (state.phases, state.retired)) settled
      exact archived
    · cases accepted
  environment state command next reached ordered same := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      have settled := PhaseRuntimeState.settle_of_same_namespace
        state.phases state.generation state.entry (state.current.environmentResult command native)
        state.retired ordered same
      have archived := congrArg (fun state => (state.phases, state.retired)) settled
      exact archived
    · cases (PMF.mem_support_pure_iff ..).mp reached
      rfl

/-- An actual prefix that retains its original attempt keeps both its
installed descriptors and its archived attempts. Namespace monotonicity
rules out an intervening reset. -/
theorem phase_attempt_metadata_of_prefix
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State)
    (initialized : ∀ state ∈ initial.support, state.Ordered) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (trace : (menu.protocol initial horizon scheduler).Trace (some after))
    (retained : TracePrefix prior trace) (ordered : before.execution.application.Ordered)
    (same : before.execution.application.attempt = after.execution.application.attempt) :
    (before.execution.application.phases, before.execution.application.retired) =
      (after.execution.application.phases, after.execution.application.retired) := by
  have along : ∀ {target} {targetTrace : (menu.protocol initial horizon scheduler).Trace target},
      TracePrefix prior targetTrace → ∃ next : (phaseApplication runtime leaks).Control,
        target = some next ∧ next.execution.application.Ordered ∧
        (before.execution.application.attempt = next.execution.application.attempt →
          (next.execution.application.phases, next.execution.application.retired) =
            (before.execution.application.phases, before.execution.application.retired)) := by
    intro target targetTrace kept
    induction kept with
    | refl => exact ⟨before, rfl, ordered, fun _ => rfl⟩
    | @extend source target earlier kept joint legal reached ih =>
        obtain ⟨middle, rfl, middleOrdered, previous⟩ := ih
        have realized : target ∈ ((phaseApplication runtime leaks).transition initial horizon
            scheduler (some middle) joint).support := reached
        obtain ⟨next, rfl, _recalled⟩ := (phaseApplication runtime leaks).transition_recall_prefix
          initial horizon scheduler middle target joint realized
        have nextOrdered := (phaseApplication_seedOrder runtime leaks).transition initial horizon
          scheduler initialized (some middle) (some next) joint middleOrdered realized
        refine ⟨next, rfl, nextOrdered, ?_⟩
        intro finalSame
        have lower := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
          horizon scheduler before middle prior earlier kept ordered
        have progress := (phaseApplication_namespace_progress runtime leaks).transition initial
          horizon scheduler middle next joint realized middleOrdered
        have intermediate : before.execution.application.attempt =
            middle.execution.application.attempt := by
          have generation := congrArg CommitAttemptId.generation finalSame
          have phase := congrArg CommitAttemptId.phase finalSame
          cases first : before.execution.application.attempt with
          | mk firstPhase firstGeneration =>
              cases second : middle.execution.application.attempt with
              | mk secondPhase secondGeneration =>
                  simp only [first, second] at lower progress generation phase ⊢
                  congr 1 <;> omega
        exact ((same_attempt_metadata runtime leaks).transition initial horizon scheduler middle
          next joint realized middleOrdered (intermediate.symm.trans finalSame)).trans
            (previous intermediate)
  obtain ⟨next, equality, _ordered, result⟩ := along retained
  cases Option.some.inj equality
  exact (result same).symm

end Vegas.EventGraphRuntime
