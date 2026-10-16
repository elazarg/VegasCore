/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitReadStability
import Vegas.Game.RecoveryReadyCommitInformation
import Vegas.Game.CompiledCommitCompletion
import Vegas.Game.CompiledAttemptExclusion
import Vegas.Pending.PhaseBindingInvariant
import Vegas.Pending.PhaseStoredCheckpoint
import Vegas.Pending.PhaseHistoryCheckpoint
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseNativeInvariant

/-! # Historical binding queries read from the actual completed source prefix -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem prefix_observation_congr {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (who : Player) (first second : SourceProgram.Config Player L Δ)
    (same : first.view who = second.view who) :
    ProtocolState.observe who (earlier.prepend suffix)
        (earlier.liftPoint suffix (ProtocolState.entry suffix first)) =
      ProtocolState.observe who (earlier.prepend suffix)
        (earlier.liftPoint suffix (ProtocolState.entry suffix second)) := by
  induction earlier with
  | nil => cases suffix <;>
      simp only [SourceProgram.CommitPrefix.prepend, SourceProgram.CommitPrefix.liftPoint,
        ProtocolState.entry,
        ProtocolState.observe, Sum.elim_inl] <;> rw [same]
  | commit name owner fresh guard rest ih =>
      exact congrArg Sum.inr (ih suffix first second same)

private theorem decoded_prefix_clear (setup : Setup (Player := Player) (L := L))
    (mode : ExecutionMode) {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (state : PhaseRuntimeState (serviceGraph setup mode))
    (coverage : state.FailureCoverage) (clear : state.current.excluded = ∅)
    (entry : SourceProgram.Config Player L Γ)
    (completed : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      embedding.event index ∈ state.current.native.config.cut.completed) :
    (decodeCommitAttempt setup.program mode block suffix embedding state.current.native entry
      ∅).2.1 = ∅ := by
  rw [decodeCommitAttempt_excluded_eq, Finset.empty_union]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro who missing
  obtain ⟨index, inside, acting, omitted⟩ := (mem_commitMissingOwners setup.program mode block
    suffix embedding state.current.native who).mp missing
  obtain ⟨owner, payload, _member, layout⟩ := block.binding_before_length suffix index inside
  have output : (serviceGraph setup mode).outputLayout (embedding.event index) =
      .binding owner payload := (embedding.layout_eq index).trans layout
  have failed : state.current.native.PublicFailure (embedding.event index) := by
    left
    rw [state.current.native.publicView_missedBinding _ owner payload output]
    exact ⟨completed index inside, omitted⟩
  have excluded := coverage.active.covered (embedding.event index) who acting failed
  rw [clear] at excluded
  exact Finset.notMem_empty _ excluded

/-- A genuine historical binding callback reads the very predecessor decoded
from its later clear completed physical prefix. Its old query coordinate is
retained even after that event has completed; pending sends are not decoded.
All native invariants and source own-word alignment come from the actual traces. -/
theorem RecoverySourceCheckpoint.binding_query_of_clear_completed_prefix
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (before after : (phaseApplication runtime leaks).Control)
    (beforeTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some before))
    (afterTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some after))
    (isPrefix : TracePrefix beforeTrace afterTrace)
    (clear : after.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode before.execution.application)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (selected : Fin (eventCount checkpoint.residual.tail)) (atEnd : selected.val = earlier.length)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, checkpoint.embedding.event selected⟩)
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (completed :
      let embedding := cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
        (outputLayout setup.program) program) reconstruct.symm) checkpoint.embedding
      ∀ index : Fin (eventCount (earlier.prepend (.commit name owner fresh guard next))),
        index.val < earlier.length →
          embedding.event index ∈ after.execution.application.current.native.config.cut.completed) :
    let embedding := cast (congrArg (fun program => OutputEmbedding (inputLayout setup.context)
      (outputLayout setup.program) program) reconstruct.symm) checkpoint.embedding
    let decoded := decodeCommitAttempt setup.program mode earlier
      (.commit name owner fresh guard next) embedding after.execution.application.current.native
      checkpoint.source ∅
    phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
        (before.execution.observe (phaseApplication runtime leaks) owner) =
      some (ProtocolState.observe owner setup.program (checkpoint.residual.lift
        (cast (congrArg ProtocolState reconstruct)
          (earlier.liftPoint (.commit name owner fresh guard next)
            (ProtocolState.entry (.commit name owner fresh guard next) decoded.1))))) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawBefore := menu.toRawTrace initial horizon scheduler beforeTrace
  have rawAfter := menu.toRawTrace initial horizon scheduler afterTrace
  have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before after beforeTrace afterTrace isPrefix clear).1
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    rawBefore
  have afterCoverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    rawAfter
  have savedClear : before.execution.application.entry.excluded = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro who excluded
    have current := coverage.inherited excluded
    rw [beforeClear] at current
    exact Finset.notMem_empty _ current
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler rawBefore
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawBefore
  have retained := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler
    rawBefore
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    rawBefore
  have frontier := (phaseApplication_frontier runtime leaks).history initial horizon scheduler
    (by
      intro state supported
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_frontier plan draw) rawBefore
  have saved : before.execution.application.entry.native.config.cut.IsPrefix
      before.execution.application.attempt.phase := by
    obtain ⟨phase, head, _inside⟩ := request.2.1
    cases phases : before.execution.application.phases with
    | nil => simp only [phases, List.head?_nil, Option.mem_def, reduceCtorEq] at head
    | cons active remaining =>
        have positioned := frontier.positioned
        rw [phases] at positioned
        simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
          Option.getD_some] using positioned.1
  have aligned := checkpoint.filled_prefix_history_of_ready fresh guard next earlier reconstruct
    savedClear selected atEnd request.2.2.1 acting bindings.active valid.active.reachable retained
      saved
  have decodedBefore := checkpoint.filled_prefix_view fresh guard next earlier reconstruct stored
    selected atEnd request.2.2.1 acting notPublication _ aligned
  have sourceBefore := phaseSourceView?_observed setup mode runtime leaks before.execution owner
    (checkpoint.embedding.event selected)
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, priorCut,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    savedHistory, origin⟩
  dsimp only at *
  change SourceProgram.Config Player L Γ at source
  change SourceProgram.CommitPrefix Γ O Δ P at earlier
  change Fin (eventCount program) at selected
  change earlier.prepend (.commit name owner fresh guard next) = program at reconstruct
  subst program
  let suffix : SourceProgram Player L Δ P := .commit name owner fresh guard next
  have stability := fillCommitPrefix_view_of_clear_prefix setup mode runtime leaks menu initial
    horizon scheduler before after beforeTrace afterTrace isPrefix clear earlier suffix embedding
      source owner selected atEnd request.2.2.1 acting notPublication
  have afterBindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler
    rawAfter
  have decodedClear := decoded_prefix_clear setup mode earlier suffix embedding
    after.execution.application afterCoverage clear source completed
  have decodeFill := decodeCommitAttempt_eq_fill_of_clear setup.program mode earlier suffix
    embedding after.execution.application.current.native afterBindings.active source ∅ completed
      decodedClear
  rw [sourceBefore, decodedBefore]
  change some (ProtocolState.observe owner setup.program
      (lift (earlier.liftPoint suffix (ProtocolState.entry suffix
        (fillCommitPrefix setup.program earlier suffix embedding
          before.execution.application.current.native.config.store source))))) =
    some (ProtocolState.observe owner setup.program
      (lift (earlier.liftPoint suffix (ProtocolState.entry suffix
        (decodeCommitAttempt setup.program mode earlier suffix embedding
          after.execution.application.current.native source ∅).1))))
  rw [decodeFill]
  apply congrArg some
  rw [views.observe, views.observe]
  apply congrArg (views.view owner)
  exact prefix_observation_congr earlier suffix owner _ _ stability

end Vegas
