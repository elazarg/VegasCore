/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixReadStability
import Vegas.Compile.CommitPrefixAdmission
import Vegas.Game.CompiledCommitPartialView
import Vegas.Pending.PhaseClearTraceProgress

/-! # Original commitment guard observations along actual clear phase histories -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

local notation "app" => phaseApplication runtime leaks

/-- An actual ready binding fixes its whole source predecessor observation and
own word. Later clear activity can fill hidden foreign cells but cannot change
that observation, even after this selected event has itself completed. -/
theorem fillCommitPrefix_view_of_clear_prefix
    (menu : (app).ResponseMenu) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (beforeTrace : (menu.protocol initial horizon scheduler).Trace (some before))
    (afterTrace : (menu.protocol initial horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix beforeTrace afterTrace)
    (clear : after.execution.application.current.excluded = ∅)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (entry : SourceProgram.Config Player L Γ) (who : Player)
    (selected : Fin (eventCount (block.prepend suffix))) (atEnd : selected.val = block.length)
    (ready : before.execution.application.current.native.config.cut.Ready
      (embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (embedding.event selected) = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (embedding.event selected)).IsPublication) :
    (fillCommitPrefix setup.program block suffix embedding
      before.execution.application.current.native.config.store entry).view who =
    (fillCommitPrefix setup.program block suffix embedding
      after.execution.application.current.native.config.store entry).view who := by
  have preserved := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before after beforeTrace afterTrace isPrefix clear).2.1
  exact fillCommitPrefix_view_of_extension setup.program block suffix embedding _ _ entry who
    preserved (commitPrefix_owned_fields_of_ready setup mode block suffix embedding
      before.execution.application.current.native.config who selected atEnd ready acting
      notPublication)

/-- Guard prediction reuses the original author's predecessor observation;
clock ticks, foreign callbacks and later completed bindings add no new reads. -/
theorem commit_guard_predicts_of_clear_prefix
    (menu : (app).ResponseMenu) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (beforeTrace : (menu.protocol initial horizon scheduler).Trace (some before))
    (afterTrace : (menu.protocol initial horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix beforeTrace afterTrace)
    (clear : after.execution.application.current.excluded = ∅)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (entry : SourceProgram.Config Player L Γ) (who : Player)
    (selected : Fin (eventCount (block.prepend suffix))) (atEnd : selected.val = block.length)
    (ready : before.execution.application.current.native.config.cut.Ready
      (embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (embedding.event selected) = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (embedding.event selected)).IsPublication)
    {name : VarId} {payload : L.Ty} (guard : SourceGuard L Δ who name payload)
    (value : L.Val payload) :
    guard.predicts (sourceObserve who (fillCommitPrefix setup.program block suffix embedding
      after.execution.application.current.native.config.store entry).state) value =
    guard.predicts (sourceObserve who (fillCommitPrefix setup.program block suffix embedding
      before.execution.application.current.native.config.store entry).state) value := by
  have views := fillCommitPrefix_view_of_clear_prefix setup mode runtime leaks menu initial
    horizon scheduler before after beforeTrace afterTrace isPrefix clear block suffix embedding
    entry who selected atEnd ready acting notPublication
  exact congrArg (fun view => guard.predicts view value) (congrArg Prod.fst views).symm

/-- Earlier own admission survives every later actual clear prefix extension.
No completion monotonicity is assumed separately; actual phase progress derives it. -/
theorem fillCommitPrefix_intendedFor_of_clear_prefix
    (menu : (app).ResponseMenu) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (beforeTrace : (menu.protocol initial horizon scheduler).Trace (some before))
    (afterTrace : (menu.protocol initial horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix beforeTrace afterTrace)
    (clear : after.execution.application.current.excluded = ∅)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (entry : SourceProgram.Config Player L Γ) (who : Player)
    (selected : Fin (eventCount (block.prepend suffix))) (atEnd : selected.val = block.length)
    (ready : before.execution.application.current.native.config.cut.Ready
      (embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (embedding.event selected) = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (embedding.event selected)).IsPublication)
    (admitted : (fillCommitPrefix setup.program block suffix embedding
      before.execution.application.current.native.config.store entry).IntendedFor who P) :
    (fillCommitPrefix setup.program block suffix embedding
      after.execution.application.current.native.config.store entry).IntendedFor who P := by
  have preserved := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before after beforeTrace afterTrace isPrefix clear).2.1
  exact fillCommitPrefix_intendedFor_of_extension setup.program block suffix embedding _ _ entry
    who preserved (commitPrefix_owned_fields_of_ready setup mode block suffix embedding
      before.execution.application.current.native.config who selected atEnd ready acting
      notPublication) admitted

end Vegas
