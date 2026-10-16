/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphInputs
import Vegas.Compile.EventGraphObservation
import Vegas.EventGraph.ExecutionMode
import Vegas.Pending.EventApplication
import Vegas.Source.CommitRecoveryObservedClosure
import Vegas.Source.CommitRecoverySurvivingInformation

/-! # Complete source information at the original physical setup draw -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Equal actual initial native observations give genuine source setup traces
with identical complete auxiliary information, including own play. -/
theorem initialized_recovery_source_information
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode) (who : Player)
    (first second : State L setup.context)
    (firstSupported : first ∈ setup.initialLaw.support)
    (secondSupported : second ∈ setup.initialLaw.support)
    (observed : ((toEventGraph setup.program).withMode mode).playerObserve who
        (EventGraphRuntime.State.initial (encodeInputs first)).config =
      ((toEventGraph setup.program).withMode mode).playerObserve who
        (EventGraphRuntime.State.initial (encodeInputs second)).config) :
    ∃ (firstTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
          (ProtocolState.entry setup.program (setup.initialConfig first)) ∅ 0)))
      (secondTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
          (ProtocolState.entry setup.program (setup.initialConfig second)) ∅ 0))),
      setup.commitRecoveryModel.infoOf who firstTrace =
        setup.commitRecoveryModel.infoOf who secondTrace := by
  let graph := (toEventGraph setup.program).withMode mode
  let refs := ContextRefs.initial setup.context (outputLayout setup.program)
  have firstDecoded := decodeObservation?_playerStore_eq_some (graph := graph) refs who first
    (EventGraphRuntime.State.initial (encodeInputs first)).config.store
    (initialConfig_agrees setup.program first)
  have secondDecoded := decodeObservation?_playerStore_eq_some (graph := graph) refs who second
    (EventGraphRuntime.State.initial (encodeInputs second)).config.store
    (initialConfig_agrees setup.program second)
  have stores := congrArg (fun view => view.store) observed
  have sourceObserved : sourceObserve who first = sourceObserve who second := by
    apply Option.some.inj
    calc
      some (sourceObserve who first) = _ := firstDecoded.symm
      _ = _ := congrArg (decodeObservation? who refs) stores
      _ = some (sourceObserve who second) := secondDecoded
  have views : (setup.initialConfig first).view who = (setup.initialConfig second).view who :=
    Prod.ext sourceObserved rfl
  have entries := ProtocolState.observe_entry_congr who setup.program _ _ views
  let firstState := CommitRecoveryState.atPoint
    (ProtocolState.entry setup.program (setup.initialConfig first)) ∅ 0
  let secondState := CommitRecoveryState.atPoint
    (ProtocolState.entry setup.program (setup.initialConfig second)) ∅ 0
  have legal : setup.commitRecoveryProtocol.Legal none (fun _ => none) :=
    ⟨(fun impossible => impossible), (fun _ impossible => impossible)⟩
  let firstTrace : setup.commitRecoveryProtocol.Trace (some firstState) :=
    .extend .start (fun _ => none) legal
      ((PMF.mem_support_map_iff _ _ _).mpr ⟨first, firstSupported, rfl⟩)
  let secondTrace : setup.commitRecoveryProtocol.Trace (some secondState) :=
    .extend .start (fun _ => none) legal
      ((PMF.mem_support_map_iff _ _ _).mpr ⟨second, secondSupported, rfl⟩)
  have privateEq : setup.commitRecoveryPrivate who (some firstState) =
      setup.commitRecoveryPrivate who (some secondState) := congrArg some entries
  have publicEq : setup.commitRecoveryPublic (some firstState) =
      setup.commitRecoveryPublic (some secondState) := by
    simp only [Setup.commitRecoveryPublic, firstState, secondState, CommitRecoveryState.atPoint,
      ProtocolState.remaining_entry]
  refine ⟨firstTrace, secondTrace, ?_⟩
  apply setup.commitRecovery_surviving_info_eq who
  · exact Finset.notMem_empty _
  · exact Finset.notMem_empty _
  · change ((setup.commitRecoveryPrivate who (some firstState),
        setup.commitRecoveryPublic (some firstState)), [(none, (∅, 0, 0))]) =
      ((setup.commitRecoveryPrivate who (some secondState),
        setup.commitRecoveryPublic (some secondState)), [(none, (∅, 0, 0))])
    rw [privateEq, publicEq]

end Vegas
