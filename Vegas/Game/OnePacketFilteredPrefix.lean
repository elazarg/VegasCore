/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketClearRegularity
import Vegas.Game.OnePacketSpliceForced
import Vegas.Pending.ExclusionNativeFailure

/-! # Backward guards at actual clear regular prefixes -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- Regularity of a full actual trace holds at each of its prefixes. -/
theorem regularTrace_of_tracePrefix
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {first final : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    {prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first}
    {top : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final}
    (isPrefix : TracePrefix prior top)
    (regular : RegularTrace setup leaks bounds horizon scheduler source focal top) :
    RegularTrace setup leaks bounds horizon scheduler source focal prior := by
  induction isPrefix with
  | refl => exact regular
  | extend _ _ _ _ ih => exact ih regular.1

/-- Actual forcedness at an endpoint reaches every initialized native prefix. -/
theorem forcedState_of_tracePrefix
    (who : Player) {control : (application setup leaks).Control}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    {state : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    {top : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state}
    (isPrefix : TracePrefix prior top) (forced : ForcedState setup leaks who state) :
    ForcedState setup leaks who (some control) := by
  induction isPrefix with
  | refl => exact forced
  | @extend source target before earlier joint legal realized ih =>
      cases source with
      | none => exact (not_tracePrefix_start before earlier).elim
      | some previous => exact ih (forcedState_of_transition before joint realized forced)

/-- Public clearance of an actual native endpoint reaches all earlier prefixes;
completed public failures cannot disappear. -/
theorem clearRecord_of_tracePrefix
    {first final : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    {prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first}
    {top : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final}
    (isPrefix : TracePrefix prior top)
    (clear : ReactiveApplication.stateInvariant (app := application setup leaks)
      (fun native => PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState (graph setup))) final) :
    ReactiveApplication.stateInvariant (app := application setup leaks)
      (fun native => PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState (graph setup))) first := by
  induction isPrefix with
  | refl => exact clear
  | @extend source target before earlier joint legal realized ih =>
      apply ih
      cases source with
      | none => trivial
      | some current =>
          apply native_clear_before_transition (runtime setup) leaks (initialLaw setup)
            (serviceInitialLaw_initialized setup) horizon scheduler
            ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
              scheduler before) joint realized ?_ current rfl
          intro next same
          subst target
          exact clear

/-- A clear regular endpoint before focal debt gives the same three guards at
all initialized prefixes, using any distinct owner to reflect focal debt. -/
theorem clear_regular_notOwes_of_tracePrefix
    (wellFormed : setup.WellFormed)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {before final : (application setup leaks).Control}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some before))
    (top : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some final))
    (isPrefix : TracePrefix prior top)
    (clear : PublicExclusionRecord
      (⟨final.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon scheduler source focal top)
    (notOwed : ∀ point, decodedPoint setup final.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point) :
    PublicExclusionRecord (⟨before.execution.application, ∅⟩ : RecoveryState (graph setup)) ∧
      RegularTrace setup leaks bounds horizon scheduler source focal prior ∧
      ∀ point, decodedPoint setup before.execution.application.config = some point →
        ¬ ProtocolState.OwesFailure focal setup.program point := by
  have forced := forcedState_of_clear_regular_notOwes wellFormed source focal top clear regular
    notOwed owner
  have earlier := forcedState_of_tracePrefix owner prior isPrefix forced
  obtain ⟨point, decoded, forcedPoint⟩ := (forcedState_iff_decodedPoint before).mp earlier
  refine ⟨clearRecord_of_tracePrefix isPrefix clear,
    regularTrace_of_tracePrefix source focal isPrefix regular, ?_⟩
  intro other otherDecoded
  cases Option.some.inj (decoded.symm.trans otherDecoded)
  exact (forcedPoint.2 focal (Ne.symm different)).2

end Vegas
