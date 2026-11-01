/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryComparisonContinuationValue
import Vegas.Game.OnePacketSiteLinearity

/-! # Source values across a completed intended event -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

/-- A completed failed event in a genuine native history retains its owner's
source obligation, independently of any future service guarantee. -/
theorem decodedDebt_of_failed_event
    (history : (NP).History) (control : (application setup runtime leaks).Control)
    (current : history.state = some control) (event : (graph setup).EventId)
    (completed : event ∈ control.execution.application.config.cut.completed)
    (who : Player) (owned : (graph setup).actor? event = some who)
    (failed : StoreEventFailed control.execution.application.config.store event) :
    DecodedState setup runtime leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure who setup.program) history.state := by
  let valid : (application setup runtime leaks).ServiceInvariant scheduler
      (fun execution => SourceFailureRecord (failureProfile setup.program)
        execution.application.config) :=
    { respond := fun execution actor response holds => by
        rw [(runtime.reactive_respond_application leaks execution actor response).1]
        exact holds
      environment := fun execution next command holds _chosen reached =>
        holds.step (environmentStep_configStep setup leaks execution next command reached) }
  have record := valid.history (initialLaw setup) horizon (fun state supported => by
    obtain ⟨initial, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact SourceFailureRecord.initial setup (failureProfile setup.program) initial)
    ((bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.trace))
  obtain ⟨rank, residual, holds⟩ := record
  rw [current]
  exact ⟨rank, residual, holds event completed who owned failed⟩

/-- A recorded completion point includes the successful intended source
checkpoint and the predicate used to select that point. -/
theorem completionPoint_spec
    (rank : Nat) (fresh : (application setup runtime leaks).Control → Prop)
    (history : (NP).History) (point : ProtocolState setup.program)
    (somePoint : completionPoint setup runtime leaks bounds horizon scheduler rank fresh history =
      some point) :
    ∃ control : (application setup runtime leaks).Control, history.state = some control ∧
      control.execution.application.config.cut.IsPrefix (rank + 1) ∧
      sourceServicePrefix? setup (rank + 1) control.execution.application.config = some point ∧
      ProtocolState.Intended setup.program point ∧ fresh control := by
  classical
  unfold completionPoint at somePoint
  split at somePoint
  · cases somePoint
  · rename_i control state
    split at somePoint
    · rename_i ordered
      split at somePoint
      · rename_i next decoded
        split at somePoint
        · rename_i good
          cases Option.some.inj somePoint
          exact ⟨control, state, ordered, decoded, good⟩
        · cases somePoint
      · cases somePoint
    · cases somePoint

end Vegas.RecoveryOnePacket
