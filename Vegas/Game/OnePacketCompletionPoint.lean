/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateSuccess
import Vegas.Game.SourceFailureRecord

/-! # Intended completion points in native histories -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler

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
  have record := SourceFailureRecord.history (runtime := runtime) (failureProfile setup.program)
    horizon scheduler
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
      LateStopped setup runtime leaks bounds horizon scheduler rank history ∧
      decodedPoint setup control.execution.application.config = some point ∧
      ProtocolState.Intended setup.program point ∧ fresh control := by
  classical
  unfold completionPoint at somePoint
  split at somePoint
  · cases somePoint
  · rename_i control state
    split at somePoint
    · rename_i completed
      split at somePoint
      · rename_i next decoded
        split at somePoint
        · rename_i good
          cases Option.some.inj somePoint
          exact ⟨control, state, completed, decoded, good⟩
        · cases somePoint
      · cases somePoint
    · cases somePoint


end Vegas
