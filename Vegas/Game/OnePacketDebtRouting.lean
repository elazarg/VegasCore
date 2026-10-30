/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceDebtObservation

/-! # Own source debt at native decision inputs

At a native decision input, an owner's decoded source debt at one history
holds throughout the information fiber, for every source profile. The result
uses actual current source endpoints and arbitrary native response menus.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {menu : (application setup runtime leaks).ResponseMenu} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- A property of the decoded point of a native history is a decoded state
property of that history, for every source profile. -/
theorem decodedState_of_nativeDecodedState (profile : BehavioralProfile setup.program)
    {property : ProtocolState setup.program → Prop}
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    {point : ProtocolState setup.program}
    (decoded : nativeDecodedState setup runtime leaks history.state = some point)
    (holds : property point) : DecodedState setup runtime leaks profile property history.state := by
  obtain ⟨state, trace⟩ := history
  cases state with
  | none => cases decoded
  | some control =>
      obtain ⟨rank, ordered, read⟩ := decodedPoint_isPrefix (setup := setup) decoded
      exact decodedState_of_decode (runtime := runtime) profile ⟨some control, trace⟩ control rfl
        ordered read holds

/-- Every initialized native history has a decoded point. -/
theorem nativeDecodedState_isSome
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    {control : (application setup runtime leaks).Control} (current : history.state = some control) :
    ∃ point, nativeDecodedState setup runtime leaks history.state = some point := by
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
    setup.program)
    menu horizon scheduler history.trace control current
  rw [current]
  exact ⟨_, decodedPoint_eq residual⟩

/-- **Owing at one history is owing at all.** If `who` owes a failure at the
decoded point of one history of a decision input of `who`, it owes one as a
decoded state property of every history of that input, for every source
profile. -/
theorem decodedState_owesFailure_of_infoOf (profile : BehavioralProfile setup.program)
    {who : Player} {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (owing : (menu.information (initialLaw setup) horizon scheduler).InformationHistory who
      (some (past, view)))
    {point : ProtocolState setup.program}
    (decoded : nativeDecodedState setup runtime leaks owing.1.state = some point)
    (owes : ProtocolState.OwesFailure who setup.program point)
    (history : (menu.information (initialLaw setup) horizon scheduler).InformationHistory who
      (some (past, view))) :
    DecodedState setup runtime leaks profile (ProtocolState.OwesFailure who setup.program)
      history.1.state := by
  obtain ⟨control, current, _view⟩ := control_of_infoOf (runtime := runtime) history.1 history.2
  obtain ⟨other, otherDecoded⟩ := nativeDecodedState_isSome (runtime := runtime) history.1 current
  exact decodedState_of_nativeDecodedState (runtime := runtime) profile history.1 otherDecoded
    ((owesFailure_iff_of_infoOf (runtime := runtime) owing history decoded otherDecoded).mp owes)

end Vegas
