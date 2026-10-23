/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketProjectedDecision

/-! # Owing sites and debt-free sites

At a decision input of `who` in the one-packet game, if `who` owes a failure at
the decoded point of one history, it owes one as a decoded state property of
every history of the input, for every source profile
(`Vegas.decodedState_owesFailure_of_infoOf`). Otherwise `who` owes no failure at
the decoded point of any history, which is the debt-freedom premise of
`Vegas.projectedDecision_of_forcedAgent`.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- A property of the decoded point of a native history is a decoded state
property of that history, for every source profile. -/
theorem decodedState_of_nativeDecodedState (profile : BehavioralProfile setup.program)
    {property : ProtocolState setup.program → Prop}
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    {point : ProtocolState setup.program}
    (decoded : nativeDecodedState setup leaks history.state = some point)
    (holds : property point) : DecodedState setup leaks profile property history.state := by
  obtain ⟨state, trace⟩ := history
  cases state with
  | none => cases decoded
  | some control =>
      obtain ⟨rank, ordered, read⟩ := decodedPoint_isPrefix (setup := setup) decoded
      exact decodedState_of_decode profile ⟨some control, trace⟩ control rfl ordered read holds

/-- Every initialized native history has a decoded point. -/
theorem nativeDecodedState_isSome
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    {control : (application setup leaks).Control} (current : history.state = some control) :
    ∃ point, nativeDecodedState setup leaks history.state = some point := by
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler history.trace control current
  rw [current]
  exact ⟨_, decodedPoint_eq residual⟩

private theorem state_of_infoOf {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      (some (past, view))) :
    ∃ control : (application setup leaks).Control, history.1.state = some control := by
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change (onePacketInformation setup leaks bounds horizon scheduler).infoOf who trace = _ at seen
  rw [onePacket_infoOf] at seen
  cases state with
  | none => cases seen
  | some control => exact ⟨control, rfl⟩

/-- **Owing at one history is owing at all.** If `who` owes a failure at the
decoded point of one history of a decision input of `who`, it owes one as a
decoded state property of every history of that input, for every source
profile. -/
theorem decodedState_owesFailure_of_infoOf (profile : BehavioralProfile setup.program)
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (owing : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      (some (past, view)))
    {point : ProtocolState setup.program}
    (decoded : nativeDecodedState setup leaks owing.1.state = some point)
    (owes : ProtocolState.OwesFailure who setup.program point)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      (some (past, view))) :
    DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
      history.1.state := by
  obtain ⟨control, current⟩ := state_of_infoOf history
  obtain ⟨other, otherDecoded⟩ := nativeDecodedState_isSome history.1 current
  exact decodedState_of_nativeDecodedState profile history.1 otherDecoded
    ((owesFailure_iff_of_infoOf owing history decoded otherDecoded).mp owes)

end Vegas
