/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketClearRecord
import Vegas.Game.OnePacketMainContent
import Vegas.Game.OnePacketOwnIntended

/-! # Regularity before public exclusion and focal source debt -/

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

/-- A clear regular prefix at which the focal player owes nothing decodes to an
actual intended source point. Arbitrary prior focal choices are allowed. -/
theorem intended_of_clear_regular_notOwes (wellFormed : setup.WellFormed)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (clear : PublicExclusionRecord
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point) :
    ∃ point, decodedPoint setup control.execution.application.config = some point ∧
      ProtocolState.Intended setup.program point :=
  intended_of_regular wellFormed source focal trace control rfl
    (publicRecord_of_publicExclusionRecord trace clear focal) regular
    (ownCompletionsIntended_of_notOwes wellFormed focal trace control rfl notOwed)

/-- Every responder is actually forced inside the clear regular debt-free
region; the current history itself supplies the information witness. -/
theorem forcedState_of_clear_regular_notOwes (wellFormed : setup.WellFormed)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (clear : PublicExclusionRecord
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (responder : Player) : ForcedState setup leaks responder (some control) := by
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes wellFormed source focal trace clear regular notOwed
  exact (forcedState_iff_decodedPoint control).mpr
    ⟨point, decoded, forcedPoint_of_intended responder intended⟩

/-- A source-main response of a foreign owner preserves the next regular-step
clause inside the clear region before focal source debt. -/
theorem regularStep_of_clear_regular_main (wellFormed : setup.WellFormed)
    (source : setup.intendedModel.BehavioralAssessment) (focal actor : Player)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some actor, execution⟩))
    (clear : PublicExclusionRecord (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon scheduler source focal prior)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal
      (some ⟨remaining, some actor, execution⟩) joint)
    (next : (application setup leaks).Control)
    (realized : some next ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step
      (some ⟨remaining, some actor, execution⟩) ⟨joint, legal⟩).support)
    (main : responseChoice setup leaks bounds (initialLaw setup) horizon scheduler actor
      (some (execution.recall actor, execution.observe (application setup leaks) actor))
      ((joint actor).getD ⟨none⟩) ∈
      (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source actor
        (some (execution.recall actor,
          execution.observe (application setup leaks) actor))).support) :
    RegularStep setup leaks bounds horizon scheduler source focal
      (some ⟨remaining, some actor, execution⟩) joint (some next) := by
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes wellFormed source focal prior clear regular notOwed
  have forced (player : Player) : ForcedState setup leaks player
      (some ⟨remaining, some actor, execution⟩) :=
    (forcedState_iff_decodedPoint _).mpr
      ⟨point, decoded, forcedPoint_of_intended player intended⟩
  obtain ⟨response, chosen, member, nextEq, _infoEq⟩ :=
    onePacket_response_step prior joint legal realized _ next rfl rfl rfl
  have actorNotOwed : ∀ found, decodedPoint setup execution.application.config = some found →
      ¬ ProtocolState.OwesFailure actor setup.program found := by
    intro found foundDecoded
    have same := Option.some.inj (decoded.symm.trans foundDecoded)
    subst found
    exact ProtocolState.Intended.not_owesFailure actor setup.program point intended
  have selected : (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler actor
      (some (execution.recall actor, execution.observe (application setup leaks) actor))
      response).1 = some response := by
    simp only [responseChoice, member, ↓reduceDIte]
  rw [chosen, Option.getD_some] at main
  have positive := contentFactor_pos_of_honestChoice source covers capacity prior actorNotOwed
    response member _ selected main
  intro responder acting _other
  cases Option.some.inj acting
  have informationForced := forcedAgent_of_history
    (⟨some ⟨remaining, some actor, execution⟩, prior⟩) (forced actor)
  rw [onePacket_infoOf] at informationForced
  refine ⟨⟨informationForced, forced focal⟩, ?_⟩
  rw [chosen, Option.getD_some, nextEq]
  exact positive

end Vegas
