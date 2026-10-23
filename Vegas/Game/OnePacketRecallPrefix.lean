/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.OwnPlayPrefix
import Vegas.Game.OnePacketSpliceForced

/-! # Actual prefix witnesses from retained native recall -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- Final private recall determines the entire recorded own-play sequence,
including at a final state where the player is inactive. -/
theorem onePacket_ownPlay_recall (who : Player)
    {state : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) :
    (onePacketInformation setup leaks bounds horizon scheduler).ownPlay who trace =
      (application setup leaks).recallOwnPlay ((application setup leaks).recallAt who state) := by
  exact ((bounds.onePacketMenu (runtime setup) leaks).ownPlay_toRawTrace (initialLaw setup)
    horizon scheduler who trace).symm.trans
      ((application setup leaks).trace_ownPlay (initialLaw setup) horizon scheduler who
        ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
          scheduler trace))

/-- Every recorded native response has an actual initialized active prefix
with exactly its recorded decision information. -/
theorem initialized_prefix_of_mem_ownPlay
    {state : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    {who : Player}
    {recorded : (onePacketInformation setup leaks bounds horizon scheduler).InfoState who ×
      (application setup leaks).Action}
    (member : recorded ∈ (onePacketInformation setup leaks bounds horizon scheduler).ownPlay
      who trace) :
    ∃ (control : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control)),
      TracePrefix prior trace ∧ control.actor = some who ∧
        (onePacketInformation setup leaks bounds horizon scheduler).infoOf who prior =
          recorded.1 := by
  obtain ⟨before, after, prior, joint, legal, realized, isPrefix, info, selected⟩ :=
    InformationModel.exists_tracePrefix_of_mem_ownPlay trace member
  have localLegal := (onePacketProtocol setup leaks bounds horizon scheduler).legalOption_of_legal
    legal who
  rw [selected] at localLegal
  have acting := localLegal.1
  cases before with
  | none =>
      change (application setup leaks).actor none = some who at acting
      simp only [ReactiveApplication.actor, Option.bind_none] at acting
      cases acting
  | some control =>
      exact ⟨control, prior, (TracePrefix.extend .refl joint legal realized).trans isPrefix,
        acting, info⟩

/-- If every actual initialized prefix is a forced input for a player, every
decision remembered in the final recall is a forced input for that player. -/
theorem forcedAgent_of_recorded_decision
    {state : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (who : Player)
    (forcedPrefixes : ∀ (control : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control)),
      TracePrefix prior trace → forcedAgent (bounds.onePacketMenu (runtime setup) leaks)
        (initialLaw setup) horizon scheduler who ((application setup leaks).observe who
          (some control)))
    {recorded : (onePacketInformation setup leaks bounds horizon scheduler).InfoState who ×
      (application setup leaks).Action}
    (member : recorded ∈ (onePacketInformation setup leaks bounds horizon scheduler).ownPlay
      who trace) :
    forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler
      who recorded.1 := by
  obtain ⟨control, prior, isPrefix, _acting, info⟩ := initialized_prefix_of_mem_ownPlay trace member
  rw [← info, onePacket_infoOf]
  exact forcedPrefixes control prior isPrefix

end Vegas
