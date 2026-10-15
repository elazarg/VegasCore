/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventSourcePolicyLaw
import Vegas.Game.CommitRecoveryClearDecoder
import Vegas.Game.CommitRecoveryRestriction
import Vegas.Game.IntendedOpeningExtension

/-! # Copied auxiliary choices equal compiled intended policy laws -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- At a genuinely realized intended information set, the complete auxiliary
raw move law is the compiled opening extension's decoded action law with a
false omission flag. The original intended history is retained explicitly. -/
theorem commitRecovery_compiled_policy_raw_law (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (original : setup.intendedModel.InformationHistory who site.1)
    (view : SourceProgram.ProtocolView who setup.program) (current : site.1 = some view)
    (event : (toEventGraph setup.program).EventId)
    (actor : (toEventGraph setup.program).actor? event = some who)
    (observation : (toEventGraph setup.program).PlayerObservation who)
    (decoded : decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
        who event observation.store (decodeCompletions setup.program observation.ownActions) =
          some view) :
    let profile := setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
      (setup.openingExtension source)
    (target who (setup.commitRecoveryClearInformation wellFormed who (some view))).map
        Subtype.val =
      ((compileEventPolicy setup.program who (profile who)) event actor observation).map
        (fun action => CommitRecoveryMove.lift (decodeEventAction setup.program event action)) := by
  classical
  intro profile
  have clearInfo : setup.commitRecoveryClearInformation wellFormed who site.1 =
      setup.commitRecoveryInformation wellFormed who site.1 := by
    rw [← original.2]
    exact setup.commitRecoveryClearInformation_intended wellFormed who original.1
  have targetRaw :
      (target who (setup.commitRecoveryClearInformation wellFormed who (some view))).map
          Subtype.val =
        (source who site.1).map (fun choice => CommitRecoveryMove.lift choice.1) := by
    rw [← current, clearInfo]
    change PMF.map _ (target who
      ((setup.commitRecoveryRestriction wellFormed).information who site.1)) = _
    rw [copies who site, PMF.map_comp]
    rfl
  have structuralRaw : (profile who).protocolAction setup.program view =
      (source who site.1).map Subtype.val := by
    change (BehavioralPolicy.fromProtocol setup.program
      (CommitmentInterface.values setup.program)
      (fun view => setup.openingExtension source who (some view))).protocolAction
        setup.program view = _
    rw [BehavioralPolicy.protocolAction_fromProtocol]
    have rawCurrent := congrArg (fun info : setup.ProtocolView who =>
      (setup.openingExtension source who info).map Subtype.val) current
    have rawExtended := congrArg (fun law : PMF
        ((setup.informationModel (CommitmentInterface.values setup.program)).Choice who site.1) =>
      law.map Subtype.val) (setup.openingExtension_extends source who site)
    change (setup.openingExtension source who site.1).map Subtype.val =
      ((source who site.1).map
        ((setup.intendedRestriction (CommitmentInterface.values setup.program)).choice who
          site.1)).map Subtype.val at rawExtended
    calc
      _ = (setup.openingExtension source who site.1).map Subtype.val := rawCurrent.symm
      _ = _ := by
        rw [PMF.map_comp] at rawExtended
        exact rawExtended
  have compiled := compileEventPolicy_source_law setup.program who (profile who) event actor
    observation view decoded
  calc
    _ = (source who site.1).map (fun choice => CommitRecoveryMove.lift choice.1) := targetRaw
    _ = ((source who site.1).map Subtype.val).map CommitRecoveryMove.lift := by
      rw [PMF.map_comp]
      rfl
    _ = ((profile who).protocolAction setup.program view).map CommitRecoveryMove.lift := by
      rw [structuralRaw]
    _ = _ := by rw [← compiled, PMF.map_comp]; rfl

end Vegas.SourceProgram.Setup
