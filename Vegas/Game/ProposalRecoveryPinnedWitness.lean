/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryHonestPins
import Vegas.Game.ProposalRecoveryRestriction
import Vegas.Source.CommitRecoveryNoMissFixed

/-! # Genuine selected source decisions at archive-refined pinned pools -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

open Classical in
omit [Fintype setup.proposalRecoveryProtocol.History] in
private theorem semantic_noMiss_fixed_of_clear (who : Player)
    (history : setup.proposalRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state) :
    setup.commitRecoveryNoMissInformation who
        (setup.proposalRecoveryEraseInfo who
          (setup.proposalRecoveryModel.infoOf who history.trace)) =
      setup.proposalRecoveryEraseInfo who
        (setup.proposalRecoveryModel.infoOf who history.trace) := by
  rw [setup.proposalRecoveryEraseInfo_observed]
  rcases history with ⟨state, trace⟩
  cases state with
  | none =>
      unfold commitRecoveryNoMissInformation
      have current : (setup.commitRecoveryModel.infoOf who
          (setup.proposalRecoveryEraseTrace trace)).1.1.1 = none := by
        change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _).1.1.1 = _
        rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current]
        rfl
      simp only [current, Option.elim_none, Bool.false_eq_true, false_and, ite_false]
  | some current =>
      have empty : current.excluded = ∅ := clear
      have unchanged : current.excluded = current.entryExcluded :=
        Finset.Subset.antisymm (by rw [empty]; exact Finset.empty_subset _) current.entered
      exact setup.commitRecoveryNoMissInformation_eq_of_unchanged_exclusions who current
        (setup.proposalRecoveryEraseTrace trace) unchanged

open Classical in
/-- A present selected pin is justified by an actual intended decision,
not merely by an arbitrary intended history or a forgetful semantic key. -/
theorem proposalRecoveryHonestPoolPins_decision_witness
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (pinned : setup.proposalRecoveryHonestPoolPins wellFormed source
      (setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt site)) ≠ none) :
    ∃ honest : setup.intendedModel.InformationSite focal,
      setup.proposalRecoveryQuery focal site.1 = setup.proposalRecoveryQuery focal
        (((setup.proposalRecoveryRestriction wellFormed).site focal honest).1) := by
  classical
  have present : ∃ history : setup.intendedProtocol.History,
      setup.proposalRecoveryQuery focal (setup.proposalRecoveryInformation wellFormed focal
        (setup.intendedModel.infoOf focal history.trace)) =
          setup.proposalRecoveryQuery focal site.1 := by
    by_contra absent
    unfold proposalRecoveryHonestPoolPins at pinned
    exact pinned (dite_eq_right absent)
  obtain ⟨original, keys⟩ := present
  obtain ⟨_history, _running, move, offered⟩ := site.property
  let information := setup.proposalRecoveryInformation wellFormed focal
    (setup.intendedModel.infoOf focal original.trace)
  have semanticMenus : setup.commitRecoveryModel.menu focal
      (setup.proposalRecoveryEraseInfo focal information) = setup.commitRecoveryModel.menu focal
        (setup.proposalRecoveryEraseInfo focal site.1) := by
    rw [← setup.commitRecoveryNoMissInformation_menu focal
      (setup.proposalRecoveryEraseInfo focal information),
      ← setup.commitRecoveryErasedInformation_menu focal
        (setup.commitRecoveryNoMissInformation focal
          (setup.proposalRecoveryEraseInfo focal information)),
      show setup.commitRecoveryErasedInformation focal
          (setup.commitRecoveryNoMissInformation focal
            (setup.proposalRecoveryEraseInfo focal information)) =
        (setup.proposalRecoveryQuery focal site.1).1 from congrArg Prod.fst keys,
      ]
    change setup.commitRecoveryModel.menu focal
      (setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal
          (setup.proposalRecoveryEraseInfo focal site.1))) = _
    rw [setup.commitRecoveryErasedInformation_menu, setup.commitRecoveryNoMissInformation_menu]
  have allowed : setup.proposalRecoveryMenu focal information (some move) := by
    apply (setup.proposalRecoveryMenu_semantic focal information _).mpr
    change setup.proposalRecoveryMenu focal site.1 (some move) at offered
    have legal := (setup.proposalRecoveryMenu_semantic focal site.1 (some move)).mp offered
    constructor
    · change (some move).map (·.semantic) ∈ setup.commitRecoveryModel.menu focal
        (setup.proposalRecoveryEraseInfo focal information)
      rw [semanticMenus]
      exact legal.1
    · exact legal.2
  have active : setup.commitRecoveryProtocol.active
      (setup.commitRecoveryLiftHistory wellFormed original).state focal := by
    have actual := ((setup.proposalRecoveryModel.menu_adequate focal
      (setup.proposalRecoveryIntendedLift wellFormed original).trace (some move)).mp ?_).1
    · exact actual
    · rw [setup.proposalRecoveryInformation_observed]
      exact allowed
  have sourceActive := (setup.commitRecoveryLiftHistory_active wellFormed original focal).mp active
  have running : ¬ setup.intendedProtocol.terminal original.state := by
    change (setup.protocolObserve focal original.state).elim False
      (fun view => ProtocolView.actor focal setup.program view = some focal) at sourceActive
    cases state : original.state with
    | none =>
        simp only [state, protocolObserve, Option.map_none, Option.elim_none] at sourceActive
    | some point =>
        have acting : ProtocolView.actor focal setup.program
            (ProtocolState.observe focal setup.program point) = some focal := by
          simpa only [state, protocolObserve, Option.map_some, Option.elim_some] using sourceActive
        intro ended
        have impossible := ProtocolState.terminal_actor_none focal setup.program point ended
        rw [acting] at impossible
        cases impossible
  obtain ⟨honest, observed⟩ := setup.intendedModel.exists_informationSite_of_active
    focal original running sourceActive
  refine ⟨honest, ?_⟩
  change _ = setup.proposalRecoveryQuery focal
    (setup.proposalRecoveryInformation wellFormed focal honest.1)
  rw [observed]
  exact keys.symm

open Classical in
/-- At an ordinary actual fiber the pin supplies the exact erased full
information AND canonical archive of an embedded selected decision site. -/
theorem proposalRecoveryHonestPoolPins_ordinary_witness
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (first : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some first))
    (atSite : setup.proposalRecoveryModel.infoOf focal trace = site.1)
    (unchanged : first.excluded = first.entryExcluded)
    (pinned : setup.proposalRecoveryHonestPoolPins wellFormed source
      (setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt site)) ≠ none) :
    ∃ honest : setup.intendedModel.InformationSite focal,
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal site.1) =
        setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal
          (((setup.proposalRecoveryRestriction wellFormed).site focal honest).1)) ∧
      setup.proposalRecoveryArchive focal site.1 = setup.proposalRecoveryArchive focal
        (((setup.proposalRecoveryRestriction wellFormed).site focal honest).1) := by
  obtain ⟨honest, keys⟩ := setup.proposalRecoveryHonestPoolPins_decision_witness
    wellFormed source focal site pinned
  have ordinaryFixed : setup.commitRecoveryNoMissInformation focal
      (setup.proposalRecoveryEraseInfo focal site.1) =
        setup.proposalRecoveryEraseInfo focal site.1 := by
    rw [← atSite, setup.proposalRecoveryEraseInfo_observed]
    exact setup.commitRecoveryNoMissInformation_eq_of_unchanged_exclusions focal first
      (setup.proposalRecoveryEraseTrace trace) unchanged
  obtain ⟨history, _running, _offered⟩ := honest.property
  have honestFixed := setup.semantic_noMiss_fixed_of_clear focal
    (setup.proposalRecoveryIntendedLift wellFormed history.1)
    (setup.commitRecoveryLiftHistory_clear wellFormed history.1)
  rw [setup.proposalRecoveryInformation_observed, history.property] at honestFixed
  refine ⟨honest, ?_, congrArg Prod.snd keys⟩
  have semantic := congrArg Prod.fst keys
  change setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal (setup.proposalRecoveryEraseInfo focal site.1)) =
    setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal (setup.proposalRecoveryEraseInfo focal
        (((setup.proposalRecoveryRestriction wellFormed).site focal honest).1))) at semantic
  change setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal (setup.proposalRecoveryEraseInfo focal site.1)) =
    setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal (setup.proposalRecoveryEraseInfo focal
        (setup.proposalRecoveryInformation wellFormed focal honest.1))) at semantic
  rw [ordinaryFixed, honestFixed] at semantic
  exact semantic

end Vegas.SourceProgram.Setup
