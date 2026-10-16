/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryHonestPrescription
import Vegas.Source.CommitRecoveryNoMissFixed

/-! # Genuine honest decision witnesses for the actual pinned source pools -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
private theorem current_signal (who : Player) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.commitRecoveryModel.infoOf who trace).1.1 =
      (setup.commitRecoveryPrivate who state, setup.commitRecoveryPublic state) := by
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1.1 = _
  rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current who trace]

omit [Fintype Player] in
private theorem noMiss_fixed_of_clear (who : Player)
    (history : setup.commitRecoveryProtocol.History)
    (clear : history.state.elim True (fun current => current.excluded = ∅)) :
    setup.commitRecoveryNoMissInformation who (setup.commitRecoveryModel.infoOf who history.trace) =
      setup.commitRecoveryModel.infoOf who history.trace := by
  rcases history with ⟨state, trace⟩
  cases state with
  | none =>
      unfold commitRecoveryNoMissInformation
      rw [setup.current_signal]
      simp only [commitRecoveryPrivate, Option.map_none, Option.elim_none,
        Bool.false_eq_true, false_and, ite_false]
  | some current =>
      have empty : current.excluded = ∅ := clear
      have unchanged : current.excluded = current.entryExcluded :=
        Finset.Subset.antisymm (by rw [empty]; exact Finset.empty_subset _) current.entered
      exact setup.commitRecoveryNoMissInformation_eq_of_unchanged_exclusions
        who current trace unchanged

variable [setup.FiniteInitialLaw] [Fintype setup.commitRecoveryProtocol.History]

open Classical in
/-- A nonempty actual honest pin at a decision pool supplies a genuine honest
decision site, not merely an intended history with unknown activity. -/
theorem commitRecoveryHonestPoolPins_decision_witness
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who) (focal : Player)
    (ordinary : setup.commitRecoveryModel.InformationSite focal)
    (pinned : setup.commitRecoveryHonestPoolPins finite wellFormed source
      (setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt ordinary)) ≠ none) :
    ∃ honest : setup.intendedModel.InformationSite focal,
      setup.commitRecoveryErasedInformation focal
          (setup.commitRecoveryNoMissInformation focal ordinary.1) =
        setup.commitRecoveryErasedInformation focal (setup.commitRecoveryNoMissInformation focal
          ((setup.commitRecoveryRestriction wellFormed).site focal honest).1) := by
  classical
  have present : ∃ history : setup.intendedProtocol.History,
      setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal
          (setup.commitRecoveryInformation wellFormed focal
            (setup.intendedModel.infoOf focal history.trace))) =
      setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal ordinary.1) := by
    by_contra absent
    unfold commitRecoveryHonestPoolPins at pinned
    exact pinned (dite_eq_right absent)
  obtain ⟨original, keys⟩ := present
  obtain ⟨_witness, _running, move, offered⟩ := ordinary.property
  have menus : setup.commitRecoveryModel.menu focal
        (setup.commitRecoveryInformation wellFormed focal
          (setup.intendedModel.infoOf focal original.trace)) =
      setup.commitRecoveryModel.menu focal ordinary.1 := by
    rw [← setup.commitRecoveryNoMissInformation_menu focal
      (setup.commitRecoveryInformation wellFormed focal
        (setup.intendedModel.infoOf focal original.trace)),
      ← setup.commitRecoveryErasedInformation_menu focal
        (setup.commitRecoveryNoMissInformation focal
          (setup.commitRecoveryInformation wellFormed focal
            (setup.intendedModel.infoOf focal original.trace))), keys,
      setup.commitRecoveryErasedInformation_menu, setup.commitRecoveryNoMissInformation_menu]
  have liftedActive : setup.commitRecoveryProtocol.active
      (setup.commitRecoveryLiftHistory wellFormed original).state focal := by
    apply ((setup.commitRecoveryModel.menu_adequate focal
      (setup.commitRecoveryLiftHistory wellFormed original).trace (some move)).mp ?_).1
    rw [setup.commitRecoveryInformation_observed, menus]
    exact offered
  have active := (setup.commitRecoveryLiftHistory_active wellFormed original focal).mp liftedActive
  have running : ¬ setup.intendedProtocol.terminal original.state := by
    change (setup.protocolObserve focal original.state).elim False
      (fun view => ProtocolView.actor focal setup.program view = some focal) at active
    cases state : original.state with
    | none =>
        simp only [state, protocolObserve, Option.map_none, Option.elim_none] at active
    | some point =>
        have acting : ProtocolView.actor focal setup.program
            (ProtocolState.observe focal setup.program point) = some focal := by
          simpa only [state, protocolObserve, Option.map_some, Option.elim_some] using active
        intro ended
        change ProtocolState.terminal setup.program point at ended
        have impossible := ProtocolState.terminal_actor_none focal setup.program point ended
        rw [acting] at impossible
        cases impossible
  obtain ⟨honest, observed⟩ := setup.intendedModel.exists_informationSite_of_active
    focal original running active
  refine ⟨honest, ?_⟩
  change _ = setup.commitRecoveryErasedInformation focal
    (setup.commitRecoveryNoMissInformation focal
      (setup.commitRecoveryInformation wellFormed focal honest.1))
  rw [observed]
  exact keys.symm

open Classical in
/-- Every ordinary member of an actual honest-pinned pool has the same erased
key as an embedded honest decision site. Both no-new-miss fixed points are
derived from genuine initialized histories. -/
theorem commitRecoveryHonestPoolPins_ordinary_witness
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who) (focal : Player)
    (ordinary : setup.commitRecoveryModel.InformationSite focal)
    (committing : ordinary.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (unchanged : ordinary.1.1.1.2.1 = setup.commitRecoverySavedExclusions focal ordinary.1)
    (pinned : setup.commitRecoveryHonestPoolPins finite wellFormed source
      (setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt ordinary)) ≠ none) :
    ∃ honest : setup.intendedModel.InformationSite focal,
      setup.commitRecoveryErasedInformation focal ordinary.1 =
        setup.commitRecoveryErasedInformation focal
          ((setup.commitRecoveryRestriction wellFormed).site focal honest).1 := by
  classical
  obtain ⟨honest, keys⟩ := setup.commitRecoveryHonestPoolPins_decision_witness finite wellFormed
    source focal ordinary pinned
  have ordinaryFixed : setup.commitRecoveryNoMissInformation focal ordinary.1 = ordinary.1 := by
    obtain ⟨⟨⟨state, trace⟩, observed⟩, _running, _offered⟩ := ordinary.property
    have active := InformationModel.InformationSite.active setup.commitRecoveryModel ordinary
      ⟨⟨state, trace⟩, observed⟩
    cases state with
    | none => exact active.elim
    | some current =>
        have atCommit : ProtocolState.atCommit setup.program current.point = true := by
          rw [← observed, setup.current_signal] at committing
          simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
            ProtocolState.atCommit_observe] using committing
        obtain ⟨prior, kept, rank⟩ := setup.commitRecovery_attempt_entry current trace atCommit
        have read := setup.commitRecoverySavedExclusions_of_entry focal current trace
          prior kept rank
        have clear : current.excluded = current.entryExcluded := by
          rw [← observed, setup.current_signal, read] at unchanged
          exact unchanged
        rw [← observed]
        exact setup.commitRecoveryNoMissInformation_eq_of_unchanged_exclusions focal
          current trace clear
  have honestFixed : setup.commitRecoveryNoMissInformation focal
        ((setup.commitRecoveryRestriction wellFormed).site focal honest).1 =
      ((setup.commitRecoveryRestriction wellFormed).site focal honest).1 := by
    obtain ⟨history, _running, _offered⟩ := honest.property
    let lifted := setup.commitRecoveryLiftHistory wellFormed history.1
    have observed : setup.commitRecoveryModel.infoOf focal lifted.trace =
        ((setup.commitRecoveryRestriction wellFormed).site focal honest).1 :=
      (setup.commitRecoveryInformation_observed wellFormed focal history.1).trans
        (congrArg (setup.commitRecoveryInformation wellFormed focal) history.2)
    have fixed := setup.noMiss_fixed_of_clear focal lifted
      (setup.commitRecoveryLiftHistory_clear wellFormed history.1)
    rwa [observed] at fixed
  refine ⟨honest, ?_⟩
  rwa [ordinaryFixed, honestFixed] at keys

end Vegas.SourceProgram.Setup
