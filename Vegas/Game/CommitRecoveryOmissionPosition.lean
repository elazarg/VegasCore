/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryPrefixConditioning
import Vegas.Game.CommitRecoveryContinuingProbability
import Vegas.Game.RecoveryReadyCommitInformation

/-! # Value-independent omission trembles at each source address -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)

/-- The omission bit of a continuing approximation is sampled only by its
reference tremble. Nonmissing failed bindings remain in the continuing part. -/
theorem commitRecovery_approximation_missing_law
    (n : Nat) (who : Player) (site : setup.commitRecoveryModel.InformationSite who) :
    ((approximation.sequence n).strategy who site.1).map
      (fun choice => CommitRecoveryMove.missed choice.1) =
      mix (approximation.epsilon n) (approximation.positive n).le (approximation.small n).le
        (((setup.commitRecoveryReference finite).strategy who site.1).map
          (fun choice => CommitRecoveryMove.missed choice.1)) (PMF.pure false) := by
  classical
  have noMissing (choice : Option (CommitRecoveryMove Player L))
      (continues : setup.CommitRecoveryContinues who site.1 choice) :
      CommitRecoveryMove.missed choice = false := by
    cases choice with
    | none => rfl
    | some move => exact (continues move rfl).1
  by_cases retained : (setup.commitRecoveryRestriction wellFormed).Retained who site.1
  · obtain ⟨original, observed⟩ := retained
    have same : (setup.commitRecoveryRestriction wellFormed).site who original = site :=
      Subtype.ext observed
    subst site
    obtain ⟨law, mixture⟩ := approximation.retained n who original
    change PMF.map _ ((approximation.sequence n).strategy who
      ((setup.commitRecoveryRestriction wellFormed).information who original.1)) = _
    rw [mixture, mix_map, PMF.map_comp]
    congr 1
    calc
      _ = law.map (fun _ => false) := by
        apply congrArg (fun f => law.map f)
        funext choice
        change CommitRecoveryMove.missed (CommitRecoveryMove.lift choice.1) = false
        cases choice.1 <;> rfl
      _ = _ := PMF.map_const _ _
  · obtain ⟨law, mixture⟩ := approximation.fresh n who site retained
    rw [mixture, mix_map, PMF.map_comp]
    congr 1
    calc
      _ = law.map (fun _ => false) := by
        apply congrArg (fun f => law.map f)
        funext choice
        exact noMissing choice.1.1 choice.2
      _ = _ := PMF.map_const _ _

/-- At any two genuine clear auxiliary sites at the same static address,
omission has exactly the same law at every approximation index. Thus observing
this bit cannot tilt the relative weights of their hidden source values. -/
theorem commitRecovery_approximation_missing_eq_of_position
    (n : Nat) (who : Player) (first second : SourceProgram.ProtocolView who setup.program)
    (samePosition : ProtocolView.position who setup.program first =
      ProtocolView.position who setup.program second)
    (firstDecision : setup.commitRecoveryModel.IsDecisionInfo who
      (setup.commitRecoveryClearInformation wellFormed who (some first)))
    (secondDecision : setup.commitRecoveryModel.IsDecisionInfo who
      (setup.commitRecoveryClearInformation wellFormed who (some second))) :
    ((approximation.sequence n).strategy who
      (setup.commitRecoveryClearInformation wellFormed who (some first))).map
        (fun choice => CommitRecoveryMove.missed choice.1) =
      ((approximation.sequence n).strategy who
        (setup.commitRecoveryClearInformation wellFormed who (some second))).map
          (fun choice => CommitRecoveryMove.missed choice.1) := by
  rw [setup.commitRecovery_approximation_missing_law finite wellFormed target approximation n who
      ⟨_, firstDecision⟩,
    setup.commitRecovery_approximation_missing_law finite wellFormed target approximation n who
      ⟨_, secondDecision⟩,
    setup.commitRecoveryReference_missing_eq_of_position finite wellFormed who first second
      samePosition]

/-- Genuine initialized source traces supply their decision sites themselves.
Their complete own words may differ; at the same owned source address the
approximating omission laws remain identical. -/
theorem commitRecovery_approximation_missing_eq_at_traces
    (n : Nat) (who : Player) (first second : CommitRecoveryState setup.program)
    (firstTrace : setup.commitRecoveryProtocol.Trace (some first))
    (secondTrace : setup.commitRecoveryProtocol.Trace (some second))
    (firstClear : first.excluded = ∅) (secondClear : second.excluded = ∅)
    (firstActor : ProtocolState.actor setup.program first.point = some who)
    (secondActor : ProtocolState.actor setup.program second.point = some who)
    (samePosition : ProtocolView.position who setup.program
        (ProtocolState.observe who setup.program first.point) =
      ProtocolView.position who setup.program
        (ProtocolState.observe who setup.program second.point)) :
    ((approximation.sequence n).strategy who
      (setup.commitRecoveryModel.infoOf who firstTrace)).map
        (fun choice => CommitRecoveryMove.missed choice.1) =
      ((approximation.sequence n).strategy who
        (setup.commitRecoveryModel.infoOf who secondTrace)).map
          (fun choice => CommitRecoveryMove.missed choice.1) := by
  have firstDecision := Vegas.commitRecovery_isDecisionInfo_of_actor setup first firstTrace who
    firstClear firstActor
  have secondDecision := Vegas.commitRecovery_isDecisionInfo_of_actor setup second secondTrace who
    secondClear secondActor
  have firstInfo := setup.commitRecoveryClearInformation_observed wellFormed who firstTrace
    firstClear
  have secondInfo := setup.commitRecoveryClearInformation_observed wellFormed who secondTrace
    secondClear
  simp only [commitRecoveryPrivate, Option.map_some] at firstInfo secondInfo
  rw [firstInfo] at firstDecision
  rw [secondInfo] at secondDecision
  have laws := setup.commitRecovery_approximation_missing_eq_of_position finite wellFormed target
    approximation n who _ _ samePosition firstDecision secondDecision
  have firstLaw := congrArg (fun info : setup.commitRecoveryModel.InfoState who =>
    ((approximation.sequence n).strategy who info).map
      (fun choice => CommitRecoveryMove.missed choice.1)) firstInfo
  have secondLaw := congrArg (fun info : setup.commitRecoveryModel.InfoState who =>
    ((approximation.sequence n).strategy who info).map
      (fun choice => CommitRecoveryMove.missed choice.1)) secondInfo
  exact firstLaw.trans (laws.trans secondLaw.symm)

end Vegas.SourceProgram.Setup
