/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationProbabilities

/-! # Source beliefs cannot distinguish the hidden bit after a failed publication -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def sourceAssessment : sourceModel.BehavioralAssessment :=
  (InformationModel.BehavioralAssessment.ofStrategy uniformSourceProfile).bayes
    uniformSourceProfile_fullyMixed sourceAntichain

theorem source_consistent : sourceAssessment.IsSequentiallyConsistent sourceAntichain :=
  InformationModel.BehavioralAssessment.IsSequentiallyConsistent.of_fullyMixed_bayes
    sourceAntichain uniformSourceProfile_fullyMixed
    ((InformationModel.BehavioralAssessment.ofStrategy uniformSourceProfile).bayes_isBayesConsistent
      uniformSourceProfile_fullyMixed sourceAntichain)

def sourceBobSite (bit : Bool) (dummy : PublicationResult Bool) (first second : Bool) :
    sourceModel.InformationSite true :=
  sourceModel.informationSite true (SourcePath.secretPublished bit dummy first second).history
    (.reveal true 2 false) (by exact id) (by
      rw [source_info]
      exact ⟨rfl, false, rfl⟩)

theorem source_bob_history (site : sourceModel.InformationSite true)
    (history : sourceModel.InformationHistory true site.1) :
    ∃ bit dummy first second, history.1 =
      (SourcePath.secretPublished bit dummy first second).history := by
  have active := InformationModel.InformationSite.active sourceModel site history
  obtain ⟨path, same⟩ := source_history_complete history.1.trace
  change history.1 = path.history at same
  rw [same] at active
  cases path with
  | secretPublished bit dummy first second => exact ⟨bit, dummy, first, second, same⟩
  | _ => cases active

theorem source_bob_site (site : sourceModel.InformationSite true) :
    ∃ bit dummy first second, site = sourceBobSite bit dummy first second := by
  obtain ⟨history, _running, _action, _legal⟩ := site.2
  obtain ⟨bit, dummy, first, second, same⟩ := source_bob_history site history
  refine ⟨bit, dummy, first, second, Subtype.ext ?_⟩
  exact history.2.symm.trans (congrArg (fun h => sourceModel.infoOf true h.trace) same)

theorem secret_bob_observation (bit other : Bool) (dummy : PublicationResult Bool)
    (first second : Bool) (failed : ((first && dummy.isSuccess) || !second) = true) :
    sourceObserve true (secretConfig bit dummy first second).state =
      sourceObserve true (secretConfig other dummy first second).state := by
  apply sourceObserve_congr
  · intro name ty ref
    rcases ref with ref | ref | ref | ref | ref | ref | ref
    cases ref
  · intro name ty ref
    rcases ref with _ | _ | ref | ref | ref | ref | ref
    · rw [secret_publication, secret_publication, failed]
      rfl
    · change (dummyConfig bit dummy first).state.get .here =
        (dummyConfig other dummy first).state.get .here
      rw [dummy_publication, dummy_publication]
    · cases ref
  · intro name ty ref
    rcases ref with ref | ref | ref | ref | ref | ref | ref
    cases ref
  · intro name ty ref
    rcases ref with ref | ref | ref | ref | ref | _ | ref
    · change (PublicationResult.success true : PublicationResult Bool) = .success true
      rfl
    · cases ref

theorem secret_bob_view (bit other : Bool) (dummy : PublicationResult Bool)
    (first second : Bool) (failed : ((first && dummy.isSuccess) || !second) = true) :
    (secretConfig bit dummy first second).view true =
      (secretConfig other dummy first second).view true := by
  apply Prod.ext
  · exact secret_bob_observation bit other dummy first second failed
  · change (secretConfig bit dummy first second).history true =
      (secretConfig other dummy first second).history true
    simp [secretConfig, dummyConfig, boundConfig, startConfig, Setup.initialConfig,
      revealSuccessor, commitSuccessor]

theorem secret_bob_info (bit other : Bool) (dummy : PublicationResult Bool)
    (first second : Bool) (failed : ((first && dummy.isSuccess) || !second) = true) :
    sourceModel.infoOf true (SourcePath.secretPublished bit dummy first second).history.trace =
      sourceModel.infoOf true
        (SourcePath.secretPublished other dummy first second).history.trace := by
  rw [source_info, source_info]
  exact congrArg (fun view => (some (Sum.inr (Sum.inr (Sum.inr (Sum.inl view)))) :
    sourceModel.InfoState true))
    (secret_bob_view bit other dummy first second failed)

def sourceSecretResult : sourceModel.InfoState true → PublicationResult Bool
  | some (.inr (.inr (.inr (.inl view)))) => view.1.cells _ _ .here
  | _ => .failure

theorem source_secret_info (bit : Bool) (dummy : PublicationResult Bool) (first second : Bool) :
    sourceSecretResult (sourceModel.infoOf true
      (SourcePath.secretPublished bit dummy first second).history.trace) =
      if (first && dummy.isSuccess) || !second then .failure else .success bit := by
  rw [source_info]
  exact secret_publication bit dummy first second

theorem source_belief_prob (site : sourceModel.InformationSite true)
    (history : sourceModel.InformationHistory true site.1) :
    (sourceAssessment.belief true site).prob history =
      (1 / 24) / sourceModel.informationMass uniformSourceProfile true site := by
  rw [sourceAssessment, InformationModel.BehavioralAssessment.bayes,
    InformationModel.bayesBelief_prob]
  obtain ⟨bit, dummy, first, second, same⟩ := source_bob_history site history
  change sourceModel.historyReachProbability uniformSourceProfile history.1 / _ = _
  rw [same, source_reach_secret]
  rfl

end VegasTests.SequentialValidation
