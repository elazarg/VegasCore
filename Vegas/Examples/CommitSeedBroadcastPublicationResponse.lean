/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPublicationChoice

/-! # Actual assessed responses at successful continuation publications -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

/-- At an actual successful publication callback, every supported decoded
equilibrium response transmits. The information-site witness is constructed
from the original history, and its full raw belief is used in the comparison. -/
theorem counted_successful_publication_response_nonsilent
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
      owner (execution.recall owner) (execution.observe app owner)).support) :
    response.transmission ≠ none := by
  classical
  let source : countedProtocol.History := ⟨some ⟨remaining, some owner, execution⟩, trace⟩
  let history := countedInRaw.history initial horizon scheduler source
  have sourceInfo : countedModel.infoOf owner source.trace =
      some (execution.recall owner, execution.observe app owner) := by
    change (countedMenu.signals initial horizon scheduler).infoOf owner source.trace = _
    rw [countedMenu.info]
    change app.observe owner (some ⟨remaining, some owner, execution⟩) = _
    simp only [ReactiveApplication.observe, ite_true]
  have rawInfo : rawModel.infoOf owner history.trace =
      some (execution.recall owner, execution.observe app owner) := by
    change (rawMenu.signals initial horizon scheduler).infoOf owner history.trace = _
    rw [rawMenu.info]
    change app.observe owner (some ⟨remaining, some owner, execution⟩) = _
    simp only [ReactiveApplication.observe, ite_true]
  have running : ¬ rawProtocol.terminal history.state := by
    intro stopped
    cases stopped.2
  have acting : rawProtocol.active history.state owner := rfl
  obtain ⟨⟨info, decision⟩, observed⟩ :=
    rawModel.exists_informationSite_of_active owner history running acting
  have same : info = some (execution.recall owner, execution.observe app owner) :=
    observed.trans rawInfo
  subst info
  let site : rawModel.InformationSite owner :=
    ⟨some (execution.recall owner, execution.observe app owner), decision⟩
  change response ∈ (app.decodePolicy
    (rawMenu.embedPolicy initial horizon scheduler owner (assessment.strategy owner))
      (execution.recall owner) (execution.observe app owner)).support at supported
  rw [ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    PMF.map_comp, PMF.support_map] at supported
  obtain ⟨choice, chosen, result⟩ := supported
  change choice.1.getD ⟨none⟩ = response at result
  obtain ⟨action, _allowed, selected⟩ := choice.2
  rw [selected, Option.getD_some] at result
  have rawSelected : choice.1 = some response := selected.trans (congrArg some result)
  intro quiet
  have responseEq : response = (⟨none⟩ : app.Action) := by
    cases response
    cases quiet
    rfl
  rw [responseEq] at rawSelected
  exact counted_successful_publication_wait_not_supported assessment equilibrium source
    remaining execution owner rfl retired request value stored site sourceInfo.symm
      choice rawSelected chosen

end Vegas.Examples.CommitSeedBroadcast
