/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAudit

/-! # The assessed response law at a genuine counted decision -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Restricting the assessed raw strategy preserves its exact response law
at every genuine counted source, including a source of zero assessed reach. -/
theorem counted_assessment_response_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (who : Player) (current : source.state = some ⟨remaining, some who, execution⟩) :
    countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
      who (execution.recall who) (execution.observe app who) =
    rawMenu.decodeProfile initial horizon scheduler assessment.strategy who
      (execution.recall who) (execution.observe app who) := by
  classical
  have running : ¬ countedProtocol.terminal source.state := by
    rw [current]
    intro stopped
    cases stopped.2
  have active : countedProtocol.active source.state who := by rw [current]; rfl
  obtain ⟨site, observed⟩ := countedModel.exists_informationSite_of_active who source running active
  have atInput : site.1 = some (execution.recall who, execution.observe app who) := by
    rw [observed]
    change (countedMenu.signals initial horizon scheduler).infoOf who source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  have covered (response : app.Action)
      (chosen : response ∈ (players who (execution.recall who)
        (execution.observe app who)).support) :
      response ∈ countedMenu.actions who (execution.recall who) (execution.observe app who) :=
    raw_equilibrium_counted_site_covered assessment equilibrium who site (execution.recall who)
      (execution.observe app who) atInput response chosen
  have embedded := countedMenu.embed_restrictPolicy initial horizon scheduler who (players who)
    (execution.recall who) (execution.observe app who) covered
  change ((countedMenu.embedPolicy initial horizon scheduler who
    (countedMenu.restrictPolicy initial horizon scheduler who (players who)))
      (some (execution.recall who, execution.observe app who))).map
        (fun selected => selected.1.getD ⟨none⟩) =
      players who (execution.recall who) (execution.observe app who)
  rw [embedded]
  simp only [ReactiveApplication.encodePolicy, PMF.map_comp, Function.comp_def, Option.getD_some]
  change (players who (execution.recall who) (execution.observe app who)).map id = _
  exact PMF.map_id _

end Vegas.Examples.CommitSeedBroadcast
