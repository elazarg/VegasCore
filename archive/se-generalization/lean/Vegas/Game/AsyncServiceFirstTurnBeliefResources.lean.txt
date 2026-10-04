/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceFirstTurnProfile

/-! # Physical resources on actual first-turn Bayes support

A history in the native Bayes belief has positive actual reach weight at its
own depth. The represented first-turn evaluator therefore supplies its physical
support and clears the owner's service risk. No clean-history assumption is
added when conditional continuation proofs consume these resources.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

/-- An actual positive-mass Bayes history belongs to the initialized physical
evaluator at its own history depth, including a pending owner activation. -/
theorem firstTurnProfile_bayes_history_roundSupported (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (who : Player) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let model := menu.information (initialLaw service.setup) service.horizon service.scheduler
    let strategy := service.firstTurnProfile turns profile
    ∀ (site : model.InformationSite who)
      (positive : 0 < model.informationMass strategy who site)
      (history : model.InformationHistory who site.1),
      history ∈ (model.bayesBelief strategy who site
        (menu.decisionInformationAntichain (initialLaw service.setup) service.horizon
          service.scheduler who site) positive).support →
      (application service.setup service.leaks).RoundSupported (initialLaw service.setup)
        service.horizon service.scheduler
        (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
          (firstTurnTiming service.setup turns) profile) history.1.state := by
  intro menu model strategy site positive history supported
  have reached : model.historyReachWeight strategy history.1 ≠ 0 := by
    intro zero
    have absent : model.bayesBelief strategy who site
        (menu.decisionInformationAntichain (initialLaw service.setup) service.horizon
          service.scheduler who site) positive history = 0 := by
      rw [model.bayesBelief_apply, zero]
      simp
    exact (PMF.mem_support_iff _ _).mp supported absent
  have physical : history.1 ∈ (model.runBehavioral strategy history.1.trace.length).support :=
    (PMF.mem_support_iff _ _).mpr reached
  exact service.firstTurnProfile_initialized_roundSupported turns profile permitted
    history.1.trace.length history.1 physical

/-- Every actual control in a first-turn Bayes belief has clear owner service
risk. This concerns the original conditional law, not perturbed waiting play. -/
theorem firstTurnProfile_bayes_serviceRisk_clear (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (who : Player) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let model := menu.information (initialLaw service.setup) service.horizon service.scheduler
    let strategy := service.firstTurnProfile turns profile
    ∀ (site : model.InformationSite who)
      (positive : 0 < model.informationMass strategy who site)
      (history : model.InformationHistory who site.1),
      history ∈ (model.bayesBelief strategy who site
        (menu.decisionInformationAntichain (initialLaw service.setup) service.horizon
          service.scheduler who site) positive).support →
      ∀ control, history.1.state = some control →
        (runtime service.setup).serviceRisk service.leaks service.bound who
          (control.execution.recall who)
          (control.execution.observe (application service.setup service.leaks) who) = false := by
  intro menu model strategy site positive history supported control current
  have physical := service.firstTurnProfile_bayes_history_roundSupported turns profile permitted
    who site positive history supported
  rw [current] at physical
  exact sourceServiceFirstTurn_serviceRisk_clear_roundSupported service.contract service.timely
    _ who turns profile rfl control physical

end Vegas.AsyncServiceSpec
