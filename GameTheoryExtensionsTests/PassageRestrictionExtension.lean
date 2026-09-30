/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.PassageRestrictionExtension

/-! # The depth-free restriction extension subsumes the clocked one

The library's extension across an action restriction takes a common decision
depth at every retained site. The passage version derives the same conclusion
with the depth hypotheses discarded.
-/

noncomputable section

namespace GameTheoryExtensionsTests.PassageRestrictionExtension

open GameTheory GameTheory.Math.Probability GameTheory.Protocol GameTheory.Protocol.InformationModel
  GameTheory.Protocol.ExecutionProtocol

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E T : ExecutionProtocol ι} {M : InformationModel E} {N : InformationModel T}
  [Finite T.History] [∀ i, DecidableEq (N.InfoState i)]
  (restriction : M.ActionRestriction N)

theorem clocked_of_unclocked
    (sourceAntichain : M.DecisionInformationAntichain)
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall)
    (depth : ∀ who, M.InformationSite who → ℕ)
    (_clock : ∀ who site, InformationSite.CommonDepth N (restriction.site who site)
      (depth who site))
    (sourcePayoff : ι → E.History → ℝ) (targetPayoff : ι → T.History → ℝ)
    (matching : ∀ who history,
      targetPayoff who (restriction.history history) = sourcePayoff who history)
    (comparison : ∀ (sourceProfile : (i : ι) → M.BehavioralPolicy i)
      (targetProfile : (i : ι) → N.BehavioralPolicy i),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : M.InformationSite who)
        (action : N.Choice who (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        ∀ belief : PMF (M.InformationHistory who site.1),
          ∃ alternative : M.BehavioralPolicy who,
            expect belief (fun history => expect (N.runBehavioralTerminalFrom targetCertificate
              (Profile.update (sig := N.behavioralSignature) targetProfile who
                ((targetProfile who).commit (restriction.site who site).1 action))
              (restriction.history history.1)) (targetPayoff who)) ≤
            expect belief (fun history => expect (M.runBehavioralTerminalFrom sourceCertificate
              (Profile.update (sig := M.behavioralSignature) sourceProfile who alternative)
              history.1) (sourcePayoff who)))
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium sourceAntichain sourceCertificate
      sourcePayoff) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        targetCertificate targetPayoff ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          (fun history => (restriction.history history, fun who => sourcePayoff who history)) =
        (N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory).map
          (fun history => (history, fun who => targetPayoff who history)) :=
  restriction.sequentialEquilibrium_extends_of_continuation_unclocked sourceAntichain
    sourceCertificate targetCertificate reference referenceMixed decisionRecall sourcePayoff
    targetPayoff matching comparison source sourceEquilibrium

end GameTheoryExtensionsTests.PassageRestrictionExtension
