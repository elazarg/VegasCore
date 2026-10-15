/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNonmissingConditioning
import GameTheoryExtensions.Analysis.Protocol.ProportionalBeliefTransport

/-! # Actual auxiliary Bayes beliefs from chronological nonmissing kernels -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)

/-- A genuine clear owned source history supplies its complete decision
fiber. The actual auxiliary assessment's posterior equals the Bayes posterior
of chronological nonmissing sampling on that same fiber. Only past draws are
normalized; the next original auxiliary omission law is unchanged. -/
theorem commitRecovery_nonmissing_belief (n : Nat) (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (clear : current.excluded = ∅)
    (actor : ProtocolState.actor setup.program current.point = some who) :
    let info := setup.commitRecoveryClearInformation wellFormed who
      (setup.commitRecoveryPrivate who (some current))
    ∃ decision : setup.commitRecoveryModel.IsDecisionInfo who info,
      ∃ positive : 0 < setup.commitRecoveryModel.informationMass
        (setup.commitRecoveryNonmissingProfile (approximation.sequence n).strategy) who
          ⟨info, decision⟩,
        (approximation.sequence n).belief who ⟨info, decision⟩ =
          setup.commitRecoveryModel.bayesBelief
            (setup.commitRecoveryNonmissingProfile (approximation.sequence n).strategy) who
            ⟨info, decision⟩ (setup.commitRecoveryModel_decisionAntichain who ⟨info, decision⟩)
            positive := by
  classical
  intro info
  have observed := setup.commitRecoveryClearInformation_observed wellFormed who trace clear
  have decision := Vegas.commitRecovery_isDecisionInfo_of_actor setup current trace who clear actor
  rw [observed] at decision
  refine ⟨decision, ?_⟩
  let site : setup.commitRecoveryModel.InformationSite who := ⟨info, decision⟩
  let raw := (approximation.sequence n).strategy
  let conditioned := setup.commitRecoveryNonmissingProfile raw
  let scale := ENNReal.ofReal (setup.commitRecoveryNonmissingFactor raw trace)
  let reference : setup.commitRecoveryModel.InformationHistory who info :=
    ⟨⟨some current, trace⟩, observed⟩
  have fiber (history : setup.commitRecoveryModel.InformationHistory who info) :
      scale * setup.commitRecoveryModel.historyReachWeight conditioned history.1 =
        ∑' original : setup.commitRecoveryModel.InformationHistory who info,
          if id original.1 = history.1 then
            setup.commitRecoveryModel.historyReachWeight raw original.1 else 0 := by
    have length := (setup.commitRecovery_clearInformation_fiber_length wellFormed who
      (setup.commitRecoveryPrivate who (some current)) reference history).symm
    have historyClear := setup.commitRecovery_clearInformation_fiber_clear wellFormed who
      (setup.commitRecoveryPrivate who (some current)) history
    have density := setup.commitRecovery_clear_prefix_mass_factorization finite wellFormed target
      approximation n trace clear history.1 historyClear
    change history.1.trace.length = trace.length at length
    change setup.commitRecoveryModel.runBehavioral raw trace.length history.1 =
      scale * setup.commitRecoveryModel.runBehavioral conditioned trace.length history.1 at density
    rw [show (∑' original : setup.commitRecoveryModel.InformationHistory who info,
        if id original.1 = history.1 then
          setup.commitRecoveryModel.historyReachWeight raw original.1 else 0) =
        setup.commitRecoveryModel.historyReachWeight raw history.1 by
      have equal (original : setup.commitRecoveryModel.InformationHistory who info) :
          id original.1 = history.1 ↔ original = history := Subtype.val_injective.eq_iff
      simp only [equal, tsum_ite_eq]]
    change scale * setup.commitRecoveryModel.runBehavioral conditioned history.1.trace.length
      history.1 = setup.commitRecoveryModel.runBehavioral raw history.1.trace.length history.1
    rw [length]
    exact density.symm
  have maps (history : setup.commitRecoveryProtocol.History)
      (same : setup.commitRecoveryModel.infoOf who history.trace = site.1) :
      setup.commitRecoveryModel.infoOf who (id history).trace = site.1 := same
  have mass := setup.commitRecoveryModel.informationMass_projection_of_proportional_reach
    setup.commitRecoveryModel raw conditioned id who site site maps scale fiber
  have rawPositive := setup.commitRecoveryModel.informationMass_pos_of_fullSupport raw
    (approximation.mixed n) who site
  have positive : 0 < setup.commitRecoveryModel.informationMass conditioned who site := by
    apply pos_iff_ne_zero.mpr
    intro zero
    rw [zero, mul_zero] at mass
    exact rawPositive.ne' mass
  refine ⟨positive, ?_⟩
  have scalePositive : scale ≠ 0 := (ENNReal.ofReal_pos.mpr
    (setup.commitRecovery_nonmissingFactor_pos (approximation.sequence n)
      (approximation.mixed n) trace)).ne'
  have transported := setup.commitRecoveryModel.bayesBelief_projection_of_proportional_reach
    setup.commitRecoveryModel raw conditioned id who site site maps scale fiber scalePositive
    ENNReal.ofReal_ne_top (setup.commitRecoveryModel_decisionAntichain who site)
    (setup.commitRecoveryModel_decisionAntichain who site) positive
  change (setup.commitRecoveryModel.bayesBelief raw who site
    (setup.commitRecoveryModel_decisionAntichain who site) _).map id = _ at transported
  rw [PMF.map_id] at transported
  have belief := (GameTheory.Protocol.InformationModel.BehavioralAssessment.isBayesConsistentAt_iff
    setup.commitRecoveryModel (approximation.sequence n) who site
      (setup.commitRecoveryModel_decisionAntichain who site) rawPositive).mp
        (approximation.bayes n who site rawPositive)
  exact belief.trans transported

end Vegas.SourceProgram.Setup
