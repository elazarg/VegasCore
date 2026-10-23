/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateCommitBlind
import Vegas.Game.OnePacketSwapDecorrelationLimit

/-! # Uniform decorrelation at late deliveries

At a forced own-turn site with the forced-belief inputs, the beliefs decorrelate
the operational records and the decoded points up to a vanishing error
(`Vegas.OnePacketBeliefInputs.tendsto_decorrelated`). So, for the base inputs of
the one-packet certificate, one vanishing error serves every late delivery of an
agent that is neither free nor owing (`Vegas.OnePacketBaseInputs.lateDecorrelated`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

variable {setup leaks bounds horizon scheduler} in
omit [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
open Classical in
/-- **Vanishing decorrelation at a forced own-turn site.** At a forced site of
`who` at its own turn whose projected view is an intended site, along a fully
mixed source sequence and a fully mixed Bayes target sequence with the
forced-belief inputs, the beliefs decorrelate the operational records and the
decoded points up to a vanishing error. -/
theorem OnePacketBeliefInputs.tendsto_decorrelated (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {who : Player} {site : (onePacketN).InformationSite who}
    {sourceSite : setup.intendedModel.InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1)
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who site.1)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (covered : BindingFieldsCovered bounds)
    (inputs : OnePacketBeliefInputs setup leaks bounds horizon scheduler sequence targetSequence
      site sourceSite decision projected) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧ ∀ n,
      BeliefDecorrelated ((targetSequence n).belief who site)
        (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
        (fun history => nativeDecodedState setup leaks history.1.state) (error n) := by
  let := Fintype.ofFinite (setup.intendedModel.InformationHistory who sourceSite.1)
  exact tendsto_beliefDecorrelated wellFormed decision projected
    (fun n => ForcedBeliefInputs.ofRegularHistories (n := n) wellFormed forced decision turn
      projected (sourceMixed n) (inputs.ownIntended n) (inputs.fiberMass n) (inputs.fiber n)
      (inputs.counterpart n) (inputs.commonWeight n) (inputs.counterpart_regular n)
      (inputs.irregular_le n) (inputs.counterpart_ge n))
    inputs.ownIntended sourceMixed turn covered (fun _ => rfl) mixed bayes inputs.floors_pos
    inputs.scale_nonneg inputs.negligible inputs.slack_nonneg

open Classical in
/-- **Decorrelation vanishes uniformly at late deliveries.** For a well-formed
setup, along a fully mixed source sequence and every fully mixed Bayes sequence
of assembled profiles, one vanishing error bounds the decorrelation of the
operational records and the decoded points at every late delivery of an agent
that is neither free nor owing. -/
theorem OnePacketBaseInputs.lateDecorrelated
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots)
    (wellFormed : setup.WellFormed) (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) :
    ∃ decorrelation : ℕ → ℝ, Tendsto decorrelation atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        BeliefDecorrelated ((targetSequence n).belief who site)
          (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
          (fun history => nativeDecodedState setup leaks history.1.state) (decorrelation n) := by
  obtain ⟨decorrelation, limit, holds⟩ := exists_uniform_decorrelation setup leaks bounds
    horizon scheduler targetSequence
    (fun who site => ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site))
    (fun who site ⟨notFree, notOwing, keyed⟩ => by
      obtain ⟨input, atSite, event, turn⟩ := lateDelivery_input setup leaks keyed.1
      have forced := forcedAgent_of_not_free setup leaks bounds horizon scheduler notFree
      have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing
      have decision := projectedDecision_of_forcedAgent wellFormed forced atSite turn debtFree
      exact OnePacketBeliefInputs.tendsto_decorrelated wellFormed sourceMixed mixed bayes atSite
        rfl forced turn (bindingFieldsCovered_of_covers inputs.covers inputs.coversInputs)
        (inputs.beliefInputs setup leaks bounds horizon scheduler weights targetSequence
          assembled mixed bayes who site notFree notOwing atSite turn decision))
  exact ⟨decorrelation, limit, fun n who site notFree notOwing keyed =>
    holds n who site ⟨notFree, notOwing, keyed⟩⟩

end Vegas
