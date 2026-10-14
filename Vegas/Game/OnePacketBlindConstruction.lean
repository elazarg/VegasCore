/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCertificateAssembly
import Vegas.Game.OnePacketNonLateValueBlind

/-! # Constructing value-blind one-packet certificates

The base certificate supplies honest counterparts and common replay fibers.
Those inputs imply vanishing unforced mass and record/value decorrelation at
pending decisions away from late delivery. The asynchronous service contract
then supplies the non-late value-blindness field of the preservation certificate.
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

omit [Finite setup.intendedProtocol.History] in
open Classical in
/-- At pending decisions away from late delivery, the base inputs make the
posterior mass outside the forced region vanish uniformly. -/
theorem OnePacketBaseInputs.nonLateUnforced
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots)
    (wellFormed : setup.WellFormed)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) :
    ∃ drift : ℕ → ℝ, Tendsto drift atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        pendingEvent setup leaks who site.1 ≠ none →
        expect ((targetSequence n).belief who site) (fun history =>
          if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ drift n := by
  obtain ⟨drift, limit, holds⟩ := exists_uniform_of_sites setup leaks bounds horizon scheduler
    (fun n who site error => expect ((targetSequence n).belief who site) (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ error)
    (fun _ _ _ _ _ le bound => bound.trans le)
    (fun who site => ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) ∧ pendingEvent setup leaks who site.1 ≠ none)
    (fun who site ⟨notFree, notOwing, notKeyed, pendingSome⟩ => by
      obtain ⟨event, pending⟩ := Option.ne_none_iff_exists'.mp pendingSome
      obtain ⟨past, view, _, atSite, pendingAt, _⟩ := firstActivation_of_nonLate setup leaks
        bounds horizon scheduler site notFree notKeyed pending
      have forced := forcedAgent_of_not_free setup leaks bounds horizon scheduler notFree
      have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing
      rw [atSite] at pendingAt
      have turn := (pendingEvent_spec (setup := setup) pendingAt).1
      have decision := projectedDecision_of_forcedAgent wellFormed forced atSite turn debtFree
      exact ⟨_, onePacket_unforcedVanishes setup leaks bounds horizon scheduler wellFormed mixed
        bayes atSite forced
        (inputs.counterpartInputs weights targetSequence assembled mixed bayes who site notFree
          notOwing atSite turn)
        (inputs.ownInputs weights targetSequence assembled mixed bayes who site notFree notOwing
          atSite turn decision).ownIntended, fun _ => le_rfl⟩)
  exact ⟨drift, limit, fun n who site notFree notOwing notKeyed pendingSome =>
    holds n who site ⟨notFree, notOwing, notKeyed, pendingSome⟩⟩

open Classical in
/-- At pending decisions away from late delivery, the base inputs make
operational records and decoded states decorrelate uniformly. -/
theorem OnePacketBaseInputs.nonLateDecorrelated
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
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        pendingEvent setup leaks who site.1 ≠ none →
        BeliefDecorrelated ((targetSequence n).belief who site)
          (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
          (fun history => nativeDecodedState setup leaks history.1.state) (error n) := by
  obtain ⟨error, limit, holds⟩ := exists_uniform_decorrelation setup leaks bounds horizon scheduler
    targetSequence
    (fun who site => ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site) ∧ pendingEvent setup leaks who site.1 ≠ none)
    (fun who site ⟨notFree, notOwing, notKeyed, pendingSome⟩ => by
      obtain ⟨event, pending⟩ := Option.ne_none_iff_exists'.mp pendingSome
      obtain ⟨past, view, _, atSite, pendingAt, _⟩ := firstActivation_of_nonLate setup leaks
        bounds horizon scheduler site notFree notKeyed pending
      have forced := forcedAgent_of_not_free setup leaks bounds horizon scheduler notFree
      have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing
      rw [atSite] at pendingAt
      have turn := (pendingEvent_spec (setup := setup) pendingAt).1
      have decision := projectedDecision_of_forcedAgent wellFormed forced atSite turn debtFree
      exact OnePacketBeliefInputs.tendsto_decorrelated wellFormed sourceMixed mixed bayes atSite
        rfl forced turn (bindingFieldsCovered_of_covers inputs.covers inputs.coversInputs)
        (inputs.beliefInputs setup leaks bounds horizon scheduler weights targetSequence assembled
          mixed bayes who site notFree notOwing atSite turn decision))
  exact ⟨error, limit, fun n who site notFree notOwing notKeyed pendingSome =>
    holds n who site ⟨notFree, notOwing, notKeyed, pendingSome⟩⟩

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- Complete the value-blind certificate from its base inputs, bounded utilities,
and protected timely service of covered canonical packets. -/
def OnePacketBaseInputs.toBlindInputs
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    {lowerUtility upperUtility : Player → ℝ}
    (inputs : OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots)
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (gap_le : ∀ who, upperUtility who - excludedPayoff who ≤ inputs.gapBound)
    (slotsCover : bounds.candidateCount ≤ slots) :
    OnePacketBlindInputs setup leaks bounds horizon scheduler parameter utility excludedPayoff
      upperUtility sequence slots where
  toOnePacketBaseInputs := inputs
  gap_le := gap_le
  slotsCover := slotsCover
  nonLateValueBlind := by
    intro weights targetSequence assembled mixed bayes
    obtain ⟨readoutBounded, excludedBounded⟩ := exclusionPayoffs_bounded setup parameter utility
      excludedPayoff lowerUtility upperUtility lower_le le_upper
    obtain ⟨unforcedDrift, unforcedLimit, unforced⟩ := inputs.nonLateUnforced setup leaks bounds
      horizon scheduler wellFormed weights targetSequence assembled mixed bayes
    obtain ⟨decorrelation, decorrelationLimit, decorrelated⟩ := inputs.nonLateDecorrelated setup
      leaks bounds horizon scheduler wellFormed sourceMixed weights targetSequence assembled mixed
      bayes
    classical
    by_cases players : Nonempty Player
    swap
    · exact ⟨fun _ => 0, tendsto_const_nhds, fun n who => (players ⟨who⟩).elim⟩
    obtain ⟨somebody⟩ := players
    exact nonLateValueBlind_of_bounds setup leaks bounds horizon scheduler parameter utility
      excludedPayoff wellFormed contract timely retains sequence inputs.scale inputs.scale_pos
      inputs.scale_le_one inputs.scale_vanishing weights targetSequence assembled inputs.covers
      (inputs.one_le_candidateCount setup leaks bounds horizon scheduler somebody) inputs.slotsLe
      unforcedDrift decorrelation unforcedLimit decorrelationLimit unforced decorrelated
      readoutBounded excludedBounded

end Vegas
