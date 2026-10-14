/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCertificateDischarge

/-! # Sites whose pending event fails surely

**No success where failure is sure.** A law whose event-level failure at a site
is one has no successful part: the local run is supported on failed histories,
on which the successful part is zero (`Vegas.onePacketSiteSuccess_eq_zero`).

**Transmit or fail surely.** Under the asynchronous contract, at a forced
first activation of `who` with a pending event, either the canonical decisions
transmit, or every choice under every assessment fails the event surely and has
no successful part (`Vegas.firstActivation_transmits_or_doomed`). The second
branch is a disclosure whose resolution of an opening already publishes a
failure; there the site's failure set is the event-level failure of the pending
event (`Vegas.onePacketFailed_of_pending`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- At an information state with `event` pending, the failure set of the agent
is the event-level failure of `event`. -/
theorem onePacketFailed_of_pending {who : Player}
    {info : (onePacketN).InfoState who} (played : info ∈ (onePacketN).playedInformation who)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who info = some event) :
    onePacketFailed setup leaks bounds horizon scheduler ⟨who, info, played⟩ =
      EventFailedHistory setup leaks bounds horizon scheduler who event := by
  unfold onePacketFailed
  change (match pendingEvent setup leaks who info with
    | none => ∅
    | some event => EventFailedHistory setup leaks bounds horizon scheduler who event) = _
  rw [pending]

/-- **No success where failure is sure.** A law whose event-level failure at a
site is one has successful part zero. -/
theorem onePacketSiteSuccess_eq_zero (assessment : (onePacketN).BehavioralAssessment)
    {who : Player} (site : (onePacketN).InformationSite who)
    (law : PMF ((onePacketN).Choice who site.1))
    (sure : onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law = 1) :
    onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility excludedPayoff
      assessment site law = 0 := by
  classical
  unfold onePacketSiteFailure localFailure at sure
  rw [expect_indicator, ENNReal.toReal_eq_one_iff, PMF.toOuterMeasure_apply_eq_one_iff] at sure
  unfold onePacketSiteSuccess localSuccessValue
  rw [expect_congr_on_support (g := fun _ => 0) fun history member => by
    simp only [sure member, ↓reduceIte]]
  exact expect_constant _ 0

/-- **Transmit or fail surely.** Under the asynchronous contract, at a forced
first activation of `who` with `event` pending, either the canonical decisions
transmit, or every choice under every assessment fails `event` surely and has
no successful part. -/
theorem firstActivation_transmits_or_doomed
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon scheduler who (some (past, view)))
    (pending : pendingEvent setup leaks who (some (past, view)) = some event)
    (first : ∀ entry ∈ past, ¬ ActivatedAt setup leaks who event entry) :
    CanonicalTransmitsAt setup leaks who past view event ∨
      ∀ (assessment : (onePacketN).BehavioralAssessment)
        (decision : (onePacketN).IsDecisionInfo who (some (past, view)))
        (choice : (onePacketN).Choice who (some (past, view))),
        onePacketSiteFailure setup leaks bounds horizon scheduler assessment
            ⟨some (past, view), decision⟩ (PMF.pure choice) = 1 ∧
          onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
            excludedPayoff assessment ⟨some (past, view), decision⟩ (PMF.pure choice) = 0 := by
  rcases firstActivationTransmits_of_contract setup leaks bounds horizon scheduler contract who
    past view event forced pending first with transmits | doomed
  · exact Or.inl transmits
  · refine Or.inr fun assessment decision choice => ?_
    have failure : onePacketSiteFailure setup leaks bounds horizon scheduler assessment
        ⟨some (past, view), decision⟩ (PMF.pure choice) = 1 := by
      unfold onePacketSiteFailure
      erw [onePacketFailed_of_pending setup leaks bounds horizon scheduler _ pending]
      exact doomed assessment decision choice
    exact ⟨failure, onePacketSiteSuccess_eq_zero setup leaks bounds horizon scheduler parameter
      utility excludedPayoff assessment _ _ failure⟩

end Vegas
