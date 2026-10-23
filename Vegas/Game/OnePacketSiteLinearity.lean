/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateDecomposition
import Vegas.Game.OnePacketNextEvent
import Vegas.Game.OnePacketCompletionLaw
import Vegas.Game.OnePacketLateCompletion

/-! # Site failure is affine in the installed law

Play until a stopping set reaches only histories that the start reaches
(`Vegas.historyReaches_of_mem_runBehavioralUntil`). From a history of a site
with a pending event, installing a law at the site draws a choice from it and
plays the corresponding commitment, so the site's failure is affine in the
installed law (`Vegas.onePacketSiteFailure_eq_expect`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

section Reach

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)

/-- **Play until a stopping set stays in the start's cone.** Every history play
until a stopping set ends at is reached from the start. -/
theorem historyReaches_of_mem_runBehavioralUntil (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) (stopped : E.History → Prop)
    (start : E.History) :
    ∀ stop ∈ (M.runBehavioralUntil certificate policies stopped start).support,
      E.HistoryReaches start stop := by
  classical
  induction start using certificate.induction with
  | _ history ih =>
  intro stop member
  by_cases halt : stopped history
  · rw [M.runBehavioralUntil_of_stopped certificate policies halt,
      PMF.mem_support_pure_iff] at member
    subst member
    exact HistoryReaches.refl E _
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralUntil_of_terminal certificate policies ended,
      PMF.mem_support_pure_iff] at member
    subst member
    exact HistoryReaches.refl E _
  rw [M.runBehavioralUntil_of_running certificate policies halt ended,
    PMF.mem_support_bind_iff] at member
  obtain ⟨next, nextMember, reached⟩ := member
  obtain ⟨successor, reaches⟩ := M.mem_support_runBehavioralFrom_one policies ended nextMember
  exact reaches stop (ih next successor stop reached)

end Reach

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

section Site

variable [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
    scheduler).History]

/-- **The site's failure is affine in the installed law.** -/
theorem onePacketSiteFailure_eq_expect (assessment : (onePacketN).BehavioralAssessment)
    {who : Player} (site : (onePacketN).InformationSite who)
    (law : PMF ((onePacketN).Choice who site.1)) :
    onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law =
      expect law fun choice => onePacketSiteFailure setup leaks bounds horizon scheduler
        assessment site (PMF.pure choice) := by
  have : Finite ((onePacketN).Choice who site.1) :=
    (onePacketN).finite_choice_of_played ((onePacketN).site_mem_playedInformation site)
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have mixed := localFailure_bind (2 * horizon + 1) assessment site
    (menu.bounded (initialLaw setup) horizon scheduler)
    (menu.decisionRecall (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
    (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) law
    PMF.pure
  rw [PMF.bind_pure] at mixed
  exact mixed

end Site

end Vegas
