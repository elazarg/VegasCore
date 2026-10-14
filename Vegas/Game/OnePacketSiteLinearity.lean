/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSureCompletion

/-! # Completion values are affine in the installed law

Play until a stopping set reaches only histories that the start reaches
(`Vegas.historyReaches_of_mem_runBehavioralUntil`). From a history of a site
with a pending event, installing a law at the site draws a choice from it and
plays the corresponding commitment, and terminal play from any later stop no
longer reads the site's law. So the completion value from the history is the
law's average of the completion values of its choices
(`Vegas.historyStopValue_withLaw_eq_expect`), and so is the site's completion
value (`Vegas.siteStopValue_eq_expect`).

**One choice from a law that mostly plays it.** The site's value-blindness
error of a law is the law's average of the errors of its choices, each bounded
by twice the payoff bound. So a law giving a choice at least half its mass
bounds the error of that choice by twice its own error plus four times the
bound times the mass of the other choices
(`Vegas.abs_siteBlind_le_of_mass`).
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

open Classical in
/-- **The completion value from a history is affine in the installed law.**
From a history of a site with a pending event, the completion value of a law is
the law's average of the completion values of its choices. -/
theorem historyStopValue_withLaw_eq_expect
    (assessment : (onePacketN).BehavioralAssessment) (profile : BehavioralProfile setup.program)
    {who : Player} (site : (onePacketN).InformationSite who)
    (law : PMF ((onePacketN).Choice who site.1)) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (history : (onePacketN).InformationHistory who site.1) {bound : ℝ}
    (readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility excludedPayoff
      readout who| ≤ bound) (excludedBounded : |excludedPayoff who| ≤ bound) :
    historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site law history.1 =
      expect law fun choice => historyStopValue setup leaks bounds horizon scheduler parameter
        utility excludedPayoff assessment profile site (PMF.pure choice) history.1 := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketN
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let stopped := LateStopped setup leaks bounds horizon scheduler (siteRank site.1)
  have actsOnce := (menu.decisionRecall (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
  obtain ⟨control, current, ordered, _, _⟩ := pendingEvent_siteRank setup leaks bounds horizon
    scheduler pending history
  obtain ⟨past, view, atSite⟩ : ∃ past view, site.1 = some (past, view) := by
    cases info : site.1 with
    | none =>
        rw [info] at pending
        cases pending
    | some input => exact ⟨input.1, input.2, rfl⟩
  -- The site's history is a running decision of `who` that has not stopped.
  have observedState : (application setup leaks).observe who history.1.state = site.1 :=
    (menu.info (initialLaw setup) horizon scheduler who history.1.trace).symm.trans history.2
  rcases control with ⟨remaining, actor, execution⟩
  have actorEq : actor = some who := by
    by_contra different
    rw [current, atSite] at observedState
    simp only [ReactiveApplication.observe, different, ↓reduceIte] at observedState
    cases observedState
  subst actorEq
  have going : ¬ stopped history.1 := by
    rintro ⟨stopControl, state, prefixed⟩
    rw [current] at state
    cases Option.some.inj state
    exact Nat.succ_ne_self _ (isPrefix_unique prefixed ordered)
  have running : ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal
      history.1.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have active : (menu.protocol (initialLaw setup) horizon scheduler).active history.1.state
      who := by
    rw [current]
    rfl
  -- Terminal play after the site's step does not read the site's law.
  have after : ∀ (first second : PMF ((onePacketN).Choice who site.1)) (choice :
      (onePacketN).Choice who site.1),
      ∀ stop ∈ (model.runBehavioralUntil certificate
        (Profile.update (sig := model.behavioralSignature) assessment.strategy who
          ((assessment.strategy who).commit site.1 choice)) stopped history.1).support,
      model.runBehavioralTerminalFrom certificate
          (Profile.update (sig := model.behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 first)) stop =
        model.runBehavioralTerminalFrom certificate
          (Profile.update (sig := model.behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 second)) stop := by
    intro first second choice stop member
    rw [model.runBehavioralUntil_of_running certificate _ going running,
      PMF.mem_support_bind_iff] at member
    obtain ⟨next, nextMember, reached⟩ := member
    have reachesStop := historyReaches_of_mem_runBehavioralUntil model certificate _ stopped
      next stop reached
    rw [model.runBehavioralFrom_succ_of_not_terminal _ 0 running,
      PMF.mem_support_bind_iff] at nextMember
    obtain ⟨draw, _, stepped⟩ := nextMember
    rw [PMF.mem_support_bindOnSupport_iff] at stepped
    obtain ⟨target, realized, nextEq⟩ := stepped
    change next ∈ (PMF.pure _).support at nextEq
    rw [PMF.mem_support_pure_iff] at nextEq
    subst nextEq
    refine model.runBehavioralTerminalFrom_congr certificate stop fun later reaches nonterminal
      player => ?_
    by_cases same : player = who
    · subst same
      rw [Profile.update_same, Profile.update_same]
      obtain ⟨firstFuel, firstReach⟩ := reachesStop
      obtain ⟨secondFuel, secondReach⟩ := reaches
      have within := firstReach.trans secondReach
      rw [model.withLaw_eq_commit_after_actsOnce actsOnce _ site.1 first choice history.2 active
          draw.2 realized later within nonterminal,
        model.withLaw_eq_commit_after_actsOnce actsOnce _ site.1 second choice history.2 active
          draw.2 realized later within nonterminal]
    · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
  have pureRun : ∀ choice : (onePacketN).Choice who site.1,
      model.runBehavioralUntil certificate
          (Profile.update (sig := model.behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 (PMF.pure choice))) stopped history.1 =
        model.runBehavioralUntil certificate
          (Profile.update (sig := model.behavioralSignature) assessment.strategy who
            ((assessment.strategy who).commit site.1 choice)) stopped history.1 := by
    intro choice
    rw [model.runBehavioralUntil_update_withLaw_eq_bind certificate actsOnce _ who _ site.1 _
      stopped history.1 history.2 going running active, PMF.pure_bind]
  have bounded : ∀ (installedLaw : PMF ((onePacketN).Choice who site.1)) stop,
      |(if stopped stop then
          completionValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            profile (siteRank site.1) (siteFresh who site.1) who
            (fun later => expect (model.runBehavioralTerminalFrom certificate
              (Profile.update (sig := model.behavioralSignature) assessment.strategy who
                ((assessment.strategy who).withLaw site.1 installedLaw)) later)
              (fun final => if final ∈ onePacketFailed setup leaks bounds horizon scheduler
                  ((onePacketN).agentAt site) then 0
                else exclusionBase setup parameter utility excludedPayoff leaks final.state who))
            stop
        else if stop ∈ onePacketFailed setup leaks bounds horizon scheduler
            ((onePacketN).agentAt site) then 0
          else exclusionBase setup parameter utility excludedPayoff leaks stop.state who)| ≤
        bound := by
    intro installedLaw stop
    have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans excludedBounded
    have payoffBounded : ∀ final : ((bounds.onePacketMenu (runtime setup) leaks).protocol
        (initialLaw setup) horizon scheduler).History,
        |(if final ∈ onePacketFailed setup leaks bounds horizon scheduler
            ((onePacketN).agentAt site) then 0
          else exclusionBase setup parameter utility excludedPayoff leaks final.state who)| ≤
          bound := fun final => by
      split
      · rw [abs_zero]
        exact boundNonneg
      · rw [exclusionBase_eq_readout]
        exact readoutBounded _
    split
    · unfold completionValue
      split
      · exact expect_abs_le_of_bounded boundNonneg payoffBounded
      · split
        · exact expect_abs_le_of_bounded boundNonneg payoffBounded
        · split
          · exact expect_abs_le_of_bounded boundNonneg readoutBounded
          · exact expect_abs_le_of_bounded boundNonneg payoffBounded
    · exact payoffBounded stop
  unfold historyStopValue
  dsimp only
  rw [model.runBehavioralUntil_update_withLaw_eq_bind certificate actsOnce _ who _ site.1 law
      stopped history.1 history.2 going running active,
    expect_bind_tower_bounded _ _ _ (bounded law)]
  refine expect_congr_on_support fun choice _ => ?_
  rw [pureRun choice]
  refine expect_congr_on_support fun stop member => ?_
  split
  · unfold completionValue
    simp only [after law (PMF.pure choice) choice stop member]
    rfl
  · rfl

section Site

variable [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
    scheduler).History]

/-- **The site's completion value is affine in the installed law.** At a site
with a pending event, the completion value of a law is the law's average of the
completion values of its choices. -/
theorem siteStopValue_eq_expect (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {bound : ℝ}
    (readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility excludedPayoff
      readout who| ≤ bound) (excludedBounded : |excludedPayoff who| ≤ bound) :
    siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site law =
      expect law fun choice => siteStopValue setup leaks bounds horizon scheduler parameter
        utility excludedPayoff assessment profile site (PMF.pure choice) := by
  have : Finite ((onePacketN).Choice who site.1) :=
    (onePacketN).finite_choice_of_played ((onePacketN).site_mem_playedInformation site)
  unfold siteStopValue
  rw [expect_congr_on_support fun history _ => historyStopValue_withLaw_eq_expect setup leaks
    bounds horizon scheduler parameter utility excludedPayoff assessment profile site law pending
    history readoutBounded excludedBounded]
  exact expect_comm_of_support_finite _ _ (Set.toFinite _) (Set.toFinite _) _

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

omit [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
    scheduler).History] in
/-- **One choice from a law that mostly plays it.** At a site with a pending
event, the value-blindness error of a choice is at most twice that of a law
giving it at least half its mass, plus four times the payoff bound times the
mass the law gives the other choices. -/
theorem abs_siteBlind_le_of_mass
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {bound : ℝ}
    (readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility excludedPayoff
      readout who| ≤ bound) (excludedBounded : |excludedPayoff who| ≤ bound)
    (choice : (onePacketN).Choice who site.1) (half : 1 / 2 ≤ (law choice).toReal) :
    |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site (PMF.pure choice) -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site
          (PMF.pure choice)) *
        siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment profile site| ≤
      2 * |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment profile site law -
        (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law) *
          siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            assessment profile site| +
        4 * bound * (1 - (law choice).toReal) := by
  classical
  let := Fintype.ofFinite ((onePacketN).Choice who site.1)
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans excludedBounded
  let value := siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
    assessment profile site
  let blind := fun other : (onePacketN).Choice who site.1 =>
    siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site (PMF.pure other) -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site
        (PMF.pure other)) * value
  have valueBounded : |value| ≤ bound := by
    refine expect_abs_le_of_bounded boundNonneg fun history => ?_
    unfold decodedPointValue
    split
    · exact excludedBounded
    · split
      · exact excludedBounded
      · split
        · exact expect_abs_le_of_bounded boundNonneg readoutBounded
        · exact excludedBounded
  have blindBounded : ∀ other, |blind other| ≤ 2 * bound := fun other => by
    have stop : |siteStopValue setup leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment profile site (PMF.pure other)| ≤ bound :=
      expect_abs_le_of_bounded boundNonneg fun history => abs_historyStopValue_le setup leaks
        bounds horizon scheduler parameter utility excludedPayoff assessment profile site _
        history.1 readoutBounded excludedBounded
    have failureNonneg : 0 ≤ onePacketSiteFailure setup leaks bounds horizon scheduler
        assessment site (PMF.pure other) := localFailure_nonneg ..
    have failureLe : onePacketSiteFailure setup leaks bounds horizon scheduler assessment site
        (PMF.pure other) ≤ 1 := localFailure_le_one ..
    have scaled : |(1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment
        site (PMF.pure other)) * value| ≤ bound := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith)).trans valueBounded
    exact (abs_sub _ _).trans (by linarith)
  -- The law's error is the law's average of the errors of its choices.
  have average : siteStopValue setup leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment profile site law -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law) *
        value = ∑ other, (law other).toReal * blind other := by
    rw [siteStopValue_eq_expect setup leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment profile site law pending readoutBounded excludedBounded,
      onePacketSiteFailure_eq_expect setup leaks bounds horizon scheduler assessment site law,
      expect_eq_sum, expect_eq_sum]
    have total : ∑ other, (law other).toReal = 1 := by
      have := expect_constant law 1
      rw [expect_eq_sum] at this
      simpa using this
    have expand : ∑ other, (law other).toReal * blind other =
        ∑ other, (law other).toReal * siteStopValue setup leaks bounds horizon scheduler
          parameter utility excludedPayoff assessment profile site (PMF.pure other) -
          value * ∑ other, (law other).toReal +
          value * ∑ other, (law other).toReal * onePacketSiteFailure setup leaks bounds horizon
            scheduler assessment site (PMF.pure other) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun other _ => by simp only [blind]; ring
    rw [expand, total]
    ring
  have split := Finset.add_sum_erase Finset.univ (fun other => (law other).toReal * blind other)
    (Finset.mem_univ choice)
  have restLe : |∑ other ∈ Finset.univ.erase choice, (law other).toReal * blind other| ≤
      2 * bound * (1 - (law choice).toReal) := by
    have total : ∑ other ∈ Finset.univ.erase choice, (law other).toReal =
        1 - (law choice).toReal := by
      have whole := Finset.add_sum_erase Finset.univ (fun other => (law other).toReal)
        (Finset.mem_univ choice)
      have := expect_constant law 1
      rw [expect_eq_sum] at this
      simp only [mul_one] at this
      linarith
    calc _ ≤ ∑ other ∈ Finset.univ.erase choice, |(law other).toReal * blind other| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ other ∈ Finset.univ.erase choice, (law other).toReal * (2 * bound) :=
          Finset.sum_le_sum fun other _ => by
            rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
            exact mul_le_mul_of_nonneg_left (blindBounded other) ENNReal.toReal_nonneg
      _ = 2 * bound * (1 - (law choice).toReal) := by
          rw [← Finset.sum_mul, total]
          ring
  have chosen : (law choice).toReal * |blind choice| ≤
      |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment profile site law -
        (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site law) *
          value| + 2 * bound * (1 - (law choice).toReal) := by
    have alone : (law choice).toReal * blind choice =
        (∑ other, (law other).toReal * blind other) -
          ∑ other ∈ Finset.univ.erase choice, (law other).toReal * blind other := by
      rw [← split]
      ring
    have absEq : (law choice).toReal * |blind choice| =
        |(law choice).toReal * blind choice| := by
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [absEq, alone, average]
    exact (abs_sub _ _).trans (add_le_add le_rfl restLe)
  change |blind choice| ≤ _
  have blindNonneg := abs_nonneg (blind choice)
  have lawLe : (law choice).toReal ≤ 1 := by
    have := Finset.single_le_sum (f := fun other => (law other).toReal)
      (fun other _ => ENNReal.toReal_nonneg) (Finset.mem_univ choice)
    have total := expect_constant law 1
    rw [expect_eq_sum] at total
    simp only [mul_one] at total
    linarith
  nlinarith

end Site

end Vegas
