/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateSuccess
import Vegas.Game.OnePacketCertificateDischarge

/-! # Site values at forced sites

**The rank of a site.** A site's information records the public completion
order, so every history of a site has completed the same number of events, the
site's rank (`Vegas.siteRank`).

**The completion value.** The belief average of the value at the first
completion of the event of the site's rank: the source continuation value of
the intended effective opening at the decoded point when that point is
intended and the site's pending event, if any, did not fail
(`Vegas.siteStopValue`).

**The continuation value.** The continuation value of a site is the belief
average, over its histories, of the source continuation value of a profile at
the decoded point of the site's rank, at points the intended game reaches, and
the exclusion payoff elsewhere (`Vegas.siteValue`). It lies between the
exclusion payoff and the upper utility whenever exclusion is a punishment at
every terminal state the profile's continuation reaches from such a point
(`Vegas.siteValue_mem_Icc`). For the intended effective opening this holds
when exclusion is a punishment at every terminal readout of the intended game
(`Vegas.excludedPayoff_le_of_reached`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

variable {setup runtime leaks} in
/-- **The rank of a site**: the number of events its public completion order
records. -/
def siteRank : (application setup runtime leaks).Info → Nat
  | none => 0
  | some (_, view) => view.application.publicView.observation.completionOrder.length

/-- A source point at which some history of the intended game ends. -/
def IntendedReached (point : ProtocolState setup.program) : Prop :=
  ∃ history : setup.intendedProtocol.History, history.state = some point

section Values

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- **The value at a site history.** The source continuation value of `profile`
at the point the history's configuration decodes to after `rank` events, when
that point is a point of the intended game; the exclusion payoff otherwise. -/
def decodedPointValue (profile : BehavioralProfile setup.program) (who : Player) (rank : Nat)
    (history : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History) : ℝ :=
  match history.state with
  | none => excludedPayoff who
  | some control =>
      match sourceServicePrefix? setup rank control.execution.application.config with
      | none => excludedPayoff who
      | some point =>
          if IntendedReached setup point then
            sourcePointValue setup parameter utility excludedPayoff profile who point
          else excludedPayoff who

/-- **The continuation value of a site.** The belief average, over the histories
of a site, of the source continuation value of `profile` at their decoded point
of the site's rank. -/
def siteValue (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) : ℝ :=
  expect (assessment.belief who site) fun history =>
    decodedPointValue setup runtime leaks bounds horizon scheduler parameter utility excludedPayoff
      profile who (siteRank (runtime := runtime) site.1) history.1

variable {setup runtime leaks} in
/-- The site's pending event, if any, has not failed. -/
def siteFresh (who : Player) (info : (application setup runtime leaks).Info)
    (control : (application setup runtime leaks).Control) : Prop :=
  match pendingEvent setup runtime leaks who info with
  | some event => ¬ StoreEventFailed control.execution.application.config.store event
  | none => True

open Classical in
/-- **The completion value from a history.** The expected completion value under
play from a history, with `law` installed at the site, until the event of the
site's rank completes: the source continuation value of `profile` at the
decoded point after that event, when the intended game reaches it and the
site's pending event did not fail, and the expected payoff of `who` off the
site's failure set otherwise. -/
def historyStopValue (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    (history : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History) : ℝ :=
  let menu := bounds.onePacketMenu runtime leaks
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let installed := Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy
    who ((assessment.strategy who).withLaw site.1 law)
  let payoff := fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    if final ∈ onePacketFailed setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt
      site)
    then 0 else exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
  expect ((onePacketN).runBehavioralUntil certificate installed
      (LateStopped setup runtime leaks bounds horizon scheduler (siteRank (runtime := runtime)
        site.1)) history)
    (fun stop => if LateStopped setup runtime leaks bounds horizon scheduler (siteRank (runtime :=
      runtime) site.1) stop then
      completionValue setup runtime leaks bounds horizon scheduler parameter utility excludedPayoff
        profile (siteRank (runtime := runtime) site.1) (siteFresh (runtime := runtime) who site.1)
          who
        (fun later => expect ((onePacketN).runBehavioralTerminalFrom certificate installed later)
          payoff) stop
      else payoff stop)

/-- **The completion value of a site.** The belief average, over the histories
of a site, of their completion values (`Vegas.historyStopValue`). -/
def siteStopValue (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) :
    ℝ :=
  expect (assessment.belief who site) fun history =>
    historyStopValue setup runtime leaks bounds horizon scheduler parameter utility excludedPayoff
      assessment profile site law history.1

end Values

section Bounds

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- An expectation of a payoff within `[low, high]` on the support lies in
`[low, high]`. -/
private theorem expect_mem_Icc {α : Type*} (law : PMF α) (payoff : α → ℝ) {low high : ℝ}
    (within : ∀ point, low ≤ payoff point ∧ payoff point ≤ high) :
    low ≤ expect law payoff ∧ expect law payoff ≤ high := by
  have integrable : PayoffIntegrable law payoff :=
    payoffIntegrable_of_bounded law payoff (C := |low| + |high|) fun point => by
      have := within point
      rw [abs_le]
      constructor <;> cases abs_cases low <;> cases abs_cases high <;> linarith
  refine ⟨?_, expect_le_const law payoff integrable high fun point _ => (within point).2⟩
  have lower := expect_mono (μ := law) (f := fun _ => low) (g := payoff)
    (fun point _ => (within point).1) (payoffIntegrable_constant law low) integrable
  rwa [expect_constant] at lower

omit [Fintype Player] in
/-- **The source continuation value is between the exclusion payoff and the
upper utility.** If the exclusion payoff of `who` is at most its utility at
every terminal state the continuation of `profile` from a point of the intended
game reaches, and the utility is at most `upper`, the source continuation value
of `profile` at every point of the intended game lies in
`[excludedPayoff who, max (excludedPayoff who) upper]`. -/
theorem sourcePointValue_mem_Icc (profile : BehavioralProfile setup.program) (who : Player)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome who ≤ upper)
    (below : ∀ point, IntendedReached setup point →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support,
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (point : ProtocolState setup.program)
    (reachedPoint : IntendedReached setup point) :
    excludedPayoff who ≤ sourcePointValue setup parameter utility excludedPayoff profile who point ∧
      sourcePointValue setup parameter utility excludedPayoff profile who point ≤
        max (excludedPayoff who) upper := by
  classical
  unfold sourcePointValue
  rw [expect_map]
  have within : ∀ terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support,
      excludedPayoff who ≤ exclusionReadoutUtility setup parameter utility excludedPayoff
        (some terminal) who ∧
      exclusionReadoutUtility setup parameter utility excludedPayoff (some terminal) who ≤
        max (excludedPayoff who) upper := by
    intro terminal member
    change excludedPayoff who ≤ exclusionUtility setup.program excludedPayoff utility
        (setup.parameterOutcome parameter terminal) who ∧
      exclusionUtility setup.program excludedPayoff utility
        (setup.parameterOutcome parameter terminal) who ≤ max (excludedPayoff who) upper
    unfold exclusionUtility
    split
    · exact ⟨below point reachedPoint terminal member,
        (le_upper _).trans (le_max_right _ _)⟩
    · exact ⟨le_rfl, le_max_left _ _⟩
  rw [expect_congr_on_support (g := fun terminal =>
    if terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support then
      exclusionReadoutUtility setup parameter utility excludedPayoff (some terminal) who
    else excludedPayoff who) (fun terminal member => by rw [ite_eq_left member ..]; rfl)]
  apply expect_mem_Icc
  intro terminal
  split
  · rename_i member
    exact within terminal member
  · exact ⟨le_rfl, le_max_left _ _⟩

omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The continuation value of a site is between the exclusion payoff and the
upper utility.** Under the hypotheses of `Vegas.sourcePointValue_mem_Icc` for
`profile`, the continuation value of a site lies in
`[excludedPayoff who, max (excludedPayoff who) upper]`. -/
theorem siteValue_mem_Icc (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome who ≤ upper)
    (below : ∀ point, IntendedReached setup point →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program profile point).support,
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who) :
    excludedPayoff who ≤ siteValue setup runtime leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment profile site ∧
      siteValue setup runtime leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site ≤ max (excludedPayoff who) upper := by
  apply expect_mem_Icc
  intro history
  unfold decodedPointValue
  split
  · exact ⟨le_rfl, le_max_left _ _⟩
  · split
    · exact ⟨le_rfl, le_max_left _ _⟩
    · split
      · rename_i reachedPoint
        exact sourcePointValue_mem_Icc setup parameter utility excludedPayoff profile who upper
          le_upper below _ reachedPoint
      · exact ⟨le_rfl, le_max_left _ _⟩

omit [Fintype Player] [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Exclusion is a punishment on reached continuations.** If the exclusion
payoff of every player is at most its utility at every terminal readout of the
intended game, it is at most its utility at every terminal state the
continuation of the intended effective opening of an intended profile reaches
from a point the intended game reaches. -/
theorem excludedPayoff_le_of_reached [Finite Player] (wellFormed : setup.WellFormed)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (point : ProtocolState setup.program) (reachedPoint : IntendedReached setup point)
    (who : Player) :
    ∀ terminal ∈ (ProtocolState.continuationLaw setup.program
        (setup.intendedOpeningProfile intended) point).support,
      excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who := by
  have := Fintype.ofFinite Player
  obtain ⟨history, state⟩ := reachedPoint
  intro terminal member
  have law := setup.intendedOpeningProfile_runFrom wellFormed intended
    (setup.protocolRemaining history.state) history le_rfl
  have readout : some terminal ∈ ((setup.continuationLaw (setup.intendedOpeningProfile intended)
      history.state).map some).support := by
    rw [state]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨terminal, member, rfl⟩
  rw [← law] at readout
  obtain ⟨final, _, read⟩ := (PMF.mem_support_map_iff _ _ _).mp readout
  exact below final terminal read who

end Bounds

end Vegas
