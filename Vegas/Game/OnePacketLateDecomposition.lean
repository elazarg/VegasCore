/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateSuccess
import Vegas.Game.OnePacketValueTransport
import Vegas.Game.OnePacketIntendedProjection

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
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler

/-- **The failure set of an agent of the one-packet game**: the event-level
failed histories of its pending event, and none without one. -/
def onePacketFailed (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    Set ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History :=
  match pendingEvent setup timeouts leaks agent.1 agent.2.1 with
  | none => ∅
  | some event => EventFailedHistory setup leaks timeouts bounds horizon scheduler agent.1 event

section Values

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- **The value at a site history.** The source continuation value of `profile`
at the point the history's configuration decodes to after `rank` events, when
that point is a point of the intended game; the exclusion payoff otherwise. -/
def decodedPointValue (profile : BehavioralProfile setup.program) (who : Player) (rank : Nat)
    (history : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
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
    decodedPointValue setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff
      profile who (siteRank (timeouts := timeouts) site.1) history.1

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
    (history : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History) : ℝ :=
  let menu := bounds.onePacketMenu timeouts leaks
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let installed := Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy
    who ((assessment.strategy who).withLaw site.1 law)
  let payoff := fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    if final ∈ onePacketFailed setup timeouts leaks bounds horizon scheduler ((onePacketN).agentAt
      site)
    then 0 else exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who
  expect ((onePacketN).runBehavioralUntil certificate installed
      (LateStopped setup timeouts leaks bounds horizon scheduler (siteRank (timeouts := timeouts)
        site.1)) history)
    (fun stop => if LateStopped setup timeouts leaks bounds horizon scheduler (siteRank (timeouts :=
      timeouts) site.1) stop then
      completionValue setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff
        profile (siteRank (timeouts := timeouts) site.1) (siteFresh (timeouts := timeouts) who
          site.1)
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
    historyStopValue setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff
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

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
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
    excludedPayoff who ≤ siteValue setup timeouts leaks bounds horizon scheduler parameter utility
        excludedPayoff assessment profile site ∧
      siteValue setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff
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


end Bounds

end Vegas
