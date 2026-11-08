/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForcedRegular
import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Game.IntendedAuthenticOpening

/-! # Regular histories owe nothing

At a forced site, a regular history along which the owner's own completions are
intended decodes to a point at which no player owes a failure
(`Vegas.not_owesFailure_of_regular`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "onePacketN" =>
  onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler

/-- **Regular histories owe nothing.** For a well-formed setup, at a forced
decision site of who, a regular history along which who's own completions decode
to intended actions decodes to a point at which no player owes a failure. -/
theorem not_owesFailure_of_regular (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    {site : (onePacketN).InformationSite who} {past : List (application setup timeouts
      leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler who site.1)
    (history : (onePacketN).InformationHistory who site.1)
    (regular : RegularTrace setup timeouts leaks bounds horizon scheduler assessment who
      history.1.trace)
    (ownIntended : OwnCompletionsIntended (timeouts := timeouts) (bounds := bounds) (horizon :=
      horizon)
      (scheduler := scheduler) who history.1.trace) :
    ∀ point, nativeDecodedState setup timeouts leaks history.1.state = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
  intro point decodedState player
  have forcedState := forcedState_of_regular (timeouts := timeouts) wellFormed assessment atSite
    forced history regular
    ownIntended
  cases state : history.1.state with
  | none =>
      rw [state] at decodedState
      cases decodedState
  | some control =>
      rw [state] at forcedState decodedState
      have record := publicRecord_of_forced (timeouts := timeouts) who control forcedState
      obtain ⟨found, foundDecoded, intendedFound⟩ := intended_of_regular (timeouts := timeouts)
        wellFormed assessment who
        history.1.trace control state record regular ownIntended
      change decodedPoint setup control.execution.application.config = some point at decodedState
      rw [foundDecoded, Option.some.injEq] at decodedState
      subst decodedState
      exact ProtocolState.Intended.not_owesFailure player setup.program found intendedFound

section ContinuationBounds

variable (setup) {Parameter : Type} (parameter : State L setup.context → Parameter)
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
    · exact ⟨le_rfl, le_max_left _ _⟩
    · exact ⟨below point reachedPoint terminal member,
        (le_upper _).trans (le_max_right _ _)⟩
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

omit [Fintype Player] in
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

end ContinuationBounds

end Vegas
