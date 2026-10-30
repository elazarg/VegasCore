/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Pending.ReactiveGraphSteps

/-! # Fixed native exit utility under arbitrary continuations

Actual public default persists through every supported native transition.
Every later continuation therefore has the same declared base utility,
including executions whose horizon ends before the source readout is complete.
Audit deductions remain separate from this base utility.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- After actual public default, every supported terminal continuation has the
same exit utility, without a service or source-completion premise. -/
theorem exclusionBase_continuation_of_defaulted {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (application setup runtime leaks).ResponseMenu)
    (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (control : (application setup runtime leaks).Control) (current : history.state = some control)
    (who : Player) (defaulted : who ∈ control.execution.application.config.defaulted) :
    ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralTerminalFrom
        certificate players history).support,
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who =
        excludedPayoff who := by
  let closed := fun state : (application setup runtime leaks).ProtocolState =>
    ∃ next : (application setup runtime leaks).Control,
      state = some next ∧ who ∈ next.execution.application.config.defaulted
  have preserved := (menu.information initial horizon
    scheduler).runBehavioralTerminalFrom_support_closed
    certificate players closed (fun before joint _legal after holds reached => by
      obtain ⟨before, rfl, member⟩ := holds
      obtain ⟨next, nextEq, _⟩ := (application setup runtime leaks).transition_recall_prefix
        initial horizon scheduler before after joint reached
      exact ⟨next, nextEq, reactive_protocol_defaulted_mono runtime leaks initial horizon scheduler
        before next joint (nextEq ▸ reached) member⟩)
    history ⟨control, current, defaulted⟩
  intro final supported
  obtain ⟨next, nextEq, member⟩ := preserved final supported
  rw [nextEq]
  exact exclusionBase_of_defaulted setup runtime parameter utility excludedPayoff leaks next who
    member

/-- The full continuation's fixed exit utility is integrable and has the
declared expectation, without a range bound on ordinary valuations. -/
theorem exclusionBase_expect_of_defaulted {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (application setup runtime leaks).ResponseMenu)
    (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (control : (application setup runtime leaks).Control) (current : history.state = some control)
    (who : Player) (defaulted : who ∈ control.execution.application.config.defaulted) :
    let law := (menu.information initial horizon scheduler).runBehavioralTerminalFrom
      certificate players history
    PayoffIntegrable law (fun final =>
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) ∧
    expect law (fun final =>
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) =
        excludedPayoff who := by
  have fixed := exclusionBase_continuation_of_defaulted parameter utility excludedPayoff menu
    initial horizon scheduler certificate players history control current who defaulted
  refine ⟨payoffIntegrable_congr_on_support (fun final supported => (fixed final supported).symm)
    (payoffIntegrable_constant _ _), ?_⟩
  exact (expect_congr_on_support fixed).trans (expect_constant _ _)

end Vegas
