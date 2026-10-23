/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Protocol.BehavioralTerminal
import GameTheory.Protocol.RestrictionExecution

/-! # Equivalent continuation horizons after a bounded prefix

A remaining-horizon context and a full-horizon context have identical outcome
laws once both reach termination, and under a global horizon both are terminal
play. This connects results stated with a step count to the terminal-play
sequential equilibrium of the library.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E)

omit [DecidableEq Player] in
/-- Terminal play stays in every set of states closed under legal steps. -/
theorem runBehavioralTerminalFrom_support_closed (certificate : E.WellFoundedHistories)
    (profile : ∀ who, M.BehavioralPolicy who) (closed : E.State → Prop)
    (step : ∀ state joint (legal : E.Legal state joint) target, closed state →
      target ∈ (E.step state ⟨joint, legal⟩).support → closed target)
    (history : E.History) (holds : closed history.state) :
    ∀ final ∈ (M.runBehavioralTerminalFrom certificate profile history).support,
      closed final.state := by
  induction history using certificate.induction with
  | _ current ih =>
      intro final supported
      by_cases stopped : E.terminal current.state
      · rw [InformationModel.runBehavioralTerminalFrom,
          E.randomizedBackwardLaw_of_terminal stopped, PMF.mem_support_pure_iff] at supported
        subst supported
        exact holds
      · rw [InformationModel.runBehavioralTerminalFrom,
          E.randomizedBackwardLaw_of_not_terminal stopped, PMF.support_bind] at supported
        obtain ⟨drawn, _, continued⟩ := Set.mem_iUnion₂.mp supported
        rw [PMF.mem_support_bindOnSupport_iff] at continued
        obtain ⟨target, realized, child⟩ := continued
        exact ih (current.extend drawn.2 realized) ⟨drawn.1, drawn.2, realized⟩
          (step _ _ drawn.2 _ holds realized) final child

omit [DecidableEq Player] in
theorem runBehavioralFrom_remaining
    (profile : ∀ who, M.BehavioralPolicy who) (horizon : Nat)
    (bounded : E.BoundedHorizon horizon) (history : E.History) :
    M.runBehavioralFrom profile (horizon - history.trace.length) history =
      M.runBehavioralFrom profile horizon history := by
  have terminal (last : E.History)
      (supported : last ∈ (M.runBehavioralFrom profile
        (horizon - history.trace.length) history).support) : E.terminal last.state := by
    rcases E.runRandomizedFor_terminal_or_length (M.randomizedChooser profile)
      (horizon - history.trace.length) history last supported with stopped | length
    · exact stopped
    · exact bounded last.state last.trace (by omega)
  have split : horizon = (horizon - history.trace.length) +
      (horizon - (horizon - history.trace.length)) := by omega
  conv_rhs => rw [split, M.runBehavioralFrom_add]
  symm
  refine Eq.trans (bind_congr_on_support _ fun last supported => ?_) (PMF.bind_pure _)
  exact M.runBehavioralFrom_of_terminal profile _ (terminal last supported)

omit [DecidableEq Player] in
/-- Under a global horizon, terminal play from a history is play for the
remaining steps. -/
theorem runBehavioralTerminalFrom_eq_remaining (certificate : E.WellFoundedHistories)
    (profile : ∀ who, M.BehavioralPolicy who) {horizon : Nat}
    (bounded : E.BoundedHorizon horizon) (history : E.History) :
    M.runBehavioralTerminalFrom certificate profile history =
      M.runBehavioralFrom profile (horizon - history.trace.length) history := by
  rw [M.runBehavioralFrom_remaining profile horizon bounded history,
    M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]

omit [DecidableEq Player] in
/-- Under a global horizon, terminal play from the initial history is play for
that horizon. -/
theorem runBehavioralTerminalFrom_initHistory (certificate : E.WellFoundedHistories)
    (profile : ∀ who, M.BehavioralPolicy who) {horizon : Nat}
    (bounded : E.BoundedHorizon horizon) :
    M.runBehavioralTerminalFrom certificate profile E.initHistory =
      M.runBehavioral profile horizon :=
  M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded profile
    E.initHistory

/-- Under a global horizon, sequential equilibrium is the same predicate as
equilibrium against play cut off at that horizon. -/
theorem BehavioralAssessment.isSequentialEquilibrium_iff_truncated_of_bounded
    (assessment : M.BehavioralAssessment) (antichain : M.DecisionInformationAntichain)
    (certificate : E.WellFoundedHistories) {horizon : Nat}
    (bounded : E.BoundedHorizon horizon) (payoff : Player → E.History → ℝ) :
    assessment.IsSequentialEquilibrium antichain certificate payoff ↔
      assessment.IsSequentialEquilibriumFor antichain (fun who site =>
        assessment.truncatedContinuationContext site (payoff who) horizon) := by
  have contexts : (fun who site => assessment.continuationContext certificate site
      (payoff who)) =
      (fun who (site : M.InformationSite who) =>
        assessment.truncatedContinuationContext site (payoff who) horizon) := by
    funext who site
    exact assessment.continuationContext_eq_truncated_of_bounded certificate bounded site
      (payoff who)
  rw [BehavioralAssessment.IsSequentialEquilibrium, contexts]

namespace ActionRestriction

variable {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  (restriction : M.ActionRestriction N)

omit [DecidableEq Player] in
/-- At a retained site of common depth, terminal play of the smaller protocol is
play for the steps remaining before the larger protocol's horizon. -/
theorem runBehavioralTerminalFrom_eq_remaining (certificate : E.WellFoundedHistories)
    {horizon : Nat} (bounded : T.BoundedHorizon horizon)
    (profile : ∀ who, M.BehavioralPolicy who) {who : Player} {site : M.InformationSite who}
    {depth : Nat} (clock : InformationSite.CommonDepth N (restriction.site who site) depth)
    (history : M.InformationHistory who site.1) :
    M.runBehavioralTerminalFrom certificate profile history.1 =
      M.runBehavioralFrom profile (horizon - depth) history.1 := by
  rw [M.runBehavioralTerminalFrom_eq_remaining certificate profile
      (restriction.boundedHorizon bounded),
    restriction.source_commonDepth who site depth clock history]

end ActionRestriction

end GameTheory.Protocol.InformationModel
