/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateDecomposition

/-! # The completion-point law

**The point at a completion.** At a history where the event of a site's rank
has completed, the configuration decodes, after one more event, to a source
point; when that point is a point of the intended game and the site's pending
event did not fail, it is the history's completion point
(`Vegas.completionPoint`), and the completion value there is the source
continuation value at that point.

**The completion-point law.** The primitive input of the value decomposition is
the law of the completion point under play, from a history of a site with a
law installed there, until the event completes: up to a vanishing error, as a
sub-probability law on source points, it is the history's success probability
times a source step law at the history's decoded point (`Vegas.CompletionPointLaw`).
Together with the vanishing mass of stops without a completion point at which
the site's failure is not sure, it gives the completion value from the history:
the success probability times the expected source continuation value of the
step law (`Vegas.abs_historyStopValue_sub_le_of_completionPointLaw`). When the
step law is the step of the intended effective opening, that expectation is the
source continuation value at the decoded point itself
(`Vegas.expect_sourcePointValue_behavioralStateStep`).
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
/-- **The completion point of a history.** The source point the configuration
decodes to after `rank + 1` events, when it has completed them, the point is a
point of the intended game, and the control satisfies `fresh`. -/
def completionPoint (rank : Nat) (fresh : (application setup leaks).Control → Prop)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History) : Option (ProtocolState setup.program) :=
  match history.state with
  | none => none
  | some control =>
      if control.execution.application.config.cut.IsPrefix (rank + 1) then
        match sourceServicePrefix? setup (rank + 1) control.execution.application.config with
        | some point =>
            if ProtocolState.Intended setup.program point ∧ fresh control then some point
            else none
        | none => none
      else none

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The completion value at a history with a completion point is the source
continuation value there. -/
theorem completionValue_of_completionPoint (profile : BehavioralProfile setup.program)
    (rank : Nat) (fresh : (application setup leaks).Control → Prop) (who : Player)
    (fallback : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History → ℝ)
    {history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History} {point : ProtocolState setup.program}
    (pointEq : completionPoint setup leaks bounds horizon scheduler rank fresh history =
      some point) :
    LateStopped setup leaks bounds horizon scheduler rank history ∧
      completionValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        profile rank fresh who fallback history =
        sourcePointValue setup parameter utility excludedPayoff profile who point := by
  classical
  unfold completionPoint at pointEq
  unfold completionValue
  split at pointEq
  · cases pointEq
  · rename_i control state
    split at pointEq
    · rename_i completed
      refine ⟨⟨control, state, completed⟩, ?_⟩
      rw [state]
      dsimp only
      split at pointEq
      · rename_i decoded
        rw [decoded]
        dsimp only
        split at pointEq
        · rename_i good
          cases pointEq
          rw [ite_eq_left good ..]
        · cases pointEq
      · cases pointEq
    · cases pointEq

/-- **The source step keeps the continuation value.** The expected source
continuation value of a profile after one step of its own behavioral step law
is the continuation value before it. -/
theorem expect_sourcePointValue_behavioralStateStep (profile : BehavioralProfile setup.program)
    (who : Player) {bound : ℝ}
    (readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility excludedPayoff
      readout who| ≤ bound)
    (point : ProtocolState setup.program) :
    expect (ProtocolState.behavioralStateStep setup.program profile point)
        (sourcePointValue setup parameter utility excludedPayoff profile who) =
      sourcePointValue setup parameter utility excludedPayoff profile who point := by
  unfold sourcePointValue
  simp only [expect_map]
  rw [← expect_bind_tower_bounded _ _ ((fun readout => exclusionReadoutUtility setup
    parameter utility excludedPayoff readout who) ∘ some) (fun terminal => readoutBounded
      (some terminal)), sourceStep_continuation]

/-- **The completion-point law.** From a history, under play of `installed`
until the event of rank `rank` completes, the law of the completion point,
as a sub-probability law on source points, is `success` times `stepLaw` up to
`error` against every bounded value. -/
def CompletionPointLaw
    (installed : ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (rank : Nat) (fresh : (application setup leaks).Control → Prop)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (success : ℝ) (stepLaw : PMF (ProtocolState setup.program)) (error : ℝ) : Prop :=
  ∀ (value : ProtocolState setup.program → ℝ) (bound : ℝ), (∀ point, |value point| ≤ bound) →
    |expect ((onePacketN).runBehavioralUntil
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories installed
        (LateStopped setup leaks bounds horizon scheduler rank) history)
        (fun stop => (completionPoint setup leaks bounds horizon scheduler rank fresh stop).elim
          0 value) -
      success * expect stepLaw value| ≤ error * bound

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- At a history where the event completed, the completion value is the source
continuation value at the completion point, and the fallback without one. -/
theorem completionValue_eq_elim (profile : BehavioralProfile setup.program)
    (rank : Nat) (fresh : (application setup leaks).Control → Prop) (who : Player)
    (fallback : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History → ℝ)
    {history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History}
    (halted : LateStopped setup leaks bounds horizon scheduler rank history) :
    completionValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        profile rank fresh who fallback history =
      (completionPoint setup leaks bounds horizon scheduler rank fresh history).elim
        (fallback history)
        (sourcePointValue setup parameter utility excludedPayoff profile who) := by
  classical
  obtain ⟨control, state, completed⟩ := halted
  unfold completionValue completionPoint
  rw [state]
  dsimp only
  rw [ite_eq_left completed ..]
  cases decoded : sourceServicePrefix? setup (rank + 1) control.execution.application.config with
  | none => rfl
  | some point =>
      dsimp only
      by_cases good : ProtocolState.Intended setup.program point ∧ fresh control
      · rw [ite_eq_left good .., ite_eq_left good ..]
        rfl
      · rw [ite_eq_right good .., ite_eq_right good ..]
        rfl

open Classical in
/-- **The completion value from a history by its completion-point law.** Let
the completion-point law from a history of a site with `law` installed be
`success` times `stepLaw` up to `pointError`, and let the stops without a
completion point at which terminal play does not surely reach the site's
failure set have mass at most `badMass`. Then, with the payoff of every readout
bounded by `bound`, the completion value from the history is `success` times
the expected source continuation value under `stepLaw` up to
`(pointError + badMass) * bound`. -/
theorem abs_historyStopValue_sub_le_of_completionPointLaw
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1))
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (success : ℝ) (stepLaw : PMF (ProtocolState setup.program)) {pointError badMass bound : ℝ}
    (readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility excludedPayoff
      readout who| ≤ bound)
    (pointLaw : CompletionPointLaw setup leaks bounds horizon scheduler
      (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
        ((assessment.strategy who).withLaw site.1 law))
      (siteRank site.1) (siteFresh who site.1) history success stepLaw pointError)
    (badLaw : expect ((onePacketN).runBehavioralUntil
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories
        (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
          ((assessment.strategy who).withLaw site.1 law))
        (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history)
      (fun stop => if completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
          (siteFresh who site.1) stop = none ∧
        ¬ ∀ final ∈ ((onePacketN).runBehavioralTerminalFrom
          ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
            scheduler).wellFoundedHistories
          (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 law)) stop).support,
          final ∈ onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)
        then 1 else 0) ≤ badMass) :
    |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site law history -
      success * expect stepLaw (sourcePointValue setup parameter utility excludedPayoff profile
        who)| ≤ (pointError + badMass) * bound := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let installed := Profile.update (sig := model.behavioralSignature) assessment.strategy who
    ((assessment.strategy who).withLaw site.1 law)
  let failed := onePacketFailed setup leaks bounds horizon scheduler (model.agentAt site)
  let payoff := fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    if final ∈ failed then 0
    else exclusionBase setup parameter utility excludedPayoff leaks final.state who
  let fallback := fun later => expect (model.runBehavioralTerminalFrom certificate installed later)
    payoff
  let stopped := LateStopped setup leaks bounds horizon scheduler (siteRank site.1)
  let point := completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
    (siteFresh who site.1)
  let value := sourcePointValue setup parameter utility excludedPayoff profile who
  let stand := fun stop => if stopped stop then
      completionValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        profile (siteRank site.1) (siteFresh who site.1) who fallback stop
    else payoff stop
  let sure := fun stop => ∀ final ∈ (model.runBehavioralTerminalFrom certificate installed
    stop).support, final ∈ failed
  let untilLaw := model.runBehavioralUntil certificate installed stopped history
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (readoutBounded none)
  have payoffBounded : ∀ final, |payoff final| ≤ bound := fun final => by
    simp only [payoff]
    split
    · rw [abs_zero]
      exact boundNonneg
    · exact readoutBounded _
  have fallbackBounded : ∀ later, |fallback later| ≤ bound := fun later =>
    expect_abs_le_of_bounded boundNonneg payoffBounded
  have valueBounded : ∀ target, |value target| ≤ bound := fun target =>
    expect_abs_le_of_bounded boundNonneg fun readout => readoutBounded readout
  have standEq : ∀ stop, stopped stop → stand stop = (point stop).elim (fallback stop) value :=
    fun stop halted => by
      simp only [stand, halted, ↓reduceIte]
      exact completionValue_eq_elim setup leaks bounds horizon scheduler parameter utility
        excludedPayoff profile _ _ who fallback halted
  have standBounded : ∀ stop, |stand stop| ≤ bound := fun stop => by
    by_cases halted : stopped stop
    · rw [standEq stop halted]
      cases point stop with
      | none => exact fallbackBounded _
      | some target => exact valueBounded target
    · simp only [stand, halted, ↓reduceIte]
      exact payoffBounded _
  -- The completion value splits into its value at the completion point and the rest.
  let rest := fun stop => if point stop = none ∧ ¬ sure stop then stand stop else 0
  have split : ∀ stop ∈ untilLaw.support, stand stop = (point stop).elim 0 value + rest stop := by
    intro stop member
    cases pointCase : point stop with
    | some target =>
        obtain ⟨halted, _⟩ := completionValue_of_completionPoint setup leaks bounds horizon
          scheduler parameter utility excludedPayoff profile _ _ who fallback pointCase
        rw [standEq stop halted, pointCase]
        simp only [rest, pointCase, reduceCtorEq, false_and, ↓reduceIte, Option.elim_some,
          add_zero]
    | none =>
        simp only [rest, pointCase, true_and, Option.elim_none, zero_add]
        by_cases isSure : sure stop
        · rw [ite_eq_right (not_not_intro isSure) ..]
          by_cases halted : stopped stop
          · rw [standEq stop halted, pointCase]
            change expect _ payoff = 0
            rw [expect_congr_on_support (g := fun _ => 0) fun final finalMember => by
              simp only [payoff, isSure final finalMember, ↓reduceIte]]
            exact expect_constant _ 0
          · have ended := (model.mem_support_runBehavioralUntil certificate installed stopped
              history stop member).resolve_left halted
            simp only [stand, halted, ↓reduceIte]
            have terminalLaw : model.runBehavioralTerminalFrom certificate installed stop =
                PMF.pure stop := by
              change (menu.protocol (initialLaw setup) horizon scheduler).randomizedBackwardLaw
                certificate (model.randomizedChooser installed) stop = _
              exact ExecutionProtocol.randomizedBackwardLaw_of_terminal _ ended
            have inFailed := isSure stop (by
              rw [terminalLaw]
              exact (PMF.mem_support_pure_iff _ _).mpr rfl)
            simp only [payoff, inFailed, ↓reduceIte]
        · rw [ite_eq_left isSure ..]
  have restAbs : ∀ stop, |rest stop| ≤ bound * (if point stop = none ∧ ¬ sure stop then 1 else 0) :=
    fun stop => by
      simp only [rest]
      split
      · rw [mul_one]
        exact standBounded stop
      · rw [abs_zero, mul_zero]
  have total : expect untilLaw stand =
      expect untilLaw (fun stop => (point stop).elim 0 value) + expect untilLaw rest := by
    rw [expect_congr_on_support split]
    exact expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  have restBound : |expect untilLaw rest| ≤ bound * badMass := by
    let indicator := fun stop => if point stop = none ∧ ¬ sure stop then (1 : ℝ) else 0
    have upper := expect_mono (μ := untilLaw) (f := rest) (g := fun stop => bound * indicator stop)
      (fun stop _ => (abs_le.mp (restAbs stop)).2) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    have lower := expect_mono (μ := untilLaw) (f := fun stop => -(bound * indicator stop))
      (g := rest) (fun stop _ => (abs_le.mp (restAbs stop)).1) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    rw [expect_const_mul] at upper
    rw [expect_neg, expect_const_mul] at lower
    have badLe : expect untilLaw indicator ≤ badMass := badLaw
    have product := mul_le_mul_of_nonneg_left badLe boundNonneg
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have pointBound := pointLaw value bound valueBounded
  change |expect untilLaw stand - _| ≤ _
  rw [total]
  calc _ ≤ |expect untilLaw (fun stop => (point stop).elim 0 value) -
          success * expect stepLaw value| + |expect untilLaw rest| := by
        rw [show expect untilLaw (fun stop => (point stop).elim 0 value) + expect untilLaw rest -
          success * expect stepLaw value = (expect untilLaw (fun stop => (point stop).elim 0 value)
            - success * expect stepLaw value) + expect untilLaw rest by ring]
        exact abs_add_le _ _
    _ ≤ pointError * bound + bound * badMass := add_le_add pointBound restBound
    _ = _ := by ring

end Vegas
