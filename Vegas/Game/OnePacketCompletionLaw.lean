/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateDecomposition

/-! # The completion-point law

**The point at a completion.** At a history where the event of a site's rank
has completed, the configuration decodes, after one more event, to a source
point; when that point is a point of the intended game and the site's pending
event did not fail, it is the history's completion point
(`Vegas.completionPoint`). The completion value there is the source
continuation value at that point, and the fallback without one
(`Vegas.completionValue_eq_elim`).

**The completion-point law.** Under play from a history of a site with a law
installed there, until the event completes, the law of the completion point is,
up to a vanishing error and as a sub-probability law on source points, the
history's success probability times a source step law at the history's decoded
point (`Vegas.CompletionPointLaw`). When the step law is a source profile's own
behavioral step, the expected source continuation value after it is the
continuation value at the decoded point itself
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
as a sub-probability law on source points, is `success` times stepLaw up to
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

end Vegas
