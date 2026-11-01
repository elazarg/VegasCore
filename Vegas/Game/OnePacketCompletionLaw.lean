/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateSuccess

/-! # The completion-point law

**The point at a completion.** At a history where the event of a site's rank
has completed, the configuration decodes at its actual completed endpoint to
a source point; when that point is a point of the intended game and the site's pending
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
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

/-- **The completion-point law.** From a history, under play of `installed`
until the event of rank `rank` completes, the law of the completion point,
as a sub-probability law on source points, is `success` times stepLaw up to
`error` against every bounded value. -/
def CompletionPointLaw
    (installed : ∀ who,
      (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
        scheduler).BehavioralPolicy who)
    (rank : Nat) (fresh : (application setup runtime leaks).Control → Prop)
    (history : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (success : ℝ) (stepLaw : PMF (ProtocolState setup.program)) (error : ℝ) : Prop :=
  ∀ (value : ProtocolState setup.program → ℝ) (bound : ℝ), (∀ point, |value point| ≤ bound) →
    |expect ((onePacketN).runBehavioralUntil
        ((bounds.onePacketMenu runtime leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories installed
        (LateStopped setup runtime leaks bounds horizon scheduler rank) history)
        (fun stop => (completionPoint setup runtime leaks bounds horizon scheduler rank fresh
          stop).elim
          0 value) -
      success * expect stepLaw value| ≤ error * bound

/-- The completion value uses the actual completion point, with its fallback
at every history where that point is unavailable. -/
theorem completionValue_eq_elim (profile : BehavioralProfile setup.program)
    (rank : Nat) (fresh : (application setup runtime leaks).Control → Prop) (who : Player)
    (fallback : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History → ℝ)
    (history : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History) :
    completionValue setup runtime leaks bounds horizon scheduler parameter utility excludedPayoff
        profile rank fresh who fallback history =
      (completionPoint setup runtime leaks bounds horizon scheduler rank fresh history).elim
        (fallback history)
        (sourcePointValue setup parameter utility excludedPayoff profile who) := rfl

end Vegas
