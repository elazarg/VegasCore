/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateDecomposition
import Vegas.Game.IntendedCommitGain

/-! # Late commitments of intended values

**The value of committing a choice at a site.** The belief average, over the
histories of a site, of the source continuation value after the source step of
a choice at the decoded point of the site's rank (`Vegas.siteCommitValue`).

**Value-blind late commitments.** At a forced late delivery at which the player
owes no failure, a choice committing an intended value at a prepared slot fails
as the late option sending at that slot does, and its completion value is its
success probability times the value of committing that value at the site, up to
an error (`Vegas.LateCommitBlind`). This is the value blindness of late success
for a single committed value: the success of a late packet depends neither on
the committed value nor, under the belief, on the hidden values the
continuation depends on.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- **The value of committing a choice at a site history.** The expected source
continuation value of `profile` after the source step of `choice` at the point
the history's configuration decodes to after `rank` events, when that point is a
point of the intended game; the exclusion payoff otherwise. -/
def decodedCommitValue (profile : BehavioralProfile setup.program) (who : Player) (rank : Nat)
    (choice : Option (OwnAction Player L))
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History) : ℝ :=
  match history.state with
  | none => excludedPayoff who
  | some control =>
      match sourceServicePrefix? setup rank control.execution.application.config with
      | none => excludedPayoff who
      | some point =>
          if IntendedReached setup point then
            expect (ProtocolState.step setup.program point fun _ => choice)
              (sourcePointValue setup parameter utility excludedPayoff profile who)
          else excludedPayoff who

/-- **The value of committing a choice at a site.** The belief average, over the
histories of a site, of the value of committing the choice at their decoded
point of the site's rank. -/
def siteCommitValue (assessment : (onePacketN).BehavioralAssessment)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (choice : Option (OwnAction Player L)) : ℝ :=
  expect (assessment.belief who site) fun history =>
    decodedCommitValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
      profile who (siteRank site.1) choice history.1

/-- **Value-blind late commitments.** At every forced late delivery at which the
player owes no failure, every choice at the player's own turn committing, at a
prepared slot below `slots`, a value whose decoded source choice is intended
fails within `blindError n` of the late option sending at that slot, and its
completion value is within `blindError n` of its success probability times the
value of committing that source choice at the site. -/
def LateCommitBlind (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (blindError : ℕ → ℝ) : Prop :=
  ∀ n who (site : (onePacketN).InformationSite who),
    ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
    ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
      ((onePacketN).agentAt site) →
    SiteDebtFree setup leaks bounds horizon scheduler site →
    ∀ (choice : (onePacketN).Choice who site.1)
      (past : List (application setup leaks).PlayerEntry)
      (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
      (material : (application setup leaks).Submission) (event : (graph setup).EventId)
      (serial : Nat) (payload : L.Ty)
      (outputEq : (graph setup).outputLayout event = .binding who payload) (value : L.Val payload),
      site.1 = some (past, view) → choice.1 = some response →
      response.transmission = some material →
      material.call.packet = .commitment event (who, .prepared serial) →
      view.application.publicView.ownTurn? who = some event →
      material.call.candidateAfter who view.application.candidates (.prepared serial) =
        .openable ⟨payload, value⟩ →
      sourceOfValue setup event outputEq value ∈
        setup.intendedMenu who (projectView setup leaks who site.1) →
      ∀ inRange : serial < slots,
        |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (PMF.pure choice) -
          onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n ((onePacketN).agentAt site)
              (some ⟨serial, inRange⟩))| ≤ blindError n ∧
        |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
            (PMF.pure choice) -
          (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (PMF.pure choice)) *
            siteCommitValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
              (sourceOfValue setup event outputEq value)| ≤ blindError n

end Vegas
