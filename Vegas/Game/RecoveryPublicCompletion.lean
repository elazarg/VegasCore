/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryOnePacketComponents
import Vegas.Game.RecoveryExclusionPayoff
import GameTheory.Analysis.Protocol.SequentialOneShot
import Interaction.ReactiveOwnPlay

/-! # Whole-policy optimality after public exclusion

Permanent exclusion is visible and persists through actual recovery steps.
One-shot optimality of the freely completed sites therefore controls arbitrary
whole continuation policies from every post-exclusion information site.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (RecoveryState (graph setup)))
  (horizon : Nat) (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "N" => model setup leaks bounds initial horizon scheduler
local notation "menu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) initial horizon scheduler

open Classical in
/-- Change a whole policy only at inputs after a public exclusion. -/
def afterExclusionPolicy {who : Player} (baseline alternative : (N).BehavioralPolicy who) :
    (N).BehavioralPolicy who := fun input =>
  if PublicExclusion setup leaks input then alternative input else baseline input

private theorem excluded_of_reaches {owner : Player} {first last : (E).History}
    (reached : (E).HistoryReaches first last)
    (excluded : RecoveryExcluded (setup := setup) (leaks := leaks) owner first.state) :
    RecoveryExcluded (setup := setup) (leaks := leaks) owner last.state := by
  obtain ⟨fuel, path⟩ := reached
  induction path with
  | refl => exact excluded
  | step joint legal realized rest ih =>
      exact ih (recoveryExcluded_transition initial horizon scheduler _ _ joint excluded realized)

private theorem publicExclusion_of_active {owner who : Player} (history : (E).History)
    (excluded : RecoveryExcluded (setup := setup) (leaks := leaks) owner history.state)
    (active : (E).active history.state who) :
    PublicExclusion setup leaks ((N).infoOf who history.trace) := by
  simp only [model, ReactiveApplication.ResponseMenu.information,
    ReactiveApplication.ResponseMenu.info]
  cases state : history.state with
  | none => rw [state] at excluded; exact excluded.elim
  | some control =>
      rw [state] at excluded active
      change control.actor = some who at active
      simp only [ReactiveApplication.observe, active, ↓reduceIte]
      exact ⟨_, _, rfl, Finset.ne_empty_of_mem excluded⟩

private theorem excluded_of_information_publicExclusion {who : Player}
    (site : (N).InformationSite who) (flagged : PublicExclusion setup leaks site.1)
    (history : (N).InformationHistory who site.1) :
    ∃ owner, RecoveryExcluded (setup := setup) (leaks := leaks) owner history.1.state := by
  obtain ⟨past, view, atSite, nonempty⟩ := flagged
  have observed := ((menu).info initial horizon scheduler who history.1.trace).symm.trans
    (history.2.trans atSite)
  cases state : history.1.state with
  | none => rw [state] at observed; cases observed
  | some control =>
      rw [state] at observed
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        have flags := congrArg (fun input => input.2.application.2) (Option.some.inj observed)
        have excluded : control.execution.application.excluded ≠ ∅ := by
          intro empty
          exact nonempty (flags.symm.trans empty)
        obtain ⟨owner, member⟩ := Finset.nonempty_iff_ne_empty.mpr excluded
        exact ⟨owner, member⟩
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        cases observed

open Classical in
/-- After an exclusion, restricting a deviator's policy to public-exclusion
inputs preserves its entire actual terminal continuation law. -/
theorem run_afterExclusionPolicy_eq
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ player, (N).BehavioralPolicy player) {who owner : Player}
    (alternative : (N).BehavioralPolicy who) (history : (E).History)
    (excluded : RecoveryExcluded (setup := setup) (leaks := leaks) owner history.state) :
    (N).runBehavioralTerminalFrom certificate
        (Profile.update (sig := (N).behavioralSignature) profile who alternative) history =
      (N).runBehavioralTerminalFrom certificate
        (Profile.update (sig := (N).behavioralSignature) profile who
          (afterExclusionPolicy setup leaks bounds initial horizon scheduler (profile who)
            alternative)) history := by
  apply (N).runBehavioralTerminalFrom_congr certificate history
  intro later reached _nonterminal player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    by_cases active : (E).active later.state who
    · have flagged := publicExclusion_of_active setup leaks bounds initial horizon scheduler later
        (excluded_of_reaches setup leaks bounds initial horizon scheduler reached excluded) active
      simp only [afterExclusionPolicy, flagged, ↓reduceIte]
    · exact (N).behavioral_eq_of_not_active _ _ later.trace active
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

open Classical in
/-- The continuation value of an arbitrary deviation agrees with its
public-exclusion restriction throughout the actual information fiber. -/
theorem value_afterExclusionPolicy_eq (certificate : (E).WellFoundedHistories)
    (assessment : (N).BehavioralAssessment) {who : Player} (site : (N).InformationSite who)
    (flagged : PublicExclusion setup leaks site.1) (payoff : (E).History → ℝ)
    (alternative : (N).BehavioralPolicy who) :
    (assessment.continuationContext certificate site payoff).value alternative =
      (assessment.continuationContext certificate site payoff).value
        (afterExclusionPolicy setup leaks bounds initial horizon scheduler (assessment.strategy who)
          alternative) := by
  rw [BehavioralAssessment.continuationContext_value,
    BehavioralAssessment.continuationContext_value]
  apply congrArg (fun law : PMF (E).History => expect law payoff)
  apply bind_congr_on_support
  intro history _supported
  obtain ⟨owner, excluded⟩ := excluded_of_information_publicExclusion setup leaks bounds initial
    horizon scheduler site flagged history
  exact run_afterExclusionPolicy_eq setup leaks bounds initial horizon scheduler certificate
    assessment.strategy alternative history.1 excluded

variable [Fintype ((Recovery.onePacketMenu (runtime setup) leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq ((model setup leaks bounds initial horizon scheduler).InfoState who)]

open Classical in
/-- A consistent assessment locally optimal at its free agents is rational
against arbitrary whole policies at every site after public exclusion. -/
theorem wholePolicyOptimal_of_publicExclusion
    (certificate : (E).WellFoundedHistories) (payoff : Player → (E).History → ℝ)
    (assessment : (N).BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      ((menu).decisionRecall initial horizon scheduler).decisionInformationAntichain)
    (localOptimal : ∀ player (site : (N).InformationSite player),
      FreeAgent setup leaks bounds initial horizon scheduler ((N).agentAt site) →
        ∀ law : PMF ((N).Choice player site.1),
          (assessment.continuationContext certificate site (payoff player)).value
              ((assessment.strategy player).withLaw site.1 law) ≤
            (assessment.continuationContext certificate site (payoff player)).value
              (assessment.strategy player))
    (who : Player) (site : (N).InformationSite who)
    (flagged : PublicExclusion setup leaks site.1) (alternative : (N).BehavioralPolicy who) :
    (assessment.continuationContext certificate site (payoff who)).value alternative ≤
      (assessment.continuationContext certificate site (payoff who)).value
        (assessment.strategy who) := by
  let restricted := afterExclusionPolicy setup leaks bounds initial horizon scheduler
    (assessment.strategy who) alternative
  rw [value_afterExclusionPolicy_eq setup leaks bounds initial horizon scheduler certificate
    assessment site flagged (payoff who) alternative]
  apply consistent.continuation_value_le_of_locallyOptimal (N)
    ((menu).decisionRecall initial horizon scheduler)
    (fun player input law => PublicExclusion setup leaks input ∨
      law = assessment.strategy player input)
    payoff certificate ?_ who site restricted ?_
  · intro player later law allowed
    rcases allowed with excluded | same
    · exact localOptimal player later (freeAgent_of_publicExclusion setup leaks bounds initial
        horizon scheduler ((N).agentAt later) excluded) law
    · rw [same, BehavioralPolicy.withLaw_eq_self]
  · intro later
    by_cases excluded : PublicExclusion setup leaks later.1
    · exact Or.inl excluded
    · exact Or.inr (ite_eq_right excluded)

end Vegas.RecoveryOnePacket
