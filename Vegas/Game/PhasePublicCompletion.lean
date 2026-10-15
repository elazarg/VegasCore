/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseExclusionPayoff
import Interaction.ReactiveOwnPlay
import GameTheory.Analysis.Protocol.SequentialOneShot

/-! # Whole-policy completion after a public exclusion in the phased runtime

The actual permanent public exclusion remains visible under every subsequent
phase, retry and legal response. Therefore free one-shot optimality at flagged
inputs controls whole continuation policies throughout each such information
fiber. No constant payoff for an unexcluded player is asserted.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (mode : EventGraph.ExecutionMode) (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "N" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

/-- The complete actual player input displays at least one permanent exclusion. -/
def PhasePublicExclusion (input : (phaseApplication runtime leaks).Info) : Prop :=
  ∃ past view, input = some (past, view) ∧ view.application.2.excluded ≠ ∅

open Classical in
/-- Change a whole policy only at inputs after a public exclusion. -/
def afterPhaseExclusionPolicy {who : Player} (baseline alternative : (N).BehavioralPolicy who) :
    (N).BehavioralPolicy who := fun input =>
  if PhasePublicExclusion setup mode runtime leaks input then alternative input else baseline input

omit [Fintype Player] in
private theorem phase_excluded_of_reaches {owner : Player} {first last : (E).History}
    (reached : (E).HistoryReaches first last)
    (excluded : PhaseExcluded setup mode runtime leaks owner first.state) :
    PhaseExcluded setup mode runtime leaks owner last.state := by
  obtain ⟨fuel, path⟩ := reached
  induction path with
  | refl => exact excluded
  | step joint legal realized rest ih =>
      exact ih (phaseExcluded_transition setup mode runtime leaks initial horizon scheduler
        _ _ joint excluded realized)

omit [Fintype Player] in
private theorem phase_publicExclusion_of_active {owner who : Player} (history : (E).History)
    (excluded : PhaseExcluded setup mode runtime leaks owner history.state)
    (active : (E).active history.state who) :
    PhasePublicExclusion setup mode runtime leaks ((N).infoOf who history.trace) := by
  simp only [ReactiveApplication.ResponseMenu.information,
    ReactiveApplication.ResponseMenu.info]
  cases state : history.state with
  | none => rw [state] at excluded; exact excluded.elim
  | some control =>
      rw [state] at excluded active
      change control.actor = some who at active
      simp only [ReactiveApplication.observe, active, ↓reduceIte]
      exact ⟨_, _, rfl, Finset.ne_empty_of_mem excluded⟩

omit [Fintype Player] in
private theorem phase_excluded_of_information_publicExclusion {who : Player}
    (site : (N).InformationSite who)
    (flagged : PhasePublicExclusion setup mode runtime leaks site.1)
    (history : (N).InformationHistory who site.1) :
    ∃ owner, PhaseExcluded setup mode runtime leaks owner history.1.state := by
  obtain ⟨past, view, atSite, nonempty⟩ := flagged
  have observed := ((menu).info initial horizon scheduler who history.1.trace).symm.trans
    (history.2.trans atSite)
  cases state : history.1.state with
  | none => rw [state] at observed; cases observed
  | some control =>
      rw [state] at observed
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        have flags := congrArg (fun input => input.2.application.2.excluded)
          (Option.some.inj observed)
        have excluded : control.execution.application.current.excluded ≠ ∅ := by
          intro empty
          exact nonempty (flags.symm.trans empty)
        obtain ⟨owner, member⟩ := Finset.nonempty_iff_ne_empty.mpr excluded
        exact ⟨owner, member⟩
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        cases observed

open Classical in
/-- After an exclusion, restricting a deviator's policy to public-exclusion
inputs preserves its entire actual terminal continuation law. -/
theorem phase_run_afterExclusionPolicy_eq
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ player, (N).BehavioralPolicy player) {who owner : Player}
    (alternative : (N).BehavioralPolicy who) (history : (E).History)
    (excluded : PhaseExcluded setup mode runtime leaks owner history.state) :
    (N).runBehavioralTerminalFrom certificate
        (Profile.update (sig := (N).behavioralSignature) profile who alternative) history =
      (N).runBehavioralTerminalFrom certificate
        (Profile.update (sig := (N).behavioralSignature) profile who
          (afterPhaseExclusionPolicy setup mode runtime leaks menu initial horizon scheduler
            (profile who)
            alternative)) history := by
  apply (N).runBehavioralTerminalFrom_congr certificate history
  intro later reached _nonterminal player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    by_cases active : (E).active later.state who
    · have retained := phase_excluded_of_reaches setup mode runtime leaks menu initial horizon
        scheduler reached excluded
      have flagged := phase_publicExclusion_of_active setup mode runtime leaks menu initial horizon
        scheduler later retained active
      simp only [afterPhaseExclusionPolicy, flagged, ↓reduceIte]
    · exact (N).behavioral_eq_of_not_active _ _ later.trace active
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

open Classical in
/-- The continuation value of an arbitrary deviation agrees with its
public-exclusion restriction throughout the actual information fiber. -/
theorem phase_value_afterExclusionPolicy_eq (certificate : (E).WellFoundedHistories)
    (assessment : (N).BehavioralAssessment) {who : Player} (site : (N).InformationSite who)
    (flagged : PhasePublicExclusion setup mode runtime leaks site.1) (payoff : (E).History → ℝ)
    (alternative : (N).BehavioralPolicy who) :
    (assessment.continuationContext certificate site payoff).value alternative =
      (assessment.continuationContext certificate site payoff).value
        (afterPhaseExclusionPolicy setup mode runtime leaks menu initial horizon scheduler
          (assessment.strategy who)
          alternative) := by
  rw [BehavioralAssessment.continuationContext_value,
    BehavioralAssessment.continuationContext_value]
  apply congrArg (fun law : PMF (E).History => expect law payoff)
  apply bind_congr_on_support
  intro history _supported
  obtain ⟨owner, excluded⟩ := phase_excluded_of_information_publicExclusion setup mode runtime leaks
    menu initial horizon scheduler site flagged history
  exact phase_run_afterExclusionPolicy_eq setup mode runtime leaks menu initial horizon scheduler
    certificate assessment.strategy alternative history.1 excluded

variable [Finite (menu.protocol initial horizon scheduler).History]
  [∀ who, DecidableEq ((menu.information initial horizon scheduler).InfoState who)]

open Classical in
/-- One-shot optimality supplied by free-site completion controls arbitrary
whole policies at every actual public-exclusion information site. -/
theorem wholePolicyOptimal_of_phasePublicExclusion
    (certificate : (E).WellFoundedHistories) (payoff : Player → (E).History → ℝ)
    (assessment : (N).BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      ((menu).decisionRecall initial horizon scheduler).decisionInformationAntichain)
    (localOptimal : ∀ player (site : (N).InformationSite player),
      PhasePublicExclusion setup mode runtime leaks site.1 →
        ∀ law : PMF ((N).Choice player site.1),
          (assessment.continuationContext certificate site (payoff player)).value
              ((assessment.strategy player).withLaw site.1 law) ≤
            (assessment.continuationContext certificate site (payoff player)).value
              (assessment.strategy player))
    (who : Player) (site : (N).InformationSite who)
    (flagged : PhasePublicExclusion setup mode runtime leaks site.1)
    (alternative : (N).BehavioralPolicy who) :
    (assessment.continuationContext certificate site (payoff who)).value alternative ≤
      (assessment.continuationContext certificate site (payoff who)).value
        (assessment.strategy who) := by
  let := Fintype.ofFinite (menu.protocol initial horizon scheduler).History
  let restricted := afterPhaseExclusionPolicy setup mode runtime leaks menu initial horizon
    scheduler (assessment.strategy who) alternative
  rw [phase_value_afterExclusionPolicy_eq setup mode runtime leaks menu initial horizon scheduler
    certificate assessment site flagged (payoff who) alternative]
  apply consistent.continuation_value_le_of_locallyOptimal (N)
    ((menu).decisionRecall initial horizon scheduler)
    (fun player input law => PhasePublicExclusion setup mode runtime leaks input ∨
      law = assessment.strategy player input)
    payoff certificate ?_ who site restricted ?_
  · intro player later law allowed
    rcases allowed with excluded | same
    · exact localOptimal player later excluded law
    · rw [same, BehavioralPolicy.withLaw_eq_self]
  · intro later
    by_cases excluded : PhasePublicExclusion setup mode runtime leaks later.1
    · exact Or.inl excluded
    · exact Or.inr (ite_eq_right excluded)

end Vegas
