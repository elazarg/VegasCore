/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceReplayComparison
import GameTheoryExtensions.Analysis.Protocol.RestrictionExtension
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Sequential equilibrium with harmless published watcher replays

The same bounded native game admits all published-ID replays at watcher turns.
No fine, monitoring probability, or utility indifference is needed for this
extension. The payoff may depend on the complete final application state.

This is a proof menu inside the existing runtime. The argument uses the fixed
service calendar and its observation interface, which does not expose duplicate
arrival notifications. It does not erase fresh packets or private response recall.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
  (payoff : Option (application setup leaks).State → Player → ℝ)

include reveals observer openable in
/-- One fixed replay-extended game implements every retained SE, with the same
complete initialized history law and application-state payoff law. In particular,
the watcher may have arbitrary preferences over application outcomes. -/
theorem replay_equilibrium_extends [setup.FiniteInitialLaw] [leaks.FiniteSupport]
    (source : (information setup leaks bounds watcher).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((menu setup leaks bounds watcher).decisionInformationAntichain (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher))
      (fun who site => source.truncatedContinuationContext site
        (fun history => payoff (history.state.map
          (fun control => control.execution.application)) who)
        (2 * horizon setup watcher + 1))) :
    ∃ target : ((replayMenu setup leaks bounds watcher).information (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((replayMenu setup leaks bounds watcher).decisionInformationAntichain (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher))
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff (history.state.map
            (fun control => control.execution.application)) who)
          (2 * horizon setup watcher + 1)) ∧
      ((menu_in_replay setup leaks bounds watcher).actionRestriction (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)).ExtendsProfile
          source.strategy target.strategy ∧
      ((information setup leaks bounds watcher).runBehavioral source.strategy
        (2 * horizon setup watcher + 1)).map
          ((menu_in_replay setup leaks bounds watcher).actionRestriction (initialLaw setup)
            (horizon setup watcher) (scheduler setup leaks watcher)).history =
        ((replayMenu setup leaks bounds watcher).information (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher)).runBehavioral target.strategy
            (2 * horizon setup watcher + 1) := by
  classical
  let initial := initialLaw setup
  let count := horizon setup watcher
  let service := scheduler setup leaks watcher
  let retained := menu setup leaks bounds watcher
  let replayed := replayMenu setup leaks bounds watcher
  let restriction := (menu_in_replay setup leaks bounds watcher).actionRestriction
    initial count service
  let model := replayed.information initial count service
  let depth (who : Player) (site : model.InformationSite who) :=
    decisionDepth setup leaks watcher who site.1
  let utility : (application setup leaks).ProtocolState → Player → ℝ :=
    fun state => payoff (state.map (fun control => control.execution.application))
  have clock := menu_common_decision_depth setup leaks replayed watcher reveals observer
  have sourceClock := menu_common_decision_depth setup leaks retained watcher reveals observer
  have sourceBounded := retained.bounded initial count service
  have targetBounded := replayed.bounded initial count service
  have sourceCertificate := sourceBounded.wellFoundedHistories
  have targetCertificate := targetBounded.wellFoundedHistories
  have sourceTerminal := (source.isSequentialEquilibrium_iff_truncated_of_bounded
    (information setup leaks bounds watcher)
    (retained.decisionInformationAntichain initial count service) sourceCertificate sourceBounded
    (fun who history => utility history.state who)).mpr equilibrium
  let comparator (who : Player)
      (site : (information setup leaks bounds watcher).InformationSite who)
      (_ : model.Choice who (restriction.site who site).1) :
      PMF ((information setup leaks bounds watcher).Choice who site.1) :=
    PMF.pure ⟨some site.2.choose_spec.2.choose, site.2.choose_spec.2.choose_spec⟩
  have comparison : ∀
      (sourceProfile : Profile (information setup leaks bounds watcher).behavioralSignature)
      (targetProfile : Profile model.behavioralSignature),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : (information setup leaks bounds watcher).InformationSite who)
        (action : model.Choice who (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        ∀ history : (information setup leaks bounds watcher).InformationHistory who site.1,
          expect (model.runBehavioralFrom
            (Profile.update targetProfile who
              ((targetProfile who).commit (restriction.site who site).1 action))
            (2 * count + 1 - depth who (restriction.site who site))
            (restriction.history history.1)) (fun final => utility final.state who) ≤
          expect ((information setup leaks bounds watcher).runBehavioralFrom
            (Profile.update sourceProfile who
              ((sourceProfile who).withLaw site.1 (comparator who site action)))
            (2 * count + 1 - depth who (restriction.site who site)) history.1)
              (fun final => utility final.state who) := by
    intro sourceProfile targetProfile paired who site action extra history
    have sameLaw := replay_extra_continuation_law setup leaks bounds watcher reveals observer
      openable sourceProfile targetProfile paired who site action extra
        (comparator who site action) history
    have sameValue := congrArg (fun law => expect law (fun state => payoff state who)) sameLaw
    simp only [expect_map] at sameValue
    rw [sourceClock who site history] at sameValue
    exact sameValue.le
  let _ := Fintype.ofFinite (replayed.protocol initial count service).History
  obtain ⟨target, targetTerminal, agrees, _beliefs, historyLaw, _joint⟩ :=
    restriction.sequentialEquilibrium_extends_of_comparator
      (retained.decisionInformationAntichain initial count service)
      sourceCertificate targetCertificate
      (replayed.uniformAssessment initial count service)
      (replayed.uniform_fullyMixed initial count service)
      (replayed.decisionRecall initial count service)
      (fun who site => depth who (restriction.site who site))
      (fun who site => clock who (restriction.site who site))
      (fun who history => utility history.state who)
      (fun who history => utility history.state who) (fun _ _ => rfl)
      comparator (fun sourceProfile targetProfile paired who site action extra history => by
        rw [restriction.runBehavioralTerminalFrom_history_eq_remaining targetCertificate
            targetBounded _ (clock who (restriction.site who site)),
          restriction.runBehavioralTerminalFrom_eq_remaining sourceCertificate targetBounded _
            (clock who (restriction.site who site))]
        exact comparison sourceProfile targetProfile paired who site action extra history)
      source sourceTerminal
  rw [InformationModel.runBehavioralTerminalFrom_initHistory _
      sourceCertificate _ sourceBounded,
    InformationModel.runBehavioralTerminalFrom_initHistory _
      targetCertificate _ targetBounded] at historyLaw
  exact ⟨target, (target.isSequentialEquilibrium_iff_truncated_of_bounded model _
    targetCertificate targetBounded _).mp targetTerminal, agrees, historyLaw⟩

end Vegas
