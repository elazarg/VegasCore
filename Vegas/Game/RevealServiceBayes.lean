/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceMixing
import Vegas.Game.RevealServiceOwnerInformation
import Interaction.ReactiveOwnPlay
import GameTheoryExtensions.Analysis.Protocol.ReadoutBayesProjection

/-! # Actual source-state posteriors in the restricted revelation service

A focal selector chooses recorded replay aliases without changing any source
choice. Its actual checkpoint law and information reconstruction identify the
source information event. Decision recall then removes the selector from the
Bayes posterior. No information-fiber or belief correspondence is assumed.
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
  (admission : CommitmentInterface setup.program)

include reveals observer openable in
/-- A source site recovered from an actual owner checkpoint has the source
instruction depth corresponding to that checkpoint. -/
theorem owner_source_common_depth
    (who : Player)
    (reference : Profile
      (information setup leaks (bounds.withInitialValues (initialLaw setup))
        watcher).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (history : (protocol setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).History)
    (supported : history ∈
      ((information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).runBehavioral
        reference (blockOffset event.val + 2 * event.val + 3)).support)
    (sourceSite : (setup.informationModel admission).InformationSite who)
    (sourceView : sourceSite.1 =
      setup.protocolObserve who (prefixReadout setup leaks event.val history.state)) :
    InformationModel.InformationSite.CommonDepth (setup.informationModel admission) sourceSite
      (event.val + 1) := by
  obtain ⟨sourceHistory, sourceSupport, same, _active, running⟩ := owner_source_history setup
    leaks (bounds.withInitialValues (initialLaw setup)) watcher who reveals observer openable
      admission reference event owned history supported
  have observed : (setup.informationModel admission).infoOf who sourceHistory.trace =
      sourceSite.1 := by
    exact (setup.protocol_info admission who sourceHistory.trace).trans
      ((congrArg (setup.protocolObserve who) same).trans sourceView.symm)
  have length := InformationModel.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
      (setup.informationModel admission)
      (setup.revealReference reveals admission).strategy (event.val + 1)
      (setup.executionProtocol admission).initHistory sourceHistory sourceSupport
  have exactLength : sourceHistory.trace.length = event.val + 1 := by
    simpa only [ExecutionProtocol.initHistory, Trace.length, Nat.zero_add] using
      length.resolve_left running
  intro other
  exact (setup.common_decision_depth admission who sourceSite other).trans
    ((setup.common_decision_depth admission who sourceSite ⟨sourceHistory, observed⟩).symm.trans
      exactLength)

/-- The native fully mixed Bayes posterior has exactly the original source
state posterior at the recovered source site, for every private alias fiber. -/
theorem owner_bayes_state [setup.FiniteInitialLaw]
    (source : (setup.informationModel admission).BehavioralAssessment)
    (sourceMixed : source.IsFullyMixed)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1) (positive : 0 < weight)
    (who : Player)
    (site : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).InformationSite who)
    (reference : Profile
      (information setup leaks (bounds.withInitialValues (initialLaw setup))
        watcher).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (history : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).InformationHistory who site.1)
    (supported : history.1 ∈
      ((information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).runBehavioral
        reference (blockOffset event.val + 2 * event.val + 3)).support)
    (length : history.1.trace.length = blockOffset event.val + 2 * event.val + 3)
    (sourceSite : (setup.informationModel admission).InformationSite who)
    (sourceView : sourceSite.1 =
      setup.protocolObserve who (prefixReadout setup leaks event.val history.1.state)) :
    let responses := menu setup leaks (bounds.withInitialValues (initialLaw setup)) watcher
    let antichain := (responses.decisionRecall (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).decisionInformationAntichain
    let compiled := InformationModel.BehavioralAssessment.ofStrategy
      (compiledProfile setup leaks (bounds.withInitialValues (initialLaw setup)) watcher
        (setup.decodeBehavioralProfile admission source.strategy) weight nonnegative small)
    let mixed := compiledProfile_fullyMixed setup leaks bounds watcher reveals observer openable
      admission source sourceMixed weight nonnegative small positive
    ((InformationModel.bayesAssessment _ compiled.strategy mixed antichain).belief who site).map
        (fun native => prefixReadout setup leaks event.val native.1.state) =
      ((InformationModel.bayesAssessment _ source.strategy sourceMixed
          (setup.decision_antichain admission)).belief who sourceSite).map
        (fun original => original.1.state) := by
  classical
  intro responses antichain compiled mixed
  let extended := bounds.withInitialValues (initialLaw setup)
  let model := information setup leaks extended watcher
  let decoded := setup.decodeBehavioralProfile admission source.strategy
  have ordinary : who ≠ watcher := fun same => observer event (same ▸ owned)
  obtain ⟨past, view, info⟩ : ∃ past view, site.1 = some (past, view) := by
    cases observed : site.1 with
    | none =>
        obtain ⟨_, _, response, member⟩ := site.2
        rw [observed] at member
        cases member
    | some input => exact ⟨input.1, input.2, rfl⟩
  let selected := focalProfile setup leaks extended watcher decoded weight nonnegative small
    who past
  have encoded : (fun actor => setup.toProtocolBehavioralPolicy admission actor (decoded actor)
      (((setup.behavioralPolicyEquiv admission actor).symm (source.strategy actor)).2)) =
        source.strategy := by
    funext actor
    exact (setup.behavioralPolicyEquiv admission actor).apply_symm_apply (source.strategy actor)
  have unmarked : (model.runBehavioral selected
      (blockOffset event.val + 2 * event.val + 3)).map
        (fun current => prefixReadout setup leaks event.val current.state) =
      ((setup.informationModel admission).runBehavioral source.strategy (event.val + 1)).map
        History.state := by
    rw [menu_owner_readout setup leaks responses watcher who reveals selected event owned]
    have law := focal_behavioral_prefix_law setup leaks bounds watcher reveals observer openable
      admission decoded
      (fun actor => ((setup.behavioralPolicyEquiv admission actor).symm
        (source.strategy actor)).2) weight nonnegative small who ordinary past event.val
        event.isLt.le
    rw [encoded] at law
    exact law
  have marked := model.informationReadout_law_of_fiber (setup.informationModel admission)
    selected who site (blockOffset event.val + 2 * event.val + 3) source.strategy sourceSite
    (event.val + 1) (fun current => prefixReadout setup leaks event.val current.state)
    History.state (fun state => setup.protocolObserve who state = sourceSite.1) unmarked
    (by
      intro current reached
      constructor
      · intro same
        rw [sourceView]
        apply owner_information_projects setup leaks extended watcher who reveals observer openable
          selected reference event owned current history.1 reached supported
        exact same.trans history.2.symm
      · intro same
        have equality := owner_focal_information setup leaks extended watcher who reveals observer
          openable decoded weight nonnegative small past view selected reference
          (focalProfile_decode setup leaks extended watcher decoded weight nonnegative small
            who ordinary past) event owned current history.1 reached supported
          (history.2.trans info) (same.trans sourceView)
        exact equality.trans history.2)
    (by intro current _; exact (setup.protocol_info admission who current.trace) ▸ Iff.rfl)
  have clock : InformationModel.InformationSite.CommonDepth model site
      (blockOffset event.val + 2 * event.val + 3) := by
    intro current
    exact (menu_common_decision_depth setup leaks responses watcher reveals observer who site
      current).trans ((menu_common_decision_depth setup leaks responses watcher reveals observer
        who site history).symm.trans length)
  have sourceClock := owner_source_common_depth setup leaks bounds watcher reveals observer
    openable admission who reference event owned history.1 supported sourceSite sourceView
  exact model.bayesBelief_readout_at_depth_of_focal_selector (setup.informationModel admission)
    selected who site _ clock source.strategy sourceSite _ sourceClock _ _ marked compiled.strategy
    (fun other different => (focalProfile_other setup leaks extended watcher decoded weight
      nonnegative small who past other different).symm)
    (responses.commonPlayerReachAt _ _ _ compiled.strategy who site)
    (responses.commonPlayerReachAt _ _ _ selected who site)
    (antichain who site) (setup.decision_antichain admission who sourceSite)
    (model.informationMass_pos_of_fullSupport compiled.strategy mixed who site)
    ((setup.informationModel admission).informationMass_pos_of_fullSupport source.strategy
      sourceMixed who sourceSite)

end Vegas
