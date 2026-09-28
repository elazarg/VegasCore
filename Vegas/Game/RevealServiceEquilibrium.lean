/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceConsistency
import Vegas.Game.RevealServiceOwnerIncentives
import Vegas.Game.RevealServiceLaw
import GameTheoryExtensions.Analysis.Protocol.SequentialOneShot
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Sequential equilibrium compilation for revelation sequences

Every sequential equilibrium of the original reveal-only source is preserved
by the fixed compiler into the restricted service. Native histories retain
private replay aliases, passive observations and all service steps. One common
Bayes perturbation sequence supplies the beliefs; the posterior one-shot
principle gives optimality against whole continuation policies.

The result concerns this compliant response menu. Extending to unrestricted
responses and collectible sanctions is a separate enforcement edge. Finiteness
of source histories follows from the source information lemmas; the explicit
instances below only supply the finite sums in the standard SE definition.
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
  [Finite (setup.executionProtocol admission).History]
  [∀ who (site : (setup.informationModel admission).InformationSite who),
    Fintype ((setup.informationModel admission).InformationHistory who site.1)]

/-- Reporting is forced by this restricted menu, at every local input. Its
optimality therefore imposes no assumption on the reporting player's utility. -/
theorem watcher_choice_subsingleton (info : (application setup leaks).Info) :
    Subsingleton ((information setup leaks bounds watcher).Choice watcher info) := by
  classical
  refine ⟨fun first second => Subtype.ext ?_⟩
  cases info with
  | none => exact first.2.trans second.2.symm
  | some data =>
      obtain ⟨past, view⟩ := data
      have deterministic : ∃ response,
          (application setup leaks).reportFirstUnpublished past view = FinDist.pure response := by
        unfold ReactiveApplication.reportFirstUnpublished
        split <;> exact ⟨_, rfl⟩
      obtain ⟨response, chosen⟩ := deterministic
      obtain ⟨left, leftMember, leftEq⟩ := first.2
      obtain ⟨right, rightMember, rightEq⟩ := second.2
      have leftChoice : left = response := by
        simpa only [menu, ↓reduceIte, chosen, FinDist.mem_supportFinset,
          FinDist.mem_support_pure, Set.mem_singleton_iff] using leftMember
      have rightChoice : right = response := by
        simpa only [menu, ↓reduceIte, chosen, FinDist.mem_supportFinset,
          FinDist.mem_support_pure, Set.mem_singleton_iff] using rightMember
      exact leftEq.trans ((congrArg some (leftChoice.trans rightChoice.symm)).trans rightEq.symm)

include reveals observer openable in
/-- The complete typed source state and utility vector are preserved jointly.
The target game, menus, utility and strategy compiler are fixed before choosing
the source equilibrium. Only the consistent belief completion is existential. -/
theorem source_sequential_equilibrium_preserved
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (setup.decision_antichain admission)
      (fun who site => source.continuationContext site
        (fun final => (setup.protocolReadout final.state).elim 0 (fun state => utility state who))
        (instructionCount setup.program + 1))) :
    let extended := bounds.withInitialValues (initialLaw setup)
    let model := information setup leaks extended watcher
    let responses := menu setup leaks extended watcher
    let antichain := (responses.decisionRecall (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).antichain
    ∃ target : model.BehavioralAssessment,
      target.strategy = compiledProfile setup leaks extended watcher
        (setup.decodeBehavioralProfile admission source.strategy) 0 le_rfl (by norm_num) ∧
      target.IsSequentialEquilibriumFor antichain (fun who site =>
        target.continuationContext site
          (fun final => baseUtility setup leaks utility final.state who)
          (2 * horizon setup watcher + 1)) ∧
      (model.runBehavioral target.strategy (2 * horizon setup watcher + 1)).map
          (fun final => (sourceReadout setup leaks final.state,
            baseUtility setup leaks utility final.state)) =
        ((setup.informationModel admission).runBehavioral source.strategy
          (instructionCount setup.program + 1)).map
            (fun final => (setup.protocolReadout final.state,
              fun who => (setup.protocolReadout final.state).elim 0
                (fun state => utility state who))) := by
  classical
  intro extended model responses antichain
  obtain ⟨target, strategy, consistent, beliefs⟩ := exists_compiled_consistent setup leaks bounds
    watcher reveals observer openable admission source equilibrium.2
  let bound := 2 * horizon setup watcher + 1
  let depth (who : Player) (site : model.InformationSite who) :=
    decisionDepth setup leaks watcher who site.1
  have clock (who : Player) (site : model.InformationSite who) :
      InformationModel.InformationSite.CommonDepth model site (depth who site) :=
    menu_common_decision_depth setup leaks responses watcher reveals observer who site
  have within (who : Player) (site : model.InformationSite who) : depth who site ≤ bound := by
    obtain ⟨history, running, _action⟩ := site.2
    have before : history.1.trace.length < bound := by
      by_contra late
      exact running (responses.bounded (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) history.1.state history.1.trace (by omega))
    rw [clock who site history] at before
    exact before.le
  have rational : target.IsSequentiallyRational fun who site =>
      target.continuationContext site
        (fun final => baseUtility setup leaks utility final.state who)
        (bound - depth who site) := by
    apply consistent.sequentiallyRational_of_localOptimal
      (responses.decisionRecall (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher)) bound
      (fun who final => baseUtility setup leaks utility final.state who) depth clock within
    intro who site _before law
    by_cases watches : who = watcher
    · subst who
      let _ := watcher_choice_subsingleton setup leaks extended watcher site.1
      obtain ⟨choice, _supported⟩ := law.support_nonempty
      have same : law = target.strategy watcher site.1 :=
        (FinDist.eq_pure_of_subsingleton law choice).trans
          (FinDist.eq_pure_of_subsingleton _ choice).symm
      rw [same, InformationModel.BehavioralPolicy.withLaw_eq_self]
    · obtain ⟨history, _running, _action⟩ := site.2
      have active := InformationModel.InformationSite.active model site history
      obtain ⟨event, owned, length, supported⟩ := owner_history_supported setup leaks extended
        watcher who reveals watches history.1 active
      let reference := responses.uniformPolicy (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher)
      obtain ⟨sourceSite, sourceView⟩ := owner_source_site setup leaks extended watcher who reveals
        observer openable admission reference event owned history.1 supported
      have currentDepth : depth who site = blockOffset event.val + 2 * event.val + 3 :=
        (clock who site history).symm.trans length
      have nativeClock : InformationModel.InformationSite.CommonDepth model site
          (blockOffset event.val + 2 * event.val + 3) := by
        simpa only [currentDepth] using clock who site
      have belief := beliefs who site reference event owned history supported length sourceSite
        sourceView
      rw [currentDepth]
      exact owner_local_optimal setup leaks bounds watcher reveals observer openable admission
        source target strategy who event owned site nativeClock reference history supported
        sourceSite sourceView belief (fun state => utility state who)
        (equilibrium.1 who sourceSite) law
  have targetEquilibrium : target.IsSequentialEquilibriumFor antichain (fun who site =>
      target.continuationContext site
        (fun final => baseUtility setup leaks utility final.state who) bound) :=
    (target.sequentialEquilibrium_remaining_iff model antichain bound
      (responses.bounded (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher))
      depth clock (fun who final => baseUtility setup leaks utility final.state who)).mp
      ⟨rational, consistent⟩
  refine ⟨target, strategy, targetEquilibrium, ?_⟩
  rw [strategy]
  exact compiled_profile_joint_utility_law setup leaks bounds watcher reveals observer openable
    admission source.strategy 0 le_rfl (by norm_num) utility

end Vegas
