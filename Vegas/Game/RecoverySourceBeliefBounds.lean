/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBaseAssembly

/-! # Source posterior convergence of assembled native profiles -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Public : Type*} {signal : State L setup.context → Public}

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

local instance : Fintype ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
    horizon scheduler).History :=
  (bounds.onePacketMenu runtime leaks).historyFintype (initialLaw setup) horizon scheduler

open Classical in
/-- One vanishing error bounds the source posterior discrepancy at every debt-free forced own turn
along the supplied fully mixed Bayes assessment sequence. -/
theorem source_belief_bounds_of_assembled
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup runtime leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler bounds.candidateCount p))
    (target : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence
      scale positive le_one weights target)
    (mixed : ∀ n, (target n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (target n)
      ((bounds.onePacketMenu runtime leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ∀ {past : List (application setup runtime leaks).PlayerEntry}
          {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past,
            view)),
        ∀ {event : (graph setup).EventId},
          view.application.publicView.ownTurn? who = some event →
        ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who
          site.1),
        ∑' point,
          |((((target n).belief who site).map
                (replayProjection setup runtime leaks bounds horizon scheduler
                  (projectedSite setup runtime leaks decision) site atSite rfl)) point).toReal -
            ((sequence n).belief who (projectedSite setup runtime leaks decision) point).toReal| ≤
              error n := by
  let eligible := fun who (site : (N).InformationSite who) =>
    ¬ Vegas.FreeAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) ∧
      ¬ Vegas.OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) ∧
      ∃ (past : List (application setup runtime leaks).PlayerEntry)
        (view : (application setup runtime leaks).PlayerView) (event : (graph setup).EventId),
        site.1 = some (past, view) ∧ view.application.publicView.ownTurn? who = some event
  let estimate := fun n who (site : (N).InformationSite who) error =>
    ∀ (past : List (application setup runtime leaks).PlayerEntry)
      (view : (application setup runtime leaks).PlayerView) (atSite : site.1 = some (past, view))
      (event : (graph setup).EventId), view.application.publicView.ownTurn? who = some event →
      ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who
        site.1),
      ∑' point,
        |((((target n).belief who site).map (replayProjection setup runtime leaks bounds horizon
            scheduler (projectedSite setup runtime leaks decision) site atSite rfl))
              point).toReal -
          ((sequence n).belief who (projectedSite setup runtime leaks decision) point).toReal| ≤
            error
  obtain ⟨error, limit, uniform⟩ := exists_uniform_of_sites setup runtime leaks bounds horizon
    scheduler estimate
    (fun _ _ _ _ _ grows holds past view atSite event turn decision =>
      (holds past view atSite event turn decision).trans grows) eligible
    (fun who site good => by
      obtain ⟨notFree, notOwing, past, view, event, atSite, turn⟩ := good
      have forced := forcedAgent_of_not_free setup runtime leaks bounds (initialLaw setup)
        horizon scheduler notFree
      have debtFree := siteDebtFree_of_not_owing setup runtime leaks bounds horizon
        scheduler
        notOwing
      have decision := projectedDecision_of_forcedAgent (runtime := runtime) wellFormed forced
        atSite turn debtFree
      let inputs : OnePacketBeliefInputs setup runtime leaks bounds horizon scheduler
        sequence
          target site (projectedSite setup runtime leaks decision) atSite rfl :=
        { toOnePacketCounterpartInputs :=
          OnePacketCounterpartInputs.ofBindingRepairs (runtime := runtime) wellFormed
            independent observable sourceMixed positive le_one scaleEq covers coversInputs capacity
            weights assembled mixed notFree notOwing atSite turn
          toOnePacketOwnInputs := OnePacketOwnInputs.ofAssembled (runtime :=
            runtime) wellFormed sourceMixed
            (2 * horizon + 2) scaleEq covers coversInputs capacity assembled notFree notOwing
            atSite rfl turn }
      have convergence := onePacket_beliefConverges setup runtime leaks bounds horizon
        scheduler
        wellFormed sourceMixed sourceBayes mixed bayes atSite rfl forced turn inputs
      refine ⟨_, convergence, ?_⟩
      intro n otherPast otherView otherAt otherEvent _otherTurn otherDecision
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans otherAt))
      exact le_rfl)
  exact ⟨error, limit, fun n who site notFree notOwing past view atSite event turn decision =>
    uniform n who site ⟨notFree, notOwing, past, view, event, atSite, turn⟩ past view atSite event
      turn decision⟩

end Vegas
