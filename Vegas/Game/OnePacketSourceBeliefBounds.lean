module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketBaseAssembly

@[expose] public section

/-! # Source posterior convergence of assembled native profiles -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Public : Type*} {signal : State L setup.context → Public}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler

local instance sourceBeliefHistoryFintype : Fintype
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon scheduler).History :=
  (bounds.onePacketMenu timeouts leaks).historyFintype (initialLaw setup) horizon scheduler

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
      (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler bounds.candidateCount p))
    (target : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence
      scale positive le_one weights target)
    (mixed : ∀ n, (target n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (target n)
      ((bounds.onePacketMenu timeouts leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ∀ {past : List (application setup timeouts leaks).PlayerEntry}
          {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past,
            view)),
        ∀ {event : (graph setup).EventId},
          view.application.publicView.ownTurn? who = some event →
        ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who
          site.1),
        ∑' point,
          |((((target n).belief who site).map
                (replayProjection setup timeouts leaks bounds horizon scheduler
                  (projectedSite setup timeouts leaks decision) site atSite rfl)) point).toReal -
            ((sequence n).belief who (projectedSite setup timeouts leaks decision) point).toReal| ≤
              error n := by
  let eligible := fun who (site : (N).InformationSite who) =>
    ¬ Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) ∧
      ¬ Vegas.OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) ∧
      ∃ (past : List (application setup timeouts leaks).PlayerEntry)
        (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId),
        site.1 = some (past, view) ∧ view.application.publicView.ownTurn? who = some event
  let estimate := fun n who (site : (N).InformationSite who) error =>
    ∀ (past : List (application setup timeouts leaks).PlayerEntry)
      (view : (application setup timeouts leaks).PlayerView) (atSite : site.1 = some (past, view))
      (event : (graph setup).EventId), view.application.publicView.ownTurn? who = some event →
      ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who
        site.1),
      ∑' point,
        |((((target n).belief who site).map (replayProjection setup timeouts leaks bounds horizon
            scheduler (projectedSite setup timeouts leaks decision) site atSite rfl))
              point).toReal -
          ((sequence n).belief who (projectedSite setup timeouts leaks decision) point).toReal| ≤
            error
  obtain ⟨error, limit, uniform⟩ := exists_uniform_of_sites setup timeouts leaks bounds horizon
    scheduler estimate
    (fun _ _ _ _ _ grows holds past view atSite event turn decision =>
      (holds past view atSite event turn decision).trans grows) eligible
    (fun who site good => by
      obtain ⟨notFree, notOwing, past, view, event, atSite, turn⟩ := good
      have forced := forcedAgent_of_not_free setup timeouts leaks bounds (initialLaw setup)
        horizon scheduler notFree
      have debtFree := siteDebtFree_of_not_owing setup timeouts leaks bounds horizon
        scheduler
        notOwing
      have decision := projectedDecision_of_forcedAgent (timeouts := timeouts) wellFormed forced
        atSite turn debtFree
      let inputs : OnePacketBeliefInputs setup timeouts leaks bounds horizon scheduler
        sequence
          target site (projectedSite setup timeouts leaks decision) atSite rfl :=
        { toOnePacketCounterpartInputs :=
          OnePacketCounterpartInputs.ofBindingRepairs (timeouts := timeouts) wellFormed
            independent observable sourceMixed positive le_one scaleEq covers coversInputs capacity
            weights assembled mixed notFree notOwing atSite turn
          toOnePacketOwnInputs := OnePacketOwnInputs.ofAssembled (timeouts :=
            timeouts) wellFormed sourceMixed
            (2 * horizon + 2) scaleEq covers coversInputs capacity assembled notFree notOwing
            atSite rfl turn }
      have convergence := onePacket_beliefConverges setup timeouts leaks bounds horizon
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
