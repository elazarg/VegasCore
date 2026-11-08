/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBaseAssembly

/-! # Irregular histories under assembled native profiles -/

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

local instance irregularBeliefHistoryFintype : Fintype
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon scheduler).History :=
  (bounds.onePacketMenu timeouts leaks).historyFintype (initialLaw setup) horizon scheduler

open Classical in
/-- One vanishing error bounds irregular-history belief mass at every debt-free forced own turn
along the supplied fully mixed Bayes assessment sequence. -/
theorem irregular_belief_bounds_of_assembled
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
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
    ∃ drift : ℕ → ℝ, Tendsto drift atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ∀ {past : List (application setup timeouts leaks).PlayerEntry}
          {view : (application setup timeouts leaks).PlayerView}, site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
          view.application.publicView.ownTurn? who = some event →
        expect ((target n).belief who site) (fun history =>
          if RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
            history.1.trace then (0 : ℝ) else 1) ≤ drift n := by
  let good := fun who (site : (N).InformationSite who) =>
    ¬ Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) ∧
      ¬ Vegas.OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) ∧
      ∃ (past : List (application setup timeouts leaks).PlayerEntry)
        (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId),
        site.1 = some (past, view) ∧ view.application.publicView.ownTurn? who = some event
  obtain ⟨drift, limit, uniform⟩ := exists_uniform_of_sites setup timeouts leaks bounds horizon
    scheduler
    (fun n who site error => expect ((target n).belief who site) (fun history =>
      if RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        history.1.trace
        then (0 : ℝ) else 1) ≤ error)
    (fun _ _ _ _ _ le bound => bound.trans le) good (fun who site eligible => by
      obtain ⟨notFree, notOwing, past, view, event, atSite, turn⟩ := eligible
      have inputs := OnePacketCounterpartInputs.ofBindingRepairs (timeouts := timeouts) wellFormed
        independent
        observable sourceMixed
        positive le_one scaleEq covers coversInputs capacity weights assembled mixed notFree
        notOwing atSite turn
      exact ⟨_, onePacket_irregularVanishes setup timeouts leaks bounds horizon scheduler
        mixed bayes
        inputs, fun _ => le_rfl⟩)
  exact ⟨drift, limit, fun n who site notFree notOwing past view atSite event turn =>
    uniform n who site ⟨notFree, notOwing, past, view, event, atSite, turn⟩⟩

end Vegas
