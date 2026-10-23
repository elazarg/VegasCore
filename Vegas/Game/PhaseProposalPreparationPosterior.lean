/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalReferenceWord
import Vegas.Game.PhaseProposalRepairLikelihood
import GameTheoryExtensions.Analysis.Protocol.ProjectedBeliefTransport

/-! # Uniform posterior bounds for generated foreign preparation failures

The initialized finite game is fixed first. The ordinary response floor is
chosen before the bad rate and free source weights. Each bad history has an
actual repair in the same full observer fiber, so an existential counterpart
suffices; no injective repair or replacement prior is introduced.
-/

noncomputable section


namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "protocol" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds)
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler
local notation "model" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler

open Classical in
/-- At every positive FULL native decision fiber, a designated foreign
owner's generated bad preparation has uniformly small actual Bayes mass.
Chance/length constants precede all rates; the response floor precedes bad
noise, source pins and free source weights. -/
theorem exists_phaseProposal_generatedPreparation_posterior_bound
    [Fintype setup.proposalRecoveryProtocol.History]
    [(app).FiniteNature initial scheduler]
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (finite : setup.program.FiniteBindingTypes) :
    ∃ (chance : ℝ) (length : Nat), 0 < chance ∧ chance ≤ 1 ∧
      ∀ (floor : ℝ) (floorPositive : 0 < floor) (floorBounded : floor ≤ 1),
      ∀ (rates : PhaseProposalRates), 0 < rates.waiting.val → rates.waiting.val < 1 →
        0 < rates.slots.val → 0 < rates.aliases.val →
      ∃ lower : ℝ, 0 < lower ∧ lower ≤ 1 ∧
        ∀ (bad : Set.Icc (0 : ℝ) 1), 0 < bad.val → bad.val ≤ 1 / 2 →
        ∀ (pins : (pool : setup.ProposalRecoveryValuePool) →
            Option (PMF (setup.ProposalRecoveryPoolPart pool)))
          (weights : (pool : setup.ProposalRecoveryValuePool) →
            PMF (setup.ProposalRecoveryPoolPart pool))
          (assessment : (model).BehavioralAssessment),
          assessment.strategy = phaseProposalReferenceStrategy setup mode runtime leaks bounds plan
            initial horizon scheduler
            (setup.proposalRecoveryPooledDomainLaw finite floor floorPositive.le floorBounded
              pins weights) { rates with badPreparation := bad } →
          InformationModel.BehavioralAssessment.IsBayesConsistent (model) assessment
            ((menu).decisionInformationAntichain initial horizon
            scheduler) →
        ∀ (observer owner : Player), observer ≠ owner →
        ∀ (site : (model).InformationSite observer),
          0 < (model).informationMass assessment.strategy observer site →
          (∑ history : (model).InformationHistory observer site.1 with
            PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial horizon
              scheduler owner history.val,
            (assessment.belief observer site history).toReal) ≤
            (Fintype.card (protocol).History : ℝ) * bad.val /
              (chance * lower ^ length) := by
  classical
  obtain ⟨chance, chancePositive, chanceBounded, chanceLower⟩ :=
    PhaseProposal.exists_transitionMass_floor runtime leaks bounds initial horizon scheduler
  obtain ⟨length, lengthBound⟩ :=
    exists_phaseProposal_recall_length_bound setup mode runtime leaks bounds plan horizon scheduler
  refine ⟨chance, length, chancePositive, chanceBounded, ?_⟩
  intro floor floorPositive floorBounded rates waiting waitingBelow slots aliases
  let fixedRates := rates.ordinary
  obtain ⟨lower, lowerPositive, lowerBounded, lowerAt⟩ :=
    exists_phaseProposalPooled_response_floor setup mode runtime leaks bounds plan complete covered
      maximal finite floor floorPositive floorBounded fixedRates waiting waitingBelow slots aliases
        horizon scheduler
  refine ⟨lower, lowerPositive, lowerBounded, ?_⟩
  intro bad badPositive badSmall pins weights assessment prescribed bayes observer owner different
    site positive
  let values := setup.proposalRecoveryPooledDomainLaw finite floor floorPositive.le floorBounded
    pins weights
  let actualRates : PhaseProposalRates := { rates with badPreparation := bad }
  have fullValues : ∀ who key, FullSupport (values who key) :=
    setup.proposalRecoveryPooledDomainLaw_fullSupport finite floor floorPositive floorBounded
      pins weights
  have actualLower := lowerAt bad badPositive badSmall pins weights
  change ∀ (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (_trace : (protocol).Trace (some ⟨remaining, some owner, execution⟩))
    (response : PhaseProposal.Response runtime leaks bounds owner (execution.recall owner)
      (execution.observe app owner)),
    phaseProposalResponsePrepared setup mode runtime leaks response.val →
      lower ≤ (phaseProposalReferenceResponses setup mode runtime leaks bounds plan values
        actualRates owner (execution.recall owner) (execution.observe app owner)
          response).toReal at actualLower
  let ratio := bad.val / (chance * lower ^ length)
  have ratioNonnegative : 0 ≤ ratio :=
    div_nonneg bad.property.1 (mul_nonneg chancePositive.le (pow_nonneg lowerPositive.le _))
  have massFinite : (model).informationMass assessment.strategy observer site ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((model).informationMass_le_one assessment.strategy observer site
        ((menu).decisionInformationAntichain initial horizon scheduler observer site))
  have massPositive : 0 < ((model).informationMass assessment.strategy observer site).toReal :=
    ENNReal.toReal_pos positive.ne' massFinite
  have one (history : (model).InformationHistory observer site.1)
      (badHistory : PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial
        horizon scheduler owner history.val) :
      (assessment.belief observer site history).toReal ≤ ratio := by
    let inputs := setup.initialLaw.map encodeInputs
    have initialEq : inputs.map (PhaseRuntimeState.initial plan) = initial := by
      exact PMF.map_comp _ _ _
    have repair := PhaseProposal.repair_information_history runtime leaks bounds plan inputs
      horizon scheduler covered (serviceGraph_revealRelaxedOrdered setup mode) owner observer
        different
    rw [initialEq] at repair
    obtain ⟨image, words, originalControl, imageControl, originalState, imageState, _originalActor,
      _imageActor, _immutable, external, prepared⟩ := repair site history
    have originalWord := phaseProposalGenerated_owner_word_upper setup mode runtime leaks bounds
      plan horizon scheduler complete covered maximal values fullValues actualRates waiting
        waitingBelow slots badPositive (by dsimp only [actualRates]; linarith) owner history.val
          badHistory
    have repairedWord : lower ^ length ≤ (model).ownPlayReachProbability
        (phaseProposalReferenceStrategy setup mode runtime leaks bounds plan initial horizon
          scheduler values actualRates owner) ((model).ownPlay owner image.val.trace) := by
      rcases image with ⟨⟨state, imageTrace⟩, imageInfo⟩
      change state = some imageControl at imageState
      subst state
      exact phaseProposalRepaired_owner_word_lower setup mode runtime leaks bounds plan horizon
        scheduler values actualRates lower lowerPositive lowerBounded actualLower length
          lengthBound owner originalControl.execution imageControl imageTrace prepared
            (congrArg Prod.fst external)
    rw [← prescribed] at originalWord repairedWord
    have reach := PhaseProposal.historyReach_le_of_designated_word runtime leaks bounds initial
      horizon scheduler assessment.strategy owner history.val image.val words chance chancePositive
        (chanceLower image.val) bad.val bad.property.1 originalWord lower lowerPositive length
          repairedWord
    have imageBound : ((model).historyReachWeight assessment.strategy image.val).toReal ≤
        ((model).informationMass assessment.strategy observer site).toReal :=
      ENNReal.toReal_mono massFinite
        ((model).historyReachWeight_le_informationMass assessment site image)
    have total := reach.trans (mul_le_mul_of_nonneg_left imageBound ratioNonnegative)
    rw [InformationModel.belief_toReal_eq_div bayes positive history, div_le_iff₀ massPositive]
    simpa only [ratio, mul_comm] using total
  have sumBound :
      (∑ history : (model).InformationHistory observer site.1 with
        PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial horizon
          scheduler owner history.val, (assessment.belief observer site history).toReal) ≤
      ∑ history : (model).InformationHistory observer site.1 with
        PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial horizon
          scheduler owner history.val, ratio :=
    Finset.sum_le_sum fun history member => one history (Finset.mem_filter.mp member).2
  have count : (Finset.univ.filter fun history : (model).InformationHistory observer site.1 =>
      PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial horizon scheduler
        owner history.val).card ≤ Fintype.card (protocol).History :=
    (Finset.card_le_univ _).trans (Fintype.card_subtype_le _)
  calc
    _ ≤ _ := sumBound
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card (protocol).History : ℝ) * ratio :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast count) ratioNonnegative
    _ = _ := by dsimp only [ratio]; ring

open Classical in
/-- The same pre-bad response floor bounds the union over all foreign owners. -/
theorem exists_phaseProposal_foreignPreparation_posterior_bound
    [Fintype setup.proposalRecoveryProtocol.History]
    [(app).FiniteNature initial scheduler]
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (finite : setup.program.FiniteBindingTypes) :
    ∃ (chance : ℝ) (length : Nat), 0 < chance ∧ chance ≤ 1 ∧
      ∀ (floor : ℝ) (floorPositive : 0 < floor) (floorBounded : floor ≤ 1),
      ∀ (rates : PhaseProposalRates), 0 < rates.waiting.val → rates.waiting.val < 1 →
        0 < rates.slots.val → 0 < rates.aliases.val →
      ∃ lower : ℝ, 0 < lower ∧ lower ≤ 1 ∧
        ∀ (bad : Set.Icc (0 : ℝ) 1), 0 < bad.val → bad.val ≤ 1 / 2 →
        ∀ (pins : (pool : setup.ProposalRecoveryValuePool) →
            Option (PMF (setup.ProposalRecoveryPoolPart pool)))
          (weights : (pool : setup.ProposalRecoveryValuePool) →
            PMF (setup.ProposalRecoveryPoolPart pool))
          (assessment : (model).BehavioralAssessment),
          assessment.strategy = phaseProposalReferenceStrategy setup mode runtime leaks bounds plan
            initial horizon scheduler
            (setup.proposalRecoveryPooledDomainLaw finite floor floorPositive.le floorBounded
              pins weights) { rates with badPreparation := bad } →
          InformationModel.BehavioralAssessment.IsBayesConsistent (model) assessment
            ((menu).decisionInformationAntichain initial horizon
            scheduler) →
        ∀ (observer : Player),
        ∀ (site : (model).InformationSite observer),
          0 < (model).informationMass assessment.strategy observer site →
          (∑ history : (model).InformationHistory observer site.1 with
            (∃ owner : Player, observer ≠ owner ∧
              PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial horizon
                scheduler owner history.val),
            (assessment.belief observer site history).toReal) ≤
            (Fintype.card Player : ℝ) *
              ((Fintype.card (protocol).History : ℝ) * bad.val /
              (chance * lower ^ length)) := by
  classical
  obtain ⟨chance, length, chancePositive, chanceBounded, designated⟩ :=
    exists_phaseProposal_generatedPreparation_posterior_bound setup mode runtime leaks bounds plan
      horizon scheduler complete covered maximal finite
  refine ⟨chance, length, chancePositive, chanceBounded, ?_⟩
  intro floor floorPositive floorBounded rates waiting waitingBelow slots aliases
  obtain ⟨lower, lowerPositive, lowerBounded, designated⟩ :=
    designated floor floorPositive floorBounded rates waiting waitingBelow slots aliases
  refine ⟨lower, lowerPositive, lowerBounded, ?_⟩
  intro bad badPositive badSmall pins weights assessment prescribed bayes observer site positive
  let cost := (Fintype.card (protocol).History : ℝ) * bad.val /
    (chance * lower ^ length)
  have costNonnegative : 0 ≤ cost := by
    dsimp only [cost]
    positivity
  let badAt (owner : Player) (history : (model).InformationHistory observer site.1) : Prop :=
    observer ≠ owner ∧ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial
      horizon scheduler owner history.val
  let mass (history : (model).InformationHistory observer site.1) :=
    (assessment.belief observer site history).toReal
  have ownerBound (owner : Player) :
      (∑ history : (model).InformationHistory observer site.1 with badAt owner history,
        mass history) ≤ cost := by
    by_cases different : observer ≠ owner
    · have filters :
          (Finset.univ.filter fun history : (model).InformationHistory observer site.1 =>
            badAt owner history) =
          (Finset.univ.filter fun history : (model).InformationHistory observer site.1 =>
            PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial horizon
              scheduler owner history.val) := by
        apply Finset.filter_congr
        intro history _
        exact ⟨fun present => present.2, fun present => ⟨different, present⟩⟩
      rw [filters]
      exact designated bad badPositive badSmall pins weights assessment prescribed bayes observer
        owner different site positive
    · simpa only [badAt, different, false_and, Finset.filter_false, Finset.sum_empty] using
        costNonnegative
  have coveredAt (history : (model).InformationHistory observer site.1) :
      (if ∃ owner : Player, badAt owner history then mass history else 0) ≤
        ∑ owner : Player, if badAt owner history then mass history else 0 := by
    by_cases existsOwner : ∃ owner : Player, badAt owner history
    · obtain ⟨owner, witnessed⟩ := existsOwner
      rw [ite_eq_left ⟨owner, witnessed⟩]
      have selected := Finset.single_le_sum
        (f := fun player : Player => if badAt player history then mass history else 0)
        (s := Finset.univ) (a := owner)
        (fun player _ => by split_ifs <;> positivity) (Finset.mem_univ owner)
      simpa only [ite_eq_left witnessed] using selected
    · rw [ite_eq_right existsOwner]
      exact Finset.sum_nonneg fun owner _ => by
        split_ifs <;> positivity
  calc
    _ = ∑ history : (model).InformationHistory observer site.1,
        if ∃ owner : Player, badAt owner history then mass history else 0 := by
      exact Finset.sum_filter _ _
    _ ≤ ∑ history : (model).InformationHistory observer site.1,
        ∑ owner : Player, if badAt owner history then mass history else 0 :=
      Finset.sum_le_sum fun history _ => coveredAt history
    _ = ∑ owner : Player,
        ∑ history : (model).InformationHistory observer site.1 with badAt owner history,
          mass history := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun owner _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ _owner : Player, cost := Finset.sum_le_sum fun owner _ => ownerBound owner
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; rfl

end Vegas
