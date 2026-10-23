/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalPooledFloor
import Vegas.Game.PhaseProposalOrdinaryRecorded
import Vegas.Game.PhaseProposalBadMass
import Vegas.Game.PhaseProposalGeneratedPreparation
import Interaction.ReactiveMenuLikelihood
import GameTheoryExtensions.Protocol.OwnPlayPrefix

/-! # The actual designated owner's reference response-word factors -/

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

/-- The complete owner factor is the indexed product at the original full
input of each actual response. Choice witnesses introduce no extra mass. -/
theorem phaseProposalReference_word_probability
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (owner : Player) (control : (app).Control)
    (trace : (protocol).Trace (some control)) :
    (model).ownPlayReachProbability
        (phaseProposalReferenceStrategy setup mode runtime leaks bounds plan initial horizon
          scheduler values rates owner) ((model).ownPlay owner trace) =
      ∏ index : Fin (control.execution.recall owner).length,
        (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates owner
          ((control.execution.recall owner).take index.val)
          (control.execution.recall owner)[index.val].beforeView
          (control.execution.recall owner)[index.val].action).toReal := by
  have word : (model).ownPlay owner trace =
      (app).recallOwnPlay (control.execution.recall owner) := by
    change ((menu).signals initial horizon scheduler).ownPlay owner trace = _
    rw [← (menu).ownPlay_toRawTrace initial horizon scheduler owner trace, (app).trace_ownPlay]
    rfl
  rw [word]
  change (model).ownPlayReachProbability
    ((menu).restrictPolicy initial horizon scheduler owner _) ((app).ownPlayFrom [] _) = _
  rw [(menu).ownPlayFrom_restrictPolicy initial horizon scheduler owner _
    (phaseProposalReferencePolicy_covered setup mode runtime leaks bounds plan values rates owner),
    (app).privateTranscriptFrom_product]
  simp only [List.nil_append]

/-- Uniform floors at actual callbacks give a complete designated word
floor; no bound is taken on any other owner's response probabilities. -/
theorem phaseProposalReference_word_lower_of_atoms
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (owner : Player) (control : (app).Control)
    (trace : (protocol).Trace (some control)) (lower : ℝ) (nonnegative : 0 ≤ lower)
    (atoms : ∀ index : Fin (control.execution.recall owner).length,
      lower ≤ (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates owner
        ((control.execution.recall owner).take index.val)
        (control.execution.recall owner)[index.val].beforeView
        (control.execution.recall owner)[index.val].action).toReal) :
    lower ^ (control.execution.recall owner).length ≤
      (model).ownPlayReachProbability
        (phaseProposalReferenceStrategy setup mode runtime leaks bounds plan initial horizon
          scheduler values rates owner) ((model).ownPlay owner trace) := by
  rw [phaseProposalReference_word_probability setup mode runtime leaks bounds plan horizon
    scheduler values rates owner control trace]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => lower)
      (fun _ _ => nonnegative) (fun index _ => atoms index)

/-- A fixed intrinsic game bounds chronological native response-word lengths
before choosing any reference probabilities. -/
theorem exists_phaseProposal_recall_length_bound
    [(app).FiniteNature initial scheduler] :
    ∃ length : Nat, ∀ (history : (protocol).History) (owner : Player),
      ((app).recallAt owner history.state).length ≤ length := by
  classical
  let size := fun coordinate : (protocol).History × Player =>
    ((app).recallAt coordinate.2 coordinate.1.state).length
  refine ⟨(Finset.univ : Finset ((protocol).History × Player)).sup size, ?_⟩
  intro history owner
  exact Finset.le_sup (f := size) (Finset.mem_univ (history, owner))

/-- The whole repair's persistent records discharge preparedness at EVERY
historical input, so the actual uniform local floor multiplies over the entire
designated response word. Past rare aliases and canceled attempts are retained. -/
theorem phaseProposalRepaired_owner_word_lower
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (lower : ℝ) (lowerPositive : 0 < lower)
    (lowerBounded : lower ≤ 1)
    (lowerAt : ∀ (remaining : Nat) (owner : Player) (execution : (app).Execution)
      (_trace : (protocol).Trace (some ⟨remaining, some owner, execution⟩))
      (response : PhaseProposal.Response runtime leaks bounds owner (execution.recall owner)
        (execution.observe app owner)),
      phaseProposalResponsePrepared setup mode runtime leaks response.val →
      lower ≤ (phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates
        owner (execution.recall owner) (execution.observe app owner) response).toReal)
    (length : Nat)
    (lengthBound : ∀ (history : (protocol).History) (owner : Player),
      ((app).recallAt owner history.state).length ≤ length)
    (owner : Player) (original : (app).Execution) (control : (app).Control)
    (trace : (protocol).Trace (some control))
    (prepared : BindingShadow.PreparedBindings runtime leaks owner original control.execution)
    (network : original.network = control.execution.network) :
    lower ^ length ≤ (model).ownPlayReachProbability
      (phaseProposalReferenceStrategy setup mode runtime leaks bounds plan initial horizon
        scheduler values rates owner) ((model).ownPlay owner trace) := by
  have atoms (index : Fin (control.execution.recall owner).length) :
      lower ≤ (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates owner
        ((control.execution.recall owner).take index.val)
        (control.execution.recall owner)[index.val].beforeView
        (control.execution.recall owner)[index.val].action).toReal := by
    let entry := (control.execution.recall owner)[index.val]
    have split := List.take_append_drop index.val (control.execution.recall owner)
    rw [List.drop_eq_getElem_cons index.isLt] at split
    obtain ⟨before, prior, _prefix, active, recalled, viewed, offered⟩ :=
      (menu).recorded_response_at initial horizon scheduler control trace owner
        ((control.execution.recall owner).take index.val) entry
        ((control.execution.recall owner).drop (index.val + 1)) split.symm
    have nested : ((menu).protocol
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
          scheduler).Trace (some control) := by
      rw [PMF.map_comp]
      exact trace
    have entryPrepared := phaseProposalRepaired_recorded_prepared setup mode runtime leaks bounds
      plan (setup.initialLaw.map encodeInputs) horizon scheduler original control nested owner
        prepared network entry (List.getElem_mem index.isLt)
    have beforeTrace : (protocol).Trace
        (some ⟨before.remaining, some owner, before.execution⟩) := by
      simpa only [← active] using prior
    rw [← recalled] at offered
    change entry.action ∈ PhaseCount.onePacketActions runtime leaks bounds owner
      (before.execution.recall owner) (before.execution.observe app owner) at offered
    have lower := lowerAt before.remaining owner before.execution beforeTrace
      ⟨entry.action, offered⟩ entryPrepared
    have atomEq : (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates
        owner (before.execution.recall owner) (before.execution.observe app owner)
          entry.action).toReal =
        (phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates owner
          (before.execution.recall owner) (before.execution.observe app owner)
            ⟨entry.action, offered⟩).toReal := by
      unfold phaseProposalReferencePolicy
      exact congrArg ENNReal.toReal (pmf_map_apply_of_injective
        (f := fun chosen : PhaseProposal.Response runtime leaks bounds owner
          (before.execution.recall owner) (before.execution.observe app owner) => chosen.val)
        (phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates owner
          (before.execution.recall owner) (before.execution.observe app owner))
        Subtype.val_injective ⟨entry.action, offered⟩)
    rw [← atomEq] at lower
    simpa only [recalled, ← viewed] using lower
  have bound := phaseProposalReference_word_lower_of_atoms setup mode runtime leaks bounds plan
    horizon scheduler values rates owner control trace lower lowerPositive.le atoms
  have size : (control.execution.recall owner).length ≤ length :=
    lengthBound ⟨some control, trace⟩ owner
  exact (pow_le_pow_of_le_one lowerPositive.le lowerBounded size).trans bound

/-- An actual generated bad response contributes its literal atom at its
original full native input. All remaining designated response factors are
bounded by one; private aliases do not invalidate the independent bad bound. -/
theorem phaseProposalGenerated_owner_word_upper
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (rates : PhaseProposalRates) (waiting : 0 < rates.waiting.val)
    (waitingBelow : rates.waiting.val < 1) (slots : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (owner : Player) (history : (protocol).History)
    (badHistory : Vegas.EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory
      runtime leaks bounds initial
      horizon scheduler owner history) :
    (model).ownPlayReachProbability
        (phaseProposalReferenceStrategy setup mode runtime leaks bounds plan initial horizon
          scheduler values rates owner) ((model).ownPlay owner history.trace) ≤
      rates.badPreparation.val := by
  classical
  let policy := phaseProposalReferenceStrategy setup mode runtime leaks bounds plan initial horizon
    scheduler values rates owner
  obtain ⟨record, recorded, event, payload, serial, opening, evidence, binding, actionEq,
    unusable⟩ := badHistory
  have atom : (((policy record.1).map Subtype.val) (some record.2)).toReal ≤
      rates.badPreparation.val := by
    obtain ⟨before, _after, prior, joint, legal, _reached, _prefix, seen, chosen⟩ :=
      (model).exists_tracePrefix_of_mem_ownPlay history.trace recorded
    have allowed := (protocol).legalOption_of_legal legal owner
    rw [chosen] at allowed
    cases before with
    | none => cases allowed.1
    | some before =>
        change before.actor = some owner ∧ record.2 ∈ PhaseCount.onePacketActions runtime leaks
          bounds owner (before.execution.recall owner) (before.execution.observe app owner)
          at allowed
        obtain ⟨active, offered⟩ := allowed
        have beforeTrace : (protocol).Trace
            (some ⟨before.remaining, some owner, before.execution⟩) := by
          simpa only [← active] using prior
        have sourceInfo : record.1 = some (before.execution.recall owner,
            before.execution.observe app owner) := by
          rw [← seen]
          change ((menu).signals initial horizon scheduler).infoOf owner prior = _
          rw [(menu).info]
          simp only [ReactiveApplication.observe, active, ite_true]
        rw [sourceInfo]
        change ((((menu).restrictPolicy initial horizon scheduler owner
          (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates owner)
            (some (before.execution.recall owner, before.execution.observe app owner))).map
              Subtype.val) (some record.2)).toReal ≤ _
        rw [(menu).restrictPolicy_atom initial horizon scheduler owner _ _ _ _
          (phaseProposalReferencePolicy_covered setup mode runtime leaks bounds plan values rates
            owner _ _)]
        rw [actionEq] at offered ⊢
        let inputs := setup.initialLaw.map encodeInputs
        have nested : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
            scheduler).Trace (some ⟨before.remaining, some owner, before.execution⟩) := by
          dsimp only [inputs]
          rw [PMF.map_comp]
          exact beforeTrace
        let material : WitnessedSubmission (serviceGraph setup mode) :=
          ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
        obtain ⟨⟨attempt, actualEvent⟩, request⟩ :=
          PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds plan inputs horizon
            scheduler before.remaining owner before.execution nested material offered
        have attemptEq := request.1
        change attempt = before.execution.application.attempt at attemptEq
        subst attempt
        have named := PhaseCount.onePacket_event_of_request runtime leaks bounds plan
          (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler before.remaining
            owner before.execution nested ⟨before.execution.application.attempt, actualEvent⟩
              request material offered
        change some event = some actualEvent at named
        have same := Option.some.inj named
        subst actualEvent
        have bound := phaseProposalReferenceResponses_badPreparation_atom_le setup mode runtime
          leaks bounds plan complete covered maximal values fullValues rates waiting waitingBelow
            slots badPositive badBelow horizon scheduler before.remaining owner before.execution
              beforeTrace event payload binding request serial opening evidence offered unusable
        unfold phaseProposalReferencePolicy
        have atomEq := congrArg ENNReal.toReal (pmf_map_apply_of_injective
          (f := fun chosen : PhaseProposal.Response runtime leaks bounds owner
            (before.execution.recall owner) (before.execution.observe app owner) => chosen.val)
          (phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates owner
            (before.execution.recall owner) (before.execution.observe app owner))
          Subtype.val_injective ⟨_, offered⟩)
        exact atomEq.le.trans bound
  have atMostOne (word : List ((model).InfoState owner × (protocol).Action owner)) :
      (model).ownPlayReachProbability policy word ≤ 1 := by
    induction word with
    | nil => exact le_rfl
    | cons head rest ih =>
        have upper := pmf_toReal_apply_le_one ((policy head.1).map Subtype.val) (some head.2)
        exact (mul_le_mul_of_nonneg_left ih ENNReal.toReal_nonneg).trans
          (by simpa only [mul_one] using upper)
  have bounded (word : List ((model).InfoState owner × (protocol).Action owner))
      (member : record ∈ word) :
      (model).ownPlayReachProbability policy word ≤ rates.badPreparation.val := by
    induction word with
    | nil => cases member
    | cons head rest ih =>
        rcases List.mem_cons.mp member with same | earlier
        · subst head
          exact (mul_le_mul_of_nonneg_left (atMostOne rest) ENNReal.toReal_nonneg).trans
            (by simpa only [mul_one] using atom)
        · exact (mul_le_mul_of_nonneg_right
            (pmf_toReal_apply_le_one ((policy head.1).map Subtype.val) (some head.2))
            ((model).ownPlayReachProbability_nonneg policy rest)).trans
              (by simpa only [one_mul] using ih earlier)
  exact bounded _ recorded

end Vegas
