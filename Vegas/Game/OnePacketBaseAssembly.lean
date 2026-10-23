/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketBeliefPartsWiring
import Vegas.Game.OnePacketOwnIntended

/-! # Assembling the own and replay inputs of the one-packet certificate

At a forced site where the player owes no failure, all its prior completions
are intended. The hidden-value exchange between any two source histories
therefore gives the common operational fiber required by belief transport.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [Finite setup.intendedProtocol.History]

local instance : Fintype ((bounds.onePacketMenu (runtime setup) leaks).protocol
    (initialLaw setup) horizon scheduler).History :=
  (bounds.onePacketMenu (runtime setup) leaks).historyFintype (initialLaw setup) horizon scheduler

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- Own and replay inputs follow from a debt-free forced site, the assembled
profiles, and coverage of all binding values. No own-completion or common-fiber
hypothesis remains. -/
def OnePacketOwnInputs.ofAssembled (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    {scale : ℕ → ℝ} {scale_pos : ∀ n, 0 < scale n} {scale_le_one : ∀ n, scale n ≤ 1}
    (depth : ℕ)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon scheduler (sequence n)) depth n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    {weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p)}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    {who : Player} {site : (onePacketN).InformationSite who}
    (notFree : ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (notOwing : ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    {sourceSite : setup.intendedModel.InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (atSite : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1)
    {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event) :
    OnePacketOwnInputs setup leaks bounds horizon scheduler sequence targetSequence site
      sourceSite atSite projected := by
  let own : ∀ n (history : (onePacketN).InformationHistory who site.1),
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler)
        who history.1.trace := fun _ history _ =>
    ownCompletionsIntended_of_siteNotOwes wellFormed
      (siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing) history
  let steps := assembledOperationalSteps wellFormed sequence scale scale_pos scale_le_one depth
    scaleEq covers capacity weights assembled who
  let fiberMass : ℕ → ℝ := fun n =>
    ∑ history with RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧
        replayProjection setup leaks bounds horizon scheduler sourceSite site atSite projected
          history = sourceSite.2.choose,
      operationalWeight setup leaks who (steps.mass n)
        (operationalRecord setup leaks bounds horizon scheduler history.1.trace)
  refine OnePacketOwnInputs.ofCertificate wellFormed depth scaleEq covers capacity assembled
    atSite projected own fiberMass ?_
  intro n point
  change _ = ∑ history with RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace ∧
      replayProjection setup leaks bounds horizon scheduler sourceSite site atSite projected
        history = sourceSite.2.choose,
    operationalWeight setup leaks who (steps.mass n)
      (operationalRecord setup leaks bounds horizon scheduler history.1.trace)
  convert fiber_sum_eq_between (who := who) (steps := steps) wellFormed
    (forcedAgent_of_not_free setup leaks bounds horizon scheduler notFree) atSite projected
    (own n) (sourceMixed n) turn (bindingFieldsCovered_of_covers covers coversInputs)
    point sourceSite.2.choose using 1
  all_goals congr 2

open Classical in
/-- Assemble the base certificate at the canonical tremble scale and all
bounded prepared slots. Honest counterparts are the only proof input; intended
own completions and common operational fibers are derived. -/
def OnePacketBaseInputs.ofCounterparts (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (depth : ℕ) (gapBound : ℝ) (gapBound_nonneg : 0 ≤ gapBound)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (counterparts : ∀
      (weights : ℕ → ∀ p,
        PMF (OnePacketPart setup leaks bounds horizon scheduler bounds.candidateCount p))
      (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup leaks bounds horizon scheduler sequence
        (fun n => trembleScale
          (combinedFloor setup leaks bounds horizon scheduler (sequence n)) depth n)
        (fun n => trembleScale_pos
          (combinedFloor_pos setup leaks bounds horizon scheduler (sequence n)))
        (fun n => trembleScale_le_one
          (combinedFloor_pos setup leaks bounds horizon scheduler (sequence n)).le
          (combinedFloor_le_one setup leaks bounds horizon scheduler (sequence n)))
        weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∀ who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ∀ {past : List (application setup leaks).PlayerEntry}
          {view : (application setup leaks).PlayerView}, site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
        view.application.publicView.ownTurn? who = some event →
        OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence targetSequence
          site) :
    OnePacketBaseInputs setup leaks bounds horizon scheduler sequence bounds.candidateCount where
  scale n := trembleScale
    (combinedFloor setup leaks bounds horizon scheduler (sequence n)) depth n
  scale_pos n := trembleScale_pos
    (combinedFloor_pos setup leaks bounds horizon scheduler (sequence n))
  scale_le_one n := trembleScale_le_one
    (combinedFloor_pos setup leaks bounds horizon scheduler (sequence n)).le
    (combinedFloor_le_one setup leaks bounds horizon scheduler (sequence n))
  scale_vanishing := tendsto_trembleScale _
    (fun n => combinedFloor_pos setup leaks bounds horizon scheduler (sequence n))
    (fun n => combinedFloor_le_one setup leaks bounds horizon scheduler (sequence n))
  gapBound := gapBound
  gapBound_nonneg := gapBound_nonneg
  covers := covers
  coversInputs := coversInputs
  capacity := capacity
  slotsLe := le_rfl
  counterpartInputs := counterparts
  ownInputs _weights _targetSequence assembled _mixed _bayes _who _site notFree notOwing
      {_past} {_view} atSite {_event} turn _decision :=
    OnePacketOwnInputs.ofAssembled wellFormed sourceMixed depth (fun _ => rfl) covers
      coversInputs capacity assembled notFree notOwing atSite rfl turn
  slots_pos := slots_pos

end Vegas
