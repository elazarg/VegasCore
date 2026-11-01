/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBeliefPartsWiring
import Vegas.Game.OnePacketOwnIntended
import Vegas.Game.OnePacketBindingRepairAssembly
import Vegas.Game.OnePacketRetention
import Vegas.Game.OnePacketSwapFiberSum

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
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [Finite setup.intendedProtocol.History]

local instance : Fintype ((bounds.onePacketMenu runtime leaks).protocol
    (initialLaw setup) horizon scheduler).History :=
  (bounds.onePacketMenu runtime leaks).historyFintype (initialLaw setup) horizon scheduler

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

section BaseInputs

variable (setup runtime leaks bounds horizon scheduler)

open Classical in
/-- **The base inputs of the one-packet certificate** for one source sequence:
the tremble scales and the obligations not yet discharged other than the value
decompositions and late commitments, each a statement along every fully mixed
Bayes sequence of profiles assembled from the certificate's components, at the
forced sites. -/
structure OnePacketBaseInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) where
  /-- The tremble scale at each index. -/
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_le_one : ∀ n, scale n ≤ 1
  scale_vanishing : Tendsto scale atTop (nhds 0)
  /-- A bound on the gap between a continuation value and the exclusion payoff. -/
  gapBound : ℝ
  gapBound_nonneg : 0 ≤ gapBound
  /-- Every binding and publication value is a bounded value. -/
  covers : bounds.CoversOutputValues
  /-- Every value of an initial binding input is a bounded value. -/
  coversInputs : bounds.CoversInputValues
  /-- Every player's binding events fit in the prepared slots. -/
  capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount
  /-- The late options use bounded slots. -/
  slotsLe : slots ≤ bounds.candidateCount
  /-- **The honest counterparts** at every forced decision input at the player's
  own turn at which the player owes no failure, along every fully mixed Bayes
  sequence of assembled profiles. -/
  counterpartInputs : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds
    (initialLaw setup) horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu runtime leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∀ who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup runtime leaks bounds (initialLaw setup)
        horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup runtime leaks bounds (initialLaw setup)
        horizon scheduler ((onePacketN).agentAt site) →
      ∀ {past : List (application setup runtime leaks).PlayerEntry}
        {view : (application setup runtime leaks).PlayerView}, site.1 = some (past, view) →
      ∀ {event : (graph setup).EventId},
      view.application.publicView.ownTurn? who = some event →
      OnePacketCounterpartInputs setup runtime leaks bounds horizon scheduler sequence
        targetSequence site
  /-- **The own and replay inputs** at every forced decision input at the
  player's own turn at which the player owes no failure, along every fully mixed
  Bayes sequence of assembled profiles. These are the sites with a projected
  decision (`Vegas.projectedDecision_of_forcedAgent`), late deliveries
  included. -/
  ownInputs : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds
    (initialLaw setup) horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu runtime leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∀ who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup runtime leaks bounds (initialLaw setup)
        horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup runtime leaks bounds (initialLaw setup)
        horizon scheduler ((onePacketN).agentAt site) →
      ∀ {past : List (application setup runtime leaks).PlayerEntry}
        {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
        {event : (graph setup).EventId},
      view.application.publicView.ownTurn? who = some event →
      ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who
        site.1),
      OnePacketOwnInputs setup runtime leaks bounds horizon scheduler sequence targetSequence site
        (projectedSite setup runtime leaks decision) atSite rfl
  /-- Some late option sends at a slot. -/
  slots_pos : 0 < slots

omit [Finite setup.intendedProtocol.History] in
/-- Some prepared slot is bounded, once there is a player. -/
theorem OnePacketBaseInputs.one_le_candidateCount
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketBaseInputs setup runtime leaks bounds horizon scheduler sequence slots)
    (who : Player) : 1 ≤ bounds.candidateCount :=
  Nat.zero_lt_of_lt (inputs.capacity who)

/-- **The forced-belief inputs** at a forced decision input at the player's own
turn at which the player owes no failure: the honest counterparts and the own
and replay inputs there. -/
def OnePacketBaseInputs.beliefInputs {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {slots : Nat}
    (inputs : OnePacketBaseInputs setup runtime leaks bounds horizon scheduler sequence slots)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence
      inputs.scale
      inputs.scale_pos inputs.scale_le_one weights
        targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu runtime leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    (who : Player) (site : (onePacketN).InformationSite who)
    (forced : ¬ FreeAgent setup runtime leaks bounds (initialLaw setup)
      horizon scheduler ((onePacketN).agentAt site))
    (notOwing : ¬ OwingAgent setup runtime leaks bounds (initialLaw setup)
      horizon scheduler ((onePacketN).agentAt
      site))
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who
      site.1)) :
    OnePacketBeliefInputs setup runtime leaks bounds horizon scheduler sequence targetSequence site
      (projectedSite setup runtime leaks decision) atSite rfl where
  toOnePacketCounterpartInputs := inputs.counterpartInputs weights targetSequence assembled mixed
    bayes who site forced notOwing atSite turn
  toOnePacketOwnInputs := inputs.ownInputs weights
    targetSequence assembled mixed bayes who site
    forced notOwing atSite turn decision

end BaseInputs

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
      (combinedFloor setup runtime leaks bounds horizon scheduler (sequence n)) depth n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    {weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler slots p)}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence)
    {who : Player} {site : (onePacketN).InformationSite who}
    (notFree : ¬ FreeAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((onePacketN).agentAt site))
    (notOwing : ¬ OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((onePacketN).agentAt site))
    {sourceSite : setup.intendedModel.InformationSite who}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (atSite : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup runtime leaks who site.1)
    {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event) :
    OnePacketOwnInputs setup runtime leaks bounds horizon scheduler sequence targetSequence site
      sourceSite atSite projected := by
  let own : ∀ n (history : (onePacketN).InformationHistory who site.1),
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler)
        who history.1.trace := fun _ history _ =>
    ownCompletionsIntended_of_siteNotOwes (runtime := runtime) wellFormed
      (siteDebtFree_of_not_owing setup runtime leaks bounds horizon scheduler notOwing) history
  let steps := assembledOperationalSteps (runtime := runtime) wellFormed sequence scale scale_pos
    scale_le_one depth
    scaleEq covers capacity weights assembled who
  let fiberMass : ℕ → ℝ := fun n =>
    ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧
        replayProjection setup runtime leaks bounds horizon scheduler sourceSite site atSite
          projected
          history = sourceSite.2.choose,
      operationalWeight setup runtime leaks who (steps.mass n)
        (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace)
  refine OnePacketOwnInputs.ofCertificate (runtime := runtime) wellFormed depth scaleEq covers
    capacity assembled
    atSite projected own fiberMass ?_
  intro n point
  change _ = ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler (sequence n)
    who
      history.1.trace ∧
      replayProjection setup runtime leaks bounds horizon scheduler sourceSite site atSite projected
        history = sourceSite.2.choose,
    operationalWeight setup runtime leaks who (steps.mass n)
      (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace)
  convert fiber_sum_eq_between (runtime := runtime) (who := who) (steps := steps) wellFormed
    (forcedAgent_of_not_free setup runtime leaks bounds (initialLaw setup) horizon scheduler
      notFree) atSite projected
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
        PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
          horizon scheduler bounds.candidateCount p))
      (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence
        (fun n => trembleScale
          (combinedFloor setup runtime leaks bounds horizon scheduler (sequence n)) depth n)
        (fun n => trembleScale_pos
          (combinedFloor_pos setup runtime leaks bounds horizon scheduler (sequence n)))
        (fun n => trembleScale_le_one
          (combinedFloor_pos setup runtime leaks bounds horizon scheduler (sequence n)).le
          (combinedFloor_le_one setup runtime leaks bounds horizon scheduler (sequence n)))
        weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu runtime leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∀ who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((onePacketN).agentAt site) →
        ¬ OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((onePacketN).agentAt site) →
        ∀ {past : List (application setup runtime leaks).PlayerEntry}
          {view : (application setup runtime leaks).PlayerView}, site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
        view.application.publicView.ownTurn? who = some event →
        OnePacketCounterpartInputs setup runtime leaks bounds horizon scheduler sequence
          targetSequence
          site) :
    OnePacketBaseInputs setup runtime leaks bounds horizon scheduler sequence
      bounds.candidateCount where
  scale n := trembleScale
    (combinedFloor setup runtime leaks bounds horizon scheduler (sequence n)) depth n
  scale_pos n := trembleScale_pos
    (combinedFloor_pos setup runtime leaks bounds horizon scheduler (sequence n))
  scale_le_one n := trembleScale_le_one
    (combinedFloor_pos setup runtime leaks bounds horizon scheduler (sequence n)).le
    (combinedFloor_le_one setup runtime leaks bounds horizon scheduler (sequence n))
  scale_vanishing := tendsto_trembleScale _
    (fun n => combinedFloor_pos setup runtime leaks bounds horizon scheduler (sequence n))
    (fun n => combinedFloor_le_one setup runtime leaks bounds horizon scheduler (sequence n))
  gapBound := gapBound
  gapBound_nonneg := gapBound_nonneg
  covers := covers
  coversInputs := coversInputs
  capacity := capacity
  slotsLe := le_rfl
  counterpartInputs := counterparts
  ownInputs _weights _targetSequence assembled _mixed _bayes _who _site
    notFree notOwing
      {_past} {_view} atSite {_event} turn _decision :=
    OnePacketOwnInputs.ofAssembled (runtime := runtime) wellFormed sourceMixed depth (fun _ =>
      rfl) covers
      coversInputs capacity assembled notFree notOwing atSite rfl turn
  slots_pos := slots_pos

section SetupAssembly

variable (setup runtime leaks bounds horizon scheduler)
  {Public : Type*} {signal : State L setup.context → Public}

open Classical in
/-- The source information, value coverage and private-binding exchange construct
all base comparison inputs at the canonical tremble scale. -/
def OnePacketBaseInputs.ofSetup
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount) :
    OnePacketBaseInputs setup runtime leaks bounds horizon scheduler sequence
      bounds.candidateCount := by
  refine OnePacketBaseInputs.ofCounterparts (runtime := runtime) wellFormed sequence sourceMixed
    (2 * horizon + 2)
    0 (le_refl 0) covers coversInputs capacity slots_pos ?_
  intro weights targetSequence assembled mixed _bayes who site notFree notOwing
    past view atSite event turn
  exact OnePacketCounterpartInputs.ofBindingRepairs (runtime := runtime) wellFormed independent
    observable sourceMixed
    (fun n => trembleScale_pos
      (combinedFloor_pos setup runtime leaks bounds horizon scheduler (sequence n)))
    (fun n => trembleScale_le_one
      (combinedFloor_pos setup runtime leaks bounds horizon scheduler (sequence n)).le
      (combinedFloor_le_one setup runtime leaks bounds horizon scheduler (sequence n)))
    (fun _ => rfl) covers coversInputs capacity weights assembled mixed
    notFree notOwing atSite turn

end SetupAssembly

end Vegas
