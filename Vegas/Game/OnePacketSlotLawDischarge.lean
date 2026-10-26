/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFactorBounds
import Vegas.Game.OnePacketSequentialPreservation
import Vegas.Game.OnePacketContentFloor

/-! # The slot law of the certificate's profile

At a forced agent, the certificate's stage profile mixes the agent's components
over its pool's weights. An unkeyed agent plays its prescribed component
(`Vegas.freeKeyedMixture_of_not_keyed`); a keyed agent plays its keyed laws
mixed over the weights of its key's pool (`Vegas.freeKeyedMixture_of_keyed`),
which are the weights the late-delivery key reads (`Vegas.keyWeights`).

The response mass of a step (`Vegas.stepResponse`) combines, at the responder's
keys before and after the response, the factor of its main law
(`Vegas.mainFactor`: the as-if-honest factor, or at a late delivery the
late-option factors mixed over the key's weights), the silence factor and the
slot-tier factor.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

section Pools

variable {Player : Type} {T : ExecutionProtocol Player} {N : InformationModel T}
  [Fintype T.History] [∀ who, DecidableEq (N.InfoState who)] {Key : Type*}
  {free keyed : N.InformationAgent N.playedInformation → Prop}
  {key : N.InformationAgent N.playedInformation → Key} {Opt : Type}

/-- A keyed agent's mixture of components over its pool's weights is its keyed
law mixed over those weights. -/
theorem freeKeyedMixture_of_keyed
    (weights : ∀ p, PMF (FreeKeyedPart free keyed key Opt p))
    (freeLaw : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    {agent : N.InformationAgent N.playedInformation} (notFree : ¬ free agent)
    (isKeyed : ownedKeyed free keyed agent) :
    (weights (freeKeyedPool free keyed key agent)).bind
        (freeKeyedComponent freeLaw prescribed keyedLaw agent) =
      (weights (.inr (some ⟨key agent, ⟨agent, isKeyed⟩, rfl⟩))).bind (keyedLaw agent) := by
  unfold freeKeyedComponent
  rw [freeKeyedPool_of_not_free notFree, keyedPool_of_keyed isKeyed]
  rfl

/-- An unkeyed agent's mixture of components is its prescribed law. -/
theorem freeKeyedMixture_of_not_keyed
    (weights : ∀ p, PMF (FreeKeyedPart free keyed key Opt p))
    (freeLaw : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    {agent : N.InformationAgent N.playedInformation} (notFree : ¬ free agent)
    (unkeyed : ¬ ownedKeyed free keyed agent) :
    (weights (freeKeyedPool free keyed key agent)).bind
        (freeKeyedComponent freeLaw prescribed keyedLaw agent) = prescribed agent := by
  unfold freeKeyedComponent
  rw [freeKeyedPool_of_not_free notFree, keyedPool_of_not_keyed unkeyed]
  exact PMF.bind_const _ _

end Pools

section Factors

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (bounds : MessageBounds (graph setup))

open Classical in
/-- **The factor of the main law**: the as-if-honest factor, and at a late
delivery the late-option factors mixed over the key's weights. -/
def mainFactor {slots : Nat} (weights : PMF (LateOption slots))
    (before after : LateKey setup runtime leaks) : ℝ :=
  if before.IsLate then
    ∑ option, (weights option).toReal * lateOptionFactor bounds before after
      option
  else honestFactor before after

/-- **The response mass of a step**: the slot combination of the main,
silence and slot-tier factors at the responder's keys before and after its
response. -/
def stepResponse {slots : Nat} (keyLaw : Option (LateKey setup runtime leaks) → PMF (LateOption
  slots))
    (scale : ℝ) :
    Option (OperationalState setup runtime leaks) → Option (OperationalState setup runtime leaks)
      → ℝ
  | some before, some after =>
      match before.actor with
      | none => 0
      | some actor =>
          match before.keys actor, after.keys actor with
          | some key, some next =>
              slotCombination scale (mainFactor bounds (keyLaw (some key))
                key next)
                (silenceFactor next) (slotTierFactor
                  bounds key next)
          | _, _ => 0
  | _, _ => 0

theorem mainFactor_mem {slots : Nat} (weights : PMF (LateOption slots))
    (before after : LateKey setup runtime leaks) :
    0 ≤ mainFactor bounds weights before after ∧ mainFactor (runtime :=
      runtime) bounds weights before after ≤ 1 := by
  classical
  unfold mainFactor
  split
  · constructor
    · exact Finset.sum_nonneg fun option _ =>
        mul_nonneg ENNReal.toReal_nonneg (lateOptionFactor_mem (runtime := runtime) bounds before
          after option).1
    · calc
        ∑ option, (weights option).toReal * lateOptionFactor bounds before after option
          ≤ ∑ option, (weights option).toReal :=
            Finset.sum_le_sum fun option _ => mul_le_of_le_one_right ENNReal.toReal_nonneg
              (lateOptionFactor_mem (runtime := runtime) bounds before after option).2
        _ = 1 := by
            rw [← ENNReal.toReal_sum (fun option _ => PMF.apply_ne_top weights option),
              show ∑ option, weights option = 1 from
                (tsum_fintype (fun option => weights option)).symm.trans weights.tsum_coe,
              ENNReal.toReal_one]
  · exact honestFactor_mem (runtime := runtime) before after

theorem stepResponse_nonneg {slots : Nat}
    (keyLaw : Option (LateKey setup runtime leaks) → PMF (LateOption slots)) {scale : ℝ}
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (before after : Option (OperationalState setup runtime leaks)) :
    0 ≤ stepResponse (runtime := runtime) bounds keyLaw scale before after := by
  unfold stepResponse
  split
  · split
    · exact le_rfl
    · split
      · exact slotCombination_nonneg nonnegative le_one (mainFactor_mem (runtime := runtime)
          bounds _ _ _).1
          (silenceFactor_mem (runtime := runtime) _).1 (slotTierFactor_mem (runtime := runtime)
            bounds _ _).1
      · exact le_rfl
  · exact le_rfl

end Factors

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

section Response

open Classical in
/-- **The weights of a late-delivery key**: the weights of its pool, and waiting
for a key of no forced late delivery. -/
def keyWeights {slots : Nat}
    (weights : ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (key : Option (LateKey setup runtime leaks)) : PMF (LateOption slots) :=
  if present : key ∈ Set.range fun agent : {agent : (onePacketN).InformationAgent
      (onePacketN).playedInformation // ownedKeyed (FreeAgent setup runtime leaks bounds horizon
        scheduler) (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon
          scheduler)
          agent} =>
      agentLateKey setup runtime leaks bounds (initialLaw setup) horizon scheduler agent.1 then
    weights (.inr (some ⟨key, present⟩))
  else PMF.pure none

end Response

section Profile

/-- **The certificate's profile** at a stage: every agent mixes its free, prescribed and
late components over its pool's weights. -/
def certificateProfile (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (n : ℕ) : ∀ player, (onePacketN).BehavioralPolicy player :=
  (onePacketN).agentBehavior (onePacketN).playedInformation
    (onePacketFallback setup runtime leaks bounds horizon scheduler)
    fun agent => (weights n (onePacketPool setup runtime leaks bounds horizon scheduler agent)).bind
      (freeKeyedComponent
        (onePacketUnforced setup runtime leaks bounds horizon scheduler scale scale_pos
          scale_le_one n)
        (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent)

variable {setup runtime leaks bounds horizon scheduler}

/-- The real mass of a law mixed over late options. -/
private theorem bind_lateOption_toReal {slots : Nat} {α : Type}
    (weights : PMF (LateOption slots)) (laws : LateOption slots → PMF α) (a : α) :
    ((weights.bind laws) a).toReal =
      ∑ option, (weights option).toReal * (laws option a).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum fun option _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  simp only [ENNReal.toReal_mul]

/-- **The certificate's profile at a forced agent.** At a played information
state of a forced agent, owing a failure or not, the certificate's profile is
the slot-trembled choice whose main law is the honest choice, or a mixture of
late choices when the agent is a late delivery. -/
theorem certificateProfile_eq_slotTrembled
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (n : ℕ) {actor : Player} (info : (application setup runtime leaks).Info)
    (played : info ∈ (onePacketN).playedInformation actor)
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup) horizon
      scheduler actor info) :
    ∃ main : PMF ((onePacketN).Choice actor info),
      (main = honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
        (sequence n)
          actor info ∨
        ∃ late : PMF (LateOption slots), main = late.bind
          (lateChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (sequence n)
            actor info)) ∧
      certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n actor info =
        slotTrembledChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (scale n)
          (scale_pos n).le (scale_le_one n) actor info main
          (PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
            actor info))
          (slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (sequence n)
            actor info) := by
  let agent : (onePacketN).InformationAgent (onePacketN).playedInformation :=
    ⟨actor, ⟨info, played⟩⟩
  have notFree : ¬ FreeAgent setup runtime leaks bounds horizon scheduler agent :=
    fun unforced => unforced forced
  have atAgent := (onePacketN).agentBehavior_at (onePacketN).playedInformation
    (onePacketFallback setup runtime leaks bounds horizon scheduler)
    (fun agent => (weights n (onePacketPool setup runtime leaks bounds horizon scheduler
      agent)).bind
      (freeKeyedComponent
        (onePacketUnforced setup runtime leaks bounds horizon scheduler scale scale_pos
          scale_le_one n)
        (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent)) agent
  by_cases keyed : ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
      (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler) agent
  · have mixture := freeKeyedMixture_of_keyed (key := agentLateKey setup runtime leaks bounds
      (initialLaw setup) horizon scheduler) (weights n)
      (onePacketUnforced setup runtime leaks bounds horizon scheduler scale scale_pos scale_le_one
        n)
      (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree keyed
    let late : PMF (LateOption slots) := weights n (.inr (some ⟨agentLateKey setup runtime leaks
      bounds
      (initialLaw setup) horizon scheduler agent, ⟨agent, keyed⟩, rfl⟩))
    refine ⟨late.bind (lateChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
      (sequence n) actor info), Or.inr ⟨late, rfl⟩, ?_⟩
    change (onePacketN).agentBehavior _ _ _ agent.1 agent.2.1 = _
    rw [atAgent, mixture]
    exact bind_lateComponent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      (sequence n) late (scale n) (scale_pos n).le (scale_le_one n) actor info
  · have mixture := freeKeyedMixture_of_not_keyed (key := agentLateKey setup runtime leaks bounds
      (initialLaw setup) horizon scheduler) (weights n)
      (onePacketUnforced setup runtime leaks bounds horizon scheduler scale scale_pos scale_le_one
        n)
      (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree keyed
    refine ⟨_, Or.inl rfl, ?_⟩
    change (onePacketN).agentBehavior _ _ _ agent.1 agent.2.1 = _
    rw [atAgent, mixture]
    rfl

/-- **The slot law at a response.** At a history of the one-packet game where a
forced player whose disclosure is canonical responds with positive content,
the certificate's profile at its information is a slot-trembled component
whose main, silence and slot-tier laws give the realized choice its content
factor times the factors read from its keys; their slot combination is the
response mass of the step; and the cube of the scale stays within the error. -/
theorem certificate_slotLaw_at (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (n : ℕ) {control next : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    {actor : Player} (acting : control.actor = some actor)
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup) horizon
      scheduler actor (some (control.execution.recall actor,
        control.execution.observe (application setup runtime leaks) actor)))
    (canonical : DisclosureCanonical setup runtime leaks bounds actor (control.execution.recall
      actor)
      (control.execution.observe (application setup runtime leaks) actor))
    (response : (application setup runtime leaks).Action)
    (member : response ∈ bounds.onePacketActions runtime leaks actor
      (control.execution.recall actor)
      (control.execution.observe (application setup runtime leaks) actor))
    (nextEq : next.execution = control.execution.respond (application setup runtime leaks) actor
      response)
    (positive : 0 < contentFactor setup runtime leaks (sequence n) actor control.execution
      next.execution
      response)
    (floored : response.transmission ≠ none →
      floor n ≤ contentFactor setup runtime leaks (sequence n) actor control.execution
        next.execution
        response)
    (info : (application setup runtime leaks).Info)
    (infoEq : info = some (control.execution.recall actor,
      control.execution.observe (application setup runtime leaks) actor))
    (played : info ∈ (onePacketN).playedInformation actor)
    (choice : (onePacketN).Choice actor info) (chosen : choice.1 = some response) :
    ∃ (main alternative slot : PMF ((onePacketN).Choice actor info))
      (mainFactor' alternativeFactor slotFactor : ℝ),
      certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n actor info =
        slotTrembledChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (scale n)
          (scale_pos n).le (scale_le_one n) actor info main alternative slot ∧
      (main choice).toReal = contentFactor setup runtime leaks (sequence n) actor control.execution
        next.execution response * mainFactor' ∧
      (alternative choice).toReal = contentFactor setup runtime leaks (sequence n) actor
        control.execution next.execution response * alternativeFactor ∧
      (slot choice).toReal = contentFactor setup runtime leaks (sequence n) actor control.execution
        next.execution response * slotFactor ∧
      slotCombination (scale n) mainFactor' alternativeFactor slotFactor =
        stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks bounds horizon
          scheduler (weights n))
          (scale n) (operationalState setup runtime leaks (some control))
          (operationalState setup runtime leaks (some next)) ∧
      scale n ^ 3 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card *
        (contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
          response *
        stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks bounds horizon
          scheduler (weights n))
          (scale n) (operationalState setup runtime leaks (some control))
          (operationalState setup runtime leaks (some next))) := by
  classical
  subst infoEq
  rw [nextEq] at positive floored ⊢
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  obtain ⟨honestMass, lateMass, silenceMass, slotMass⟩ := onePacket_step_masses (runtime :=
    runtime) (sequence n)
    covers capacity trace actor canonical response member positive choice chosen
  -- The keys before and after the response.
  have responseEq : stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks
    bounds horizon scheduler
      (weights n)) (scale n) (operationalState setup runtime leaks (some control))
      (operationalState setup runtime leaks (some next)) =
      slotCombination (scale n)
        (mainFactor bounds (keyWeights setup runtime leaks bounds horizon
          scheduler (weights n)
          (some (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
            (control.execution.observe (application setup runtime leaks) actor))))
          (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
            (control.execution.observe (application setup runtime leaks) actor))
          (LateKey.ofView setup runtime leaks actor
            ((control.execution.respond (application setup runtime leaks) actor response).recall
              actor)
            ((control.execution.respond (application setup runtime leaks) actor response).observe
              (application setup runtime leaks) actor)))
        (silenceFactor (LateKey.ofView setup runtime leaks actor
          ((control.execution.respond (application setup runtime leaks) actor response).recall
            actor)
          ((control.execution.respond (application setup runtime leaks) actor response).observe
            (application setup runtime leaks) actor)))
        (slotTierFactor bounds
          (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
            (control.execution.observe (application setup runtime leaks) actor))
          (LateKey.ofView setup runtime leaks actor
            ((control.execution.respond (application setup runtime leaks) actor response).recall
              actor)
            ((control.execution.respond (application setup runtime leaks) actor response).observe
              (application setup runtime leaks) actor))) := by
    unfold stepResponse operationalState
    dsimp only
    rw [acting]
    dsimp only
    rw [nextEq]
    rfl
  have keyLate := LateKey.ofView_isLate (runtime := runtime) rawTrace actor
  let agent : (onePacketN).InformationAgent (onePacketN).playedInformation :=
    ⟨actor, ⟨_, played⟩⟩
  have notFree : ¬ FreeAgent setup runtime leaks bounds horizon scheduler agent :=
    fun unforced => unforced forced
  have atAgent := (onePacketN).agentBehavior_at (onePacketN).playedInformation
    (onePacketFallback setup runtime leaks bounds horizon scheduler)
    (fun agent => (weights n (onePacketPool setup runtime leaks bounds horizon scheduler
      agent)).bind
      (freeKeyedComponent
        (onePacketUnforced setup runtime leaks bounds horizon scheduler scale scale_pos
          scale_le_one n)
        (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent)) agent
  have contentNonneg : 0 ≤ contentFactor setup runtime leaks (sequence n) actor control.execution
      (control.execution.respond (application setup runtime leaks) actor response) response :=
    positive.le
  have slotsPos : 0 < (trembleSlots setup bounds).card :=
    (trembleSlots_nonempty setup bounds).card_pos
  -- The cube of the scale stays within the error for every nonnegative main factor.
  have cube : ∀ main, 0 ≤ main → scale n ^ 3 ≤ slotError (scale n) (floor n)
      (trembleSlots setup bounds).card * (contentFactor setup runtime leaks (sequence n) actor
        control.execution (control.execution.respond (application setup runtime leaks) actor
          response)
        response * slotCombination (scale n) main
          (silenceFactor (LateKey.ofView setup runtime leaks actor
            ((control.execution.respond (application setup runtime leaks) actor response).recall
              actor)
            ((control.execution.respond (application setup runtime leaks) actor response).observe
              (application setup runtime leaks) actor)))
          (slotTierFactor bounds
            (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
              (control.execution.observe (application setup runtime leaks) actor))
            (LateKey.ofView setup runtime leaks actor
              ((control.execution.respond (application setup runtime leaks) actor response).recall
                actor)
              ((control.execution.respond (application setup runtime leaks) actor response).observe
                (application setup runtime leaks) actor)))) := by
    intro main mainNonneg
    rw [← mul_assoc]
    cases sends : response.transmission with
    | none =>
        have silent : response = ⟨none⟩ := by
          rcases response with ⟨transmission⟩
          change transmission = none at sends
          rw [sends]
        subst silent
        have contentOne : contentFactor setup runtime leaks (sequence n) actor control.execution
            (control.execution.respond (application setup runtime leaks) actor ⟨none⟩) ⟨none⟩ = 1
              := rfl
        have silenceOne : silenceFactor (LateKey.ofView setup runtime leaks
          actor
            ((control.execution.respond (application setup runtime leaks) actor ⟨none⟩).recall
              actor)
            ((control.execution.respond (application setup runtime leaks) actor ⟨none⟩).observe
              (application setup runtime leaks) actor)) = 1 := by
          unfold silenceFactor
          rw [LateKey.respond_lastEmitted]
          rfl
        rw [contentOne, silenceOne]
        exact cube_le_slotError_of_one (scale_pos n).le (small n) (floor_pos n) _ mainNonneg
          zero_le_one (slotTierFactor_mem (runtime := runtime) bounds _ _).1 (Or.inr rfl)
    | some material =>
        obtain ⟨event, turn, unsent, _⟩ := onePacket_content_pos (runtime := runtime) (sequence n)
          trace actor
          response member material sends _ positive
        have pending : (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
            (control.execution.observe (application setup runtime leaks) actor)).pending =
              some event := by
          rw [LateKey.ofView_pending rawTrace actor]
          exact pendingEvent_of_spec (runtime := runtime) (setup := setup) (leaks := leaks)
            (view := control.execution.observe (application setup runtime leaks) actor) turn unsent
        have lastSome : (LateKey.ofView setup runtime leaks actor
            ((control.execution.respond (application setup runtime leaks) actor response).recall
              actor)
            ((control.execution.respond (application setup runtime leaks) actor response).observe
              (application setup runtime leaks) actor)).lastEmitted ≠ none :=
                by
          rw [LateKey.respond_lastEmitted, sends]
          exact Option.some_ne_none _
        have silenceZero : silenceFactor (LateKey.ofView setup runtime leaks
          actor
            ((control.execution.respond (application setup runtime leaks) actor response).recall
              actor)
            ((control.execution.respond (application setup runtime leaks) actor response).observe
              (application setup runtime leaks) actor)) = 0 := by
          unfold silenceFactor
          simp [lastSome]
        have uniform : 1 / ((trembleSlots setup bounds).card : ℝ) ≤ slotTierFactor (runtime :=
          runtime) bounds
            (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
              (control.execution.observe (application setup runtime leaks) actor))
            (LateKey.ofView setup runtime leaks actor
              ((control.execution.respond (application setup runtime leaks) actor response).recall
                actor)
              ((control.execution.respond (application setup runtime leaks) actor response).observe
                (application setup runtime leaks) actor)) := by
          have owned := (PublicView.ownTurn?_spec _ actor event turn).2
          cases node : nodeView (graph setup) event with
          | sample payload law outputEq codeEq =>
              have none := nodeView_sample_actor outputEq codeEq
              rw [owned] at none
              cases none
          | bind owner payload outputEq codeEq =>
              rw [slotTierFactor_of_bind (runtime := runtime) bounds pending node]
              unfold pendingBindingSlotFactor
              cases last : (LateKey.ofView setup runtime leaks actor
                  ((control.execution.respond (application setup runtime leaks) actor
                    response).recall
                    actor)
                  ((control.execution.respond (application setup runtime leaks) actor
                    response).observe
                    (application setup runtime leaks) actor)).lastEmitted with
              | none => exact absurd last lastSome
              | some _ => exact le_rfl
          | resolve owner payload binding checks outputEq codeEq =>
              rw [slotTierFactor_of_resolve (runtime := runtime) bounds pending node]
              unfold transmitFactor
              rw [silenceZero, sub_zero]
              have : (1 : ℝ) ≤ (trembleSlots setup bounds).card := by exact_mod_cast slotsPos
              rw [div_le_one (by linarith)]
              exact this
        exact cube_le_slotError_of_slot_ge (scale_pos n).le (small n) (floor_pos n)
          (floored (by rw [sends]; exact Option.some_ne_none _)) slotsPos mainNonneg
          (silenceFactor_mem (runtime := runtime) _).1 uniform
  by_cases isLate : LateDelivery setup runtime leaks actor (some (control.execution.recall actor,
      control.execution.observe (application setup runtime leaks) actor))
  · have keyed : ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
        (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler) agent :=
      ⟨isLate, notFree⟩
    have weightsEq : keyWeights setup runtime leaks bounds horizon scheduler (weights n)
        (some (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
          (control.execution.observe (application setup runtime leaks) actor))) =
        weights n (.inr (some ⟨agentLateKey setup runtime leaks bounds (initialLaw setup) horizon
          scheduler agent, ⟨agent, keyed⟩, rfl⟩)) := by
      have present : some (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
          (control.execution.observe (application setup runtime leaks) actor)) ∈ Set.range
            fun agent : {agent : (onePacketN).InformationAgent (onePacketN).playedInformation //
              ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
                (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler)
                  agent} =>
            agentLateKey setup runtime leaks bounds (initialLaw setup) horizon scheduler agent.1 :=
        ⟨⟨agent, keyed⟩, rfl⟩
      unfold keyWeights
      rw [dite_eq_left_of_eq_true (eq_true present)]
      rfl
    have mixture := freeKeyedMixture_of_keyed (key := agentLateKey setup runtime leaks bounds
      (initialLaw setup) horizon scheduler) (weights n)
      (onePacketUnforced setup runtime leaks bounds horizon scheduler scale scale_pos scale_le_one
        n)
      (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree keyed
    have profileEq : certificateProfile setup runtime leaks bounds horizon scheduler sequence scale
        scale_pos scale_le_one weights n actor (some (control.execution.recall actor,
          control.execution.observe (application setup runtime leaks) actor)) =
        slotTrembledChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (scale n)
          (scale_pos n).le (scale_le_one n) actor _
          ((keyWeights setup runtime leaks bounds horizon scheduler (weights n)
            (some (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
              (control.execution.observe (application setup runtime leaks) actor)))).bind
            (lateChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (sequence n)
              actor _))
          (PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
            actor _))
          (slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (sequence n)
            actor _) := by
      change (onePacketN).agentBehavior _ _ _ agent.1 agent.2.1 = _
      rw [atAgent, mixture, weightsEq]
      exact bind_lateComponent setup runtime leaks bounds (initialLaw setup) horizon scheduler
        (sequence n) _ (scale n) (scale_pos n).le (scale_le_one n) actor _
    have mainEq : mainFactor bounds (keyWeights setup runtime leaks bounds
      horizon scheduler (weights n)
        (some (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
          (control.execution.observe (application setup runtime leaks) actor))))
        (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
          (control.execution.observe (application setup runtime leaks) actor))
        (LateKey.ofView setup runtime leaks actor
          ((control.execution.respond (application setup runtime leaks) actor response).recall
            actor)
          ((control.execution.respond (application setup runtime leaks) actor response).observe
            (application setup runtime leaks) actor)) =
        ∑ option, ((keyWeights setup runtime leaks bounds horizon scheduler (weights n)
          (some (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
            (control.execution.observe (application setup runtime leaks) actor)))) option).toReal *
          lateOptionFactor bounds
            (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
              (control.execution.observe (application setup runtime leaks) actor))
            (LateKey.ofView setup runtime leaks actor
              ((control.execution.respond (application setup runtime leaks) actor response).recall
                actor)
              ((control.execution.respond (application setup runtime leaks) actor response).observe
                (application setup runtime leaks) actor)) option := by
      unfold mainFactor
      simp only [keyLate.mpr isLate, ↓reduceIte]
    refine ⟨_, _, _, mainFactor bounds
      (keyWeights setup runtime leaks bounds horizon scheduler (weights n)
        (some (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
          (control.execution.observe (application setup runtime leaks) actor))))
      (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
        (control.execution.observe (application setup runtime leaks) actor))
      (LateKey.ofView setup runtime leaks actor
        ((control.execution.respond (application setup runtime leaks) actor response).recall actor)
        ((control.execution.respond (application setup runtime leaks) actor response).observe
          (application setup runtime leaks) actor)), _, _, profileEq, ?_, silenceMass, slotMass,
      responseEq.symm, ?_⟩
    · rw [bind_lateOption_toReal, mainEq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun option _ => ?_
      rw [lateMass option]
      ring
    · rw [responseEq]
      exact cube _ (mainFactor_mem (runtime := runtime) bounds _ _ _).1
  · have unkeyed : ¬ ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
        (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler) agent :=
      fun keyed => isLate keyed.1
    have mixture := freeKeyedMixture_of_not_keyed (key := agentLateKey setup runtime leaks bounds
      (initialLaw setup) horizon scheduler) (weights n)
      (onePacketUnforced setup runtime leaks bounds horizon scheduler scale scale_pos scale_le_one
        n)
      (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree unkeyed
    have profileEq : certificateProfile setup runtime leaks bounds horizon scheduler sequence scale
        scale_pos scale_le_one weights n actor (some (control.execution.recall actor,
          control.execution.observe (application setup runtime leaks) actor)) =
        slotTrembledChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (scale n)
          (scale_pos n).le (scale_le_one n) actor _
          (honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (sequence n)
            actor _)
          (PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
            actor _))
          (slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (sequence n)
            actor _) := by
      change (onePacketN).agentBehavior _ _ _ agent.1 agent.2.1 = _
      rw [atAgent, mixture]
      rfl
    have mainEq : mainFactor bounds (keyWeights setup runtime leaks bounds
      horizon scheduler (weights n)
        (some (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
          (control.execution.observe (application setup runtime leaks) actor))))
        (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
          (control.execution.observe (application setup runtime leaks) actor))
        (LateKey.ofView setup runtime leaks actor
          ((control.execution.respond (application setup runtime leaks) actor response).recall
            actor)
          ((control.execution.respond (application setup runtime leaks) actor response).observe
            (application setup runtime leaks) actor)) =
        honestFactor
          (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
            (control.execution.observe (application setup runtime leaks) actor))
          (LateKey.ofView setup runtime leaks actor
            ((control.execution.respond (application setup runtime leaks) actor response).recall
              actor)
            ((control.execution.respond (application setup runtime leaks) actor response).observe
              (application setup runtime leaks) actor)) := by
      unfold mainFactor
      exact ite_eq_right_iff.mpr fun late => absurd (keyLate.mp late) isLate
    refine ⟨_, _, _, mainFactor bounds
      (keyWeights setup runtime leaks bounds horizon scheduler (weights n)
        (some (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
          (control.execution.observe (application setup runtime leaks) actor))))
      (LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
        (control.execution.observe (application setup runtime leaks) actor))
      (LateKey.ofView setup runtime leaks actor
        ((control.execution.respond (application setup runtime leaks) actor response).recall actor)
        ((control.execution.respond (application setup runtime leaks) actor response).observe
          (application setup runtime leaks) actor)), _, _, profileEq, ?_, silenceMass, slotMass,
      responseEq.symm, ?_⟩
    · rw [mainEq]
      exact honestMass
    · rw [responseEq]
      exact cube _ (mainFactor_mem (runtime := runtime) bounds _ _ _).1

/-- **The slot law of the certificate's profile.** At every response step of
the one-packet game by a forced player other than the observer, from a state
forced for the observer, with positive content, the certificate's profile at
the responder's information is a slot-trembled component whose main, silence
and slot-tier laws give the realized choice its content factor times factors
whose slot combination is the step response, and the cube of the scale stays
within the error. The responder's disclosure is required to be canonical at
states forced for the observer. -/
theorem certificate_slotLaw (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
    [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]
    (floored : ∀ n, floor n ≤ contentFloor setup runtime leaks bounds horizon scheduler (sequence
      n))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (who : Player)
    (canonical : ∀ {control : (application setup runtime leaks).Control},
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some control) → ∀ actor, ForcedState setup runtime leaks who (some
          control) →
      actor ≠ who → DisclosureCanonical setup runtime leaks bounds actor (control.execution.recall
        actor)
        (control.execution.observe (application setup runtime leaks) actor))
    (n : ℕ) {before after : (application setup runtime leaks).ProtocolState}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
      before
      ⟨joint, legal⟩).support) (control next : (application setup runtime leaks).Control)
    (actor : Player) (initialized : before = some control) (reached : after = some next)
    (acting : control.actor = some actor) (other : actor ≠ who)
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup) horizon
      scheduler actor ((application setup runtime leaks).observe actor (some control)))
    (positive : 0 < contentFactor setup runtime leaks (sequence n) actor control.execution
      next.execution
      ((joint actor).getD ⟨none⟩))
    (observerForced : ForcedState setup runtime leaks who before) :
    ∃ (main alternative slot : PMF ((onePacketInformation setup runtime leaks bounds horizon
        scheduler).Choice actor
          ((onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf actor prior)))
      (mainFactor' alternativeFactor slotFactor : ℝ),
      certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n actor
          ((onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf actor prior) =
        slotTrembledChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (scale n)
          (scale_pos n).le (scale_le_one n) actor _ main alternative slot ∧
      (main (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor)).toReal =
        contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
          ((joint actor).getD ⟨none⟩) * mainFactor' ∧
      (alternative (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor)).toReal =
        contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
          ((joint actor).getD ⟨none⟩) * alternativeFactor ∧
      (slot (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor)).toReal =
        contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
          ((joint actor).getD ⟨none⟩) * slotFactor ∧
      slotCombination (scale n) mainFactor' alternativeFactor slotFactor =
        stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks bounds horizon
          scheduler (weights n))
          (scale n) (operationalState setup runtime leaks before) (operationalState setup runtime
            leaks after) ∧
      scale n ^ 3 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card *
        (contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
          ((joint actor).getD ⟨none⟩) *
        stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks bounds horizon
          scheduler (weights n))
          (scale n) (operationalState setup runtime leaks before)
          (operationalState setup runtime leaks after)) := by
  obtain ⟨response, chosenJoint, member, nextEq, infoEq⟩ :=
    onePacket_response_step (runtime := runtime) prior joint legal realized control next
      initialized reached acting
  have floorStep := contentFloor_le_of_step (runtime := runtime) (sequence n) prior joint legal
    realized control next
    initialized reached actor positive
  subst initialized reached
  have played : (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf actor
    prior ∈
      (onePacketN).playedInformation actor :=
    (onePacketN).mem_playedInformation (history := ⟨some control, prior⟩) legal.1
  have observed : (application setup runtime leaks).observe actor (some control) =
      some (control.execution.recall actor,
        control.execution.observe (application setup runtime leaks) actor) := by
    simp [ReactiveApplication.observe, acting]
  rw [observed] at forced
  rw [chosenJoint, Option.getD_some] at positive floorStep ⊢
  exact certificate_slotLaw_at (runtime := runtime) sequence scale scale_pos scale_le_one small
    floor floor_pos covers
    capacity weights n prior acting forced (canonical prior actor observerForced other) response
    member nextEq positive (fun _ => (floored n).trans floorStep) _ infoEq played _ chosenJoint

end Profile

end Vegas
