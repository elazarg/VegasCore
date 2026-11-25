module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketComponents
public import Vegas.Game.OnePacketSlotDistribution
public import Vegas.Game.OnePacketExtension
public import Vegas.Game.OnePacketDistributionApproximation
public import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPools
public import Vegas.Game.OnePacketDelivery
public import Vegas.Game.OnePacketIntendedProjection

@[expose] public section

/-! # The pooled components of the one-packet certificate

The source is the intended game of a well-formed setup, observed through its
typed readout and the exclusion payoff it determines
(`Vegas.intendedReadoutExclusion`); the target is the one-packet game of the
supplied runtime, observed through its typed readout and native exclusion
payoff (`Vegas.readoutExclusion`). The utility of either observation is its
payoff component (`Vegas.payoffComponent`).

The agents outside the clear forced region are free, each alone in its pool
(`Vegas.FreeAgent`); forced late deliveries sharing a late-delivery key form a
pool with the late options as parts, and every other agent sits in a pool with
one part (`Vegas.onePacketPool`). Unforced agents tremble each choice, forced
late deliveries play the late component of each option, and every other agent
plays the slot-trembled prescribed component (`Vegas.onePacketComponent`); at a
positive scale every component has full support
(`Vegas.onePacketComponent_fullSupport`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts setup.informationGraph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
  (bounds : MessageBounds setup.informationGraph) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  [(application setup timeouts leaks).FiniteNature (initialDistribution setup) scheduler]
  [Finite setup.intendedProtocol.History]

local notation "Initial" => initialDistribution setup

section Certificate

local notation "onePacketN" =>
  onePacketModel setup timeouts leaks bounds (initialDistribution setup) horizon scheduler

variable [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds
    (initialDistribution setup) horizon
  scheduler).InfoState who)]

/-- The fallback of the one-packet certificate: some choice at every information
state. -/
def onePacketFallback (who : Player) :
    (onePacketModel setup timeouts leaks bounds Initial horizon scheduler).Policy who :=
  fun _ => Classical.arbitrary _

open Classical in
/-- The free laws of the one-packet certificate along a scale sequence. -/
def onePacketUnforced (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n)
    (scale_le_one : ∀ n, scale n ≤ 1) (n : ℕ)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    (onePacketN).Choice agent.1 agent.2.1 → PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  unforcedDistribution setup timeouts leaks bounds Initial horizon scheduler (scale n)
    (scale_pos n).le
    (scale_le_one n) agent

open Classical in
/-- The prescribed laws of the one-packet certificate along a source sequence
and a scale sequence. -/
def onePacketPrescribed (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1) (n : ℕ)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  slotPrescribedComponent setup timeouts leaks bounds Initial horizon scheduler
    (sequence n)
    (scale n) (scale_pos n).le (scale_le_one n) agent.1 agent.2.1

open Classical in
/-- The late laws of the one-packet certificate along a source sequence and a
scale sequence. -/
def onePacketLate (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
    (option : LateOption slots) : PMF ((onePacketN).Choice agent.1 agent.2.1) :=
  lateComponent setup timeouts leaks bounds Initial horizon scheduler (sequence n)
    (scale n)
    (scale_pos n).le (scale_le_one n) agent.1 agent.2.1 option

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α] (law : PMF α) (a : α) :
    law a = 1 := by
  rw [← law.tsum_coe, tsum_eq_single a (fun other different =>
    (different (Subsingleton.elim other a)).elim)]

omit [Finite setup.intendedProtocol.History] in
/-- **Mixtures of one-packet components keep as-if-honest play away from late
deliveries.** At every forced information state that some history reaches and
that is not a late delivery, every mixture of the components of the one-packet
certificate gives each choice at least the slot retention of the scale times
its as-if-honest mass: its components are all the slot-trembled prescribed
component. -/
theorem onePacketMixture_ge_honest_of_not_late
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ)
    (weights : ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialDistribution setup)
      horizon scheduler slots p))
    {who : Player} {info : (application setup timeouts leaks).Info}
    (notLate : ¬ LateDelivery setup timeouts leaks who info)
    (occurs : ∃ history : ((bounds.onePacketMenu timeouts leaks).protocol
      (initialDistribution setup)
      horizon scheduler).History, (onePacketN).infoOf who history.trace = info)
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks)
      (initialDistribution
      setup) horizon
      scheduler who info)
    (clear : info.isSome → (ClearInput timeouts) leaks info)
    (choice : (onePacketN).Choice who info) :
    slotRetention (scale n) * ((honestProfile setup timeouts leaks bounds
      (initialDistribution setup) horizon
        scheduler (sequence n) who info) choice).toReal ≤
      (((onePacketN).agentBehavior (onePacketN).playedInformation
        (onePacketFallback setup timeouts leaks bounds horizon scheduler)
        (fun agent => (weights (onePacketPool setup timeouts leaks bounds
          (initialDistribution setup)
          horizon scheduler
          agent)).bind
          (freeKeyedComponent
            (onePacketUnforced setup timeouts leaks bounds horizon scheduler scale scale_pos
              scale_le_one n)
            (onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale
              scale_pos
              scale_le_one n)
            (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n) agent)) who info) choice).toReal := by
  classical
  have retention_le_one := slotRetention_le_one (scale_pos n).le (scale_le_one n)
  by_cases inactive : info = none
  · subst info
    have : Subsingleton ((onePacketN).Choice who none) :=
      InformationModel.subsingleton_choice_of_menu_subsingleton _ _ Set.subsingleton_singleton
    rw [apply_eq_one_of_subsingleton _ choice, apply_eq_one_of_subsingleton _ choice,
      ENNReal.toReal_one, mul_one]
    exact retention_le_one
  have actualClear := clear (by
    cases info with
    | none => exact (inactive rfl).elim
    | some _ => rfl)
  by_cases present : info ∈ (onePacketN).playedInformation who
  · let agent : (onePacketN).InformationAgent (onePacketN).playedInformation :=
      ⟨who, ⟨info, present⟩⟩
    have notFree : ¬ FreeAgent setup timeouts leaks bounds (initialDistribution setup)
      horizon scheduler agent :=
      fun unforced => unforced ⟨actualClear, forced⟩
    have notKeyed : ¬ ownedKeyed (FreeAgent setup timeouts leaks bounds (initialDistribution setup)
      horizon scheduler)
        (LateDeliveryAgent setup timeouts leaks bounds (initialDistribution setup) horizon
          scheduler)
          agent :=
      fun keyed => notLate keyed.1
    obtain ⟨identify, componentEq⟩ := freeKeyedComponent_of_not_free
      (key := agentLateKey setup timeouts leaks bounds (initialDistribution setup) horizon
        scheduler)
      (onePacketUnforced setup timeouts leaks bounds horizon scheduler scale scale_pos scale_le_one
        n)
      (onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree
    have constant : ∀ part, freeKeyedComponent
        (onePacketUnforced setup timeouts leaks bounds horizon scheduler scale scale_pos
          scale_le_one n)
        (onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent part =
        onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n agent := fun part => by
      rw [componentEq]
      exact keyedComponent_of_not_keyed _ _ notKeyed _
    have atAgent := (onePacketN).agentBehavior_at (onePacketN).playedInformation
      (onePacketFallback setup timeouts leaks bounds horizon scheduler)
      (fun agent => (weights (onePacketPool setup timeouts leaks bounds (initialDistribution setup)
        horizon scheduler
        agent)).bind
        (freeKeyedComponent
          (onePacketUnforced setup timeouts leaks bounds horizon scheduler scale scale_pos
            scale_le_one n)
          (onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale
            scale_pos
            scale_le_one n)
          (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n) agent)) agent
    change _ ≤ (((onePacketN).agentBehavior _ _ _ agent.1 agent.2.1) choice).toReal
    have mixture : (weights (onePacketPool setup timeouts leaks bounds (initialDistribution setup)
      horizon scheduler agent)).bind
        (freeKeyedComponent
          (onePacketUnforced setup timeouts leaks bounds horizon scheduler scale scale_pos
            scale_le_one n)
          (onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale
            scale_pos
            scale_le_one n)
          (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n) agent) =
        onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n agent := by
      rw [show freeKeyedComponent
          (onePacketUnforced setup timeouts leaks bounds horizon scheduler scale scale_pos
            scale_le_one n)
          (onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale
            scale_pos
            scale_le_one n)
          (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n) agent = fun _ =>
          onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n agent from funext constant]
      exact PMF.bind_const _ _
    rw [atAgent]
    refine le_of_le_of_eq (slotTrembledChoice_ge_main setup timeouts leaks bounds
      (initialDistribution
      setup) horizon
      scheduler (scale_pos n).le (scale_le_one n) who info
      (honestChoice setup timeouts leaks bounds (initialDistribution setup) horizon scheduler
        (sequence n)
        who info)
      (PMF.pure (silenceChoice setup timeouts leaks bounds
        (initialDistribution setup) horizon scheduler who
        info))
      (slotChoice setup timeouts leaks bounds (initialDistribution setup) horizon scheduler
        (sequence n) who
        info)
      choice) ?_
    exact congrArg (fun law => (law choice).toReal) mixture.symm
  · have none : info = none := by
      obtain ⟨history, infoEq⟩ := occurs
      cases infoCase : info with
      | none => rfl
      | some observed =>
          exfalso
          apply present
          rw [← infoEq]
          apply (onePacketN).mem_playedInformation
          have active : (application setup timeouts leaks).observe who history.state = some
            observed :=
            ((bounds.onePacketMenu timeouts leaks).info (initialDistribution setup) horizon
              scheduler who history.trace).symm.trans (infoEq.trans infoCase)
          have isSome := ((application setup timeouts leaks).observe_isSome who history.state).mp
            (by rw [active]; rfl)
          intro stopped
          revert stopped isSome
          cases history.state with
          | none => exact fun _ stopped => stopped.elim
          | some control =>
              rintro actorSome ⟨_, actorNone⟩
              simp [ReactiveApplication.actor, actorNone] at actorSome
    exact (inactive none).elim


/-- Profiles assembled from mixtures of the components of the one-packet
certificate: at each index, every agent mixes its pool's components with the
pool's weights. -/
def OnePacketAssembled (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialDistribution setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) : Prop :=
  ∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior (onePacketN).playedInformation
    (onePacketFallback setup timeouts leaks bounds horizon scheduler)
    fun agent => (weights n (onePacketPool setup timeouts leaks bounds (initialDistribution setup)
      horizon scheduler agent)).bind
      (freeKeyedComponent
        (onePacketUnforced setup timeouts leaks bounds horizon scheduler scale scale_pos
          scale_le_one n)
        (onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent)

end Certificate

end Vegas
