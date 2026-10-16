/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceTimingPolicy
import Vegas.Game.PhasePublicCompletion
import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPools

/-! # Operational timing pools in the actual phased finite menu

The key retains public phase identities, clocks, envelopes, receipts and physical
slot freshness. It omits the masked source store, private preparation values and
private source actions. At openings it also retains the value to be delivered.
Equality of these data is not asserted to identify posteriors or success scores.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The physical data available for timing and serial choices, retaining
freshness but discarding the private meanings of prepared candidates. -/
structure PhaseOperationalView (graph : EventGraph Player L) where
  application : PhasePublicView graph
  messages : MessageNetwork.PlayerView Player (CommitAttemptPacket graph)
  receipts : List (MessageId Player × Bool)
  fresh : CandidateSlot graph → Bool

section Operational

variable {graph : EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

def phaseOperationalView (view : (phaseApplication runtime leaks).PlayerView) :
    PhaseOperationalView graph :=
  ⟨view.application.2, view.messages, view.receipts, fun slot =>
    match view.application.1.candidates slot with
    | .fresh => true
    | _ => false⟩

/-- Only the current owned opening contributes a delivered private binding.
At a binding callback no earlier private result is inserted into the key. -/
def phaseDeliveredValue (who : Player) (view : (phaseApplication runtime leaks).PlayerView) :
    Option (Σ kind : EventField Player L, Option kind.Value) :=
  match view.application.2.native.ownTurn? who with
  | none => none
  | some event =>
      match nodeView graph event with
      | .resolve owner payload binding _ _ _ =>
          some ⟨.binding owner payload, binding.get? view.application.1.observation.store⟩
      | _ => none

/-- The actual erased owner word retains all attempts and signed envelopes,
including their handles and authorization. It does not identify an owner input
with a source information site or assume any value-independent likelihood. -/
structure PhaseTimingKey (graph : EventGraph Player L) where
  owner : Player
  current : PhaseOperationalView graph
  recalled : List (PhaseOperationalView graph × Option (Message Player (CommitAttemptPacket graph)))
  delivered : Option (Σ kind : EventField Player L, Option kind.Value)

def phaseTimingKey (who : Player) :
    (phaseApplication runtime leaks).Info → Option (PhaseTimingKey graph)
  | none => none
  | some (past, view) => some
      ⟨who, phaseOperationalView runtime leaks view,
        past.map fun entry =>
          (phaseOperationalView runtime leaks entry.beforeView, entry.emitted),
        phaseDeliveredValue runtime leaks who view⟩

/-- Public readiness with insufficient protected inclusion slack. This is a
classification of actual input data, not an assertion that the event must fail. -/
def PhaseUnprotected (bound : graph.EventId → Nat) (who : Player)
    (input : (phaseApplication runtime leaks).Info) : Prop :=
  ∃ past view event, input = some (past, view) ∧
    PhaseRuntimeState.requests view.application.2 who ⟨view.application.2.attempt, event⟩ ∧
    ¬ view.application.2.native.InclusionFitsDeadline runtime bound event

end Operational

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).InfoState who)]

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Publicly excluded agents remain free. Clear unprotected agents share only
their erased operational key; all remaining agents retain the source recipe. -/
def phaseTimingPool :=
  freeKeyedPool
    (fun agent : (N).InformationAgent (N).playedInformation =>
      PhasePublicExclusion setup mode runtime leaks agent.2.1)
    (fun agent => PhaseUnprotected runtime leaks bound agent.1 agent.2.1)
    (fun agent => phaseTimingKey runtime leaks agent.1 agent.2.1)

abbrev PhaseTimingPart := FreeKeyedPart
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks agent.2.1)
  (fun agent => PhaseUnprotected runtime leaks bound agent.1 agent.2.1)
  (fun agent => phaseTimingKey runtime leaks agent.1 agent.2.1)
  (LateOption bounds.candidateCount)

/-- Free singleton parts index all raw menu choices. Keyed parts retain the
original auxiliary draw before encoding their timing and serial option. -/
def phaseTimingComponent (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation) :
    PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
        (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent) →
      PMF ((N).Choice agent.1 agent.2.1) :=
  freeKeyedComponent
    (fun agent choice => mix noise noiseNonnegative noiseBounded
      ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) (PMF.pure choice))
    (fun agent => phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
        slotBounded agent.1 agent.2.1)
    (fun agent option => phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
        slotBounded agent.1 agent.2.1 option)
    agent

theorem phaseTimingComponent_fullSupport (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (positive : 0 < noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (part : PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent)) :
    FullSupport (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler
      bound wellFormed assessment noise positive.le noiseBounded slotWeight slotNonnegative
        slotBounded agent part) := by
  apply freeKeyedComponent_fullSupport
  · intro player choice other
    let := Fintype.ofFinite ((N).Choice player.1 player.2.1)
    exact mem_support_mix_left _ _ _ positive (PMF.mem_support_uniformOfFintype other)
  · intro player
    exact phaseSourcePerturbedStrategy_fullSupport setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise positive noiseBounded slotWeight slotNonnegative
        slotBounded player.1 player.2.1
  · intro player option
    exact phaseSourceTimingComponent_fullSupport setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise positive noiseBounded slotWeight slotNonnegative
        slotBounded player.1 player.2.1 option

/-- With vanishing raw noise, a publicly excluded singleton's components
converge to its individual pure choices, regardless of all source and slot laws. -/
theorem phaseTimingComponent_free_converges (wellFormed : setup.WellFormed)
    (sourceSequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ noise n) (bounded : ∀ n, noise n ≤ 1)
    (vanishes : Filter.Tendsto noise Filter.atTop (nhds 0))
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (excluded : PhasePublicExclusion setup mode runtime leaks agent.2.1)
    (part : PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent)) :
    let identify := freeIdentify
      (free := fun agent : (N).InformationAgent (N).playedInformation =>
        PhasePublicExclusion setup mode runtime leaks agent.2.1)
      (keyed := fun agent => PhaseUnprotected runtime leaks bound agent.1 agent.2.1)
      (key := fun agent => phaseTimingKey runtime leaks agent.1 agent.2.1)
      (Opt := LateOption bounds.candidateCount) excluded
    PMFConvergesPointwise (fun n => phaseTimingComponent setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (sourceSequence n) (noise n) (nonnegative n) (bounded n)
        (slotWeight n) (slotNonnegative n) (slotBounded n) agent part)
      (PMF.pure (identify part)) := by
  intro identify
  have same : (fun n => phaseTimingComponent setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed (sourceSequence n) (noise n) (nonnegative n) (bounded n)
        (slotWeight n) (slotNonnegative n) (slotBounded n) agent part) =
      fun n => mix (noise n) (nonnegative n) (bounded n)
        ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1)
        (PMF.pure (identify part)) := by
    funext n
    exact freeKeyedComponent_of_free _ _ _ excluded part
  rw [same]
  exact pmfConvergesPointwise_mix_zero noise nonnegative bounded vanishes _ _


/-- Every component outside public exclusion retains the same independent
slot-tier lower bound, including components that deliberately choose WAIT. -/
theorem phaseTimingComponent_ge_slot (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (unflagged : ¬ PhasePublicExclusion setup mode runtime leaks agent.2.1)
    (part : PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent))
    (choice : (N).Choice agent.1 agent.2.1) :
    (1 - noise) * slotWeight *
        ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
          horizon scheduler agent.1 agent.2.1) choice).toReal ≤
      (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded agent part choice).toReal := by
  classical
  let free := fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks agent.2.1
  let keyed := fun agent : (N).InformationAgent (N).playedInformation =>
    PhaseUnprotected runtime leaks bound agent.1 agent.2.1
  let key := fun agent : (N).InformationAgent (N).playedInformation =>
    phaseTimingKey runtime leaks agent.1 agent.2.1
  let freeLaw := fun (agent : (N).InformationAgent (N).playedInformation)
    (choice : (N).Choice agent.1 agent.2.1) => mix noise noiseNonnegative noiseBounded
      ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) (PMF.pure choice)
  let prescribed := fun agent : (N).InformationAgent (N).playedInformation =>
    phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
      wellFormed
      assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
        agent.1 agent.2.1
  let timed := fun (agent : (N).InformationAgent (N).playedInformation) option =>
    phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler wellFormed
      assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
        agent.1 agent.2.1 option
  obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free (free := free) (keyed := keyed)
    (key := key) freeLaw prescribed timed (agent := agent) unflagged
  change _ ≤ ((freeKeyedComponent freeLaw prescribed timed agent part) choice).toReal
  rw [same part]
  by_cases selected : ownedKeyed free keyed agent
  · obtain ⟨option, chosen⟩ := keyedComponent_of_keyed prescribed timed selected (identify part)
    rw [chosen]
    exact phaseSourceTimingComponent_ge_slot setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
        slotBounded agent.1 agent.2.1 option choice
  · rw [keyedComponent_of_not_keyed prescribed timed selected]
    exact phaseSourcePerturbedStrategy_ge_slot setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
        slotBounded agent.1 agent.2.1 choice

/-- Arbitrary common pool weights preserve the independent slot-tier bound.
The estimate uses the actual component mixture, not a canonical-profile proxy. -/
theorem phaseTimingComponent_mixture_ge_slot (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (unflagged : ¬ PhasePublicExclusion setup mode runtime leaks agent.2.1)
    (weights : PMF (PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent)))
    (choice : (N).Choice agent.1 agent.2.1) :
    (1 - noise) * slotWeight *
        ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
          horizon scheduler agent.1 agent.2.1) choice).toReal ≤
      ((weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        bound wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded agent)) choice).toReal := by
  rw [toReal_bind_apply]
  have lower := expect_mono
    (fun part _ => phaseTimingComponent_ge_slot setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
        slotNonnegative slotBounded agent unflagged part choice)
    (payoffIntegrable_constant weights _)
    (payoffIntegrable_of_bounded weights _ (C := 1) (fun part => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa only [ENNReal.ofReal_one] using PMF.coe_le_one _ _)))
  simpa only [expect_constant] using lower

end Vegas
