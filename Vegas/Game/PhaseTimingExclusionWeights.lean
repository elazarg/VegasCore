/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingRawMixture

/-! # Prescribed continuation laws inside the original timing-pool family -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
    scheduler).InfoState who)]

local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

/-- Replace only the free singleton pools by a prescribed continuation law.
All nonfree pools retain their original common operational weights. This is
an exact representation inside the same component family, not an optimality
or source-information assertion about the prescribed law. -/
def phaseTimingWeightsWithExclusionLaw
    (weights : (p : Pool) → PMF (Parts p))
    (prescribed : (agent : Agent) → PMF ((N).Choice agent.1 agent.2.1)) :
    (p : Pool) → PMF (Parts p)
  | .inl owner => prescribed owner.1
  | .inr keyed => weights (.inr keyed)

/-- Prescribing the post-exclusion continuation does not change any common
pool weight at a clear input. -/
theorem phaseTimingWeightsWithExclusionLaw_of_clear
    (weights : (p : Pool) → PMF (Parts p))
    (prescribed : (agent : Agent) → PMF ((N).Choice agent.1 agent.2.1))
    (agent : Agent) (clear : ¬ PhasePublicExclusion setup mode runtime leaks agent.2.1) :
    phaseTimingWeightsWithExclusionLaw setup mode runtime leaks bounds initial horizon scheduler
        bound weights prescribed (pool agent) = weights (pool agent) := by
  change phaseTimingWeightsWithExclusionLaw setup mode runtime leaks bounds initial horizon
    scheduler bound weights prescribed (freeKeyedPool isFree isKeyed poolKey agent) =
      weights (freeKeyedPool isFree isKeyed poolKey agent)
  generalize poolEq : freeKeyedPool isFree isKeyed poolKey agent = p
  cases p with
  | inl owner =>
    have nonfree := freeKeyedPool_of_not_free (free := isFree) (keyed := isKeyed)
      (key := poolKey) (agent := agent) clear
    rw [nonfree] at poolEq
    contradiction
  | inr keyed => rfl

/-- The actual original component mixture at an excluded input equals the
prescribed continuation with exactly its original raw uniform perturbation.
No new profile, decoder or changed native menu is hidden in the identity. -/
theorem phaseTimingComponent_with_exclusionLaw
    (weights : (p : Pool) → PMF (Parts p))
    (prescribed : (agent : Agent) → PMF ((N).Choice agent.1 agent.2.1))
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : Agent) (excluded : PhasePublicExclusion setup mode runtime leaks agent.2.1) :
    (phaseTimingWeightsWithExclusionLaw setup mode runtime leaks bounds initial horizon scheduler
        bound weights prescribed (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
            slotBounded agent) =
      mix noise noiseNonnegative noiseBounded
        ((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy initial horizon scheduler
          agent.1 agent.2.1) (prescribed agent) := by
  rw [phaseTimingComponent_mixture_raw_mixture]
  congr 1
  unfold phaseTimingComponent freeKeyedComponent phaseTimingPool
  rw [freeKeyedPool_of_free excluded]
  dsimp only [phaseTimingWeightsWithExclusionLaw]
  calc
    _ = (prescribed agent).bind PMF.pure := by
      apply congrArg ((prescribed agent).bind)
      funext choice
      simp only [freeKeyedComponentAt, ↓reduceDIte, mix_zero]
    _ = _ := PMF.bind_pure _

end Vegas
