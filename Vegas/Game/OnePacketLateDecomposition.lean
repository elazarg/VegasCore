/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateSuccess
import Vegas.Game.OnePacketCertificateDischarge

/-! # The value decomposition of late deliveries

**Installed laws keep as-if-honest play from reached boundaries.** Installing a
law at a late delivery of an assembled profile leaves its play at every forced
information state as-if-honest play reaches from a reached boundary: such a
state is not a late delivery (`Vegas.not_lateDelivery_of_honestReachedFrom`), so
it is not the late delivery, and its components are the slot-trembled prescribed
component (`Vegas.installedLate_dominates`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- **Installed laws keep as-if-honest play from reached boundaries.** Under the
asynchronous contract with timely delays and retention of first covered
canonical packets, installing any law at a late delivery of a profile assembled
from mixtures of the components of the one-packet certificate gives, from every
one-packet history ending between rounds at a reached boundary decoding to a
point of the intended game, each choice at every forced information state
as-if-honest play reaches at least the slot retention of the scale times its
as-if-honest mass. -/
theorem installedLate_dominates {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (n : ℕ) {owner : Player} {late : (application setup leaks).Info}
    (lateDelivery : LateDelivery setup leaks owner late)
    (law : PMF ((onePacketN).Choice owner late))
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) (anchor : (application setup leaks).Execution) (rank : Nat)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (who : Player) (info : (application setup leaks).Info)
    (reachedInfo : HonestReachedFrom setup leaks bounds horizon scheduler (sequence n) start who
      info)
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who info)
    (choice : (onePacketN).Choice who info) :
    slotRetention (scale n) * ((honestProfile setup leaks bounds (initialLaw setup) horizon
        scheduler (sequence n) who info) choice).toReal ≤
      ((Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy owner
        (((targetSequence n).strategy owner).withLaw late law) who info) choice).toReal := by
  have notLate := not_lateDelivery_of_honestReachedFrom bounds contract timely (sequence n)
    retains reached point decoded intendedPoint start state reachedInfo
  have occurs : ∃ history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History,
      (onePacketN).infoOf who history.trace = info := by
    obtain ⟨_, history, _, infoEq⟩ := reachedInfo
    exact ⟨history, infoEq⟩
  have base := onePacketMixture_ge_honest_of_not_late setup leaks bounds horizon scheduler
    sequence scale scale_pos scale_le_one n (weights n) notLate occurs forced choice
  have agrees : Profile.update (sig := (onePacketN).behavioralSignature)
      (targetSequence n).strategy owner (((targetSequence n).strategy owner).withLaw late law)
      who info = (targetSequence n).strategy who info := by
    by_cases same : who = owner
    · subst same
      have different : info ≠ late := fun equal => notLate (equal ▸ lateDelivery)
      rw [Profile.update_same, BehavioralPolicy.withLaw_of_ne _ _ _ different]
    · rw [Profile.update_of_ne _ _ same]
  rw [agrees, assembled n]
  exact base

end Vegas
