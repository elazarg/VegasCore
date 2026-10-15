/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRepairRawSendingWitness

/-! # Every selected raw binding record retains its actual repair decomposition -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- This predicate records raw binding syntax, not the latent mixture tier
from which the action was sampled. A marked contribution is selected later. -/
def phaseRawBindingRecord (who : Player) (record : (N).InfoState who × (E).Action who) : Prop :=
  ∃ (event : (serviceGraph setup mode).EventId) (serial : Nat) (preparation : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup mode)),
    record.2 = ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩

/-- Each selected original raw binding has one actual same-slot marked image,
with ordinary chronological witnesses for the full words on both sides. -/
def PhaseRepairMarkedBindings (who : Player)
    (first second : List ((N).InfoState who × (E).Action who)) : Prop :=
  ∀ before record after, first = before ++ record :: after →
    phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler who record →
    ∃ imageBefore imageRecord imageAfter beforeSends beforeWaits afterSends afterWaits,
      second = imageBefore ++ imageRecord :: imageAfter ∧
      PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
        before imageBefore beforeSends beforeWaits ∧
      phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
        record imageRecord ∧
      PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
        after imageAfter afterSends afterWaits

theorem PhaseRepairMarkedBindings.nil (who : Player) :
    PhaseRepairMarkedBindings setup mode runtime leaks bounds plan horizon scheduler who [] [] := by
  intro before record after impossible
  have lengths := congrArg List.length impossible
  simp only [List.length_nil, List.length_append, List.length_cons] at lengths
  omega

/-- Prepending one actual callback preserves all earlier marked decompositions
and, for a raw binding head, installs its concrete same-slot witness. -/
theorem PhaseRepairMarkedBindings.cons (who : Player)
    (firstHead secondHead : (N).InfoState who × (E).Action who)
    (firstTail secondTail : List ((N).InfoState who × (E).Action who))
    (stepSends stepWaits sends waits : Nat)
    (head : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      [firstHead] [secondHead] stepSends stepWaits)
    (tail : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      firstTail secondTail sends waits)
    (marked : PhaseRepairMarkedBindings setup mode runtime leaks bounds plan horizon scheduler who
      firstTail secondTail)
    (markedHead : phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler who
        firstHead →
      phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
        firstHead secondHead) :
    PhaseRepairMarkedBindings setup mode runtime leaks bounds plan horizon scheduler who
      (firstHead :: firstTail) (secondHead :: secondTail) := by
  intro before record after decomposition raw
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at decomposition
      rcases decomposition with ⟨rfl, rfl⟩
      exact ⟨[], secondHead, secondTail, 0, 0, sends, waits, rfl, .nil, markedHead raw, tail⟩
  | cons earlier before =>
      simp only [List.cons_append, List.cons.injEq] at decomposition
      rcases decomposition with ⟨rfl, rest⟩
      obtain ⟨imageBefore, imageRecord, imageAfter, beforeSends, beforeWaits, afterSends,
        afterWaits, imageEq, beforePair, actual, afterPair⟩ := marked before record after rest raw
      refine ⟨secondHead :: imageBefore, imageRecord, imageAfter, stepSends + beforeSends,
        stepWaits + beforeWaits, afterSends, afterWaits, ?_, ?_, actual, afterPair⟩
      · simpa only [List.cons_append] using congrArg (secondHead :: ·) imageEq
      · simpa only [List.singleton_append] using head.append setup mode runtime leaks bounds plan
          horizon scheduler beforePair

end Vegas
