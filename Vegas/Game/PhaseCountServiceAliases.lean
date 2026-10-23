/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourcePolicy
import Vegas.Pending.PhaseCountServiceReference
import Vegas.Pending.PhasePrivateService
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseBindingResponseWitness
import Interaction.ReactiveRecordedResponse
import Vegas.Game.PhaseObservableSourceQuery
import Vegas.Game.PhaseRecoveryDomainValue
import Vegas.Pending.PhaseResponseNormalization
import Interaction.ReactiveAliasLaw

/-! # Operational aliases in the selected counted source prescription

The actual source query uses the current physical view. The timing word,
eligibility test and raw menu retain observations and emissions, but ignore
the hidden syntax of equivalent evidence requests. The original raw aliases
are summed by the existing response-normalization history projection.
-/

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

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

omit [Fintype Player] in
/-- Normalize response aliases only for the selected owners. Every other
owner's actual raw recall, in particular the focal information, is retained. -/
def phaseCountServiceNormalization (owners : Finset Player) : (app).SubmissionNormalization where
  normalize who view known material := if who ∈ owners then
    (PhaseCount.normalization runtime leaks).normalize who view known material else material
  idempotent who view known material := by
    by_cases inside : who ∈ owners
    · simpa only [ite_eq_left inside] using
        (PhaseCount.normalization runtime leaks).idempotent who view known material
    · simp only [ite_eq_right inside]
  packet state who known material := by
    by_cases inside : who ∈ owners
    · simpa only [ite_eq_left inside] using
        (PhaseCount.normalization runtime leaks).packet state who known material
    · simp only [ite_eq_right inside]
  submit state who known material := by
    by_cases inside : who ∈ owners
    · simpa only [ite_eq_left inside] using
        (PhaseCount.normalization runtime leaks).submit state who known material
    · simp only [ite_eq_right inside]

omit [Fintype Player] in
theorem phaseCountServiceNormalization_recall_fixed (owners : Finset Player) (who : Player)
    (outside : who ∉ owners) (past : List (app).PlayerEntry) :
    (phaseCountServiceNormalization setup mode runtime leaks owners).recall who past = past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [ReactiveApplication.SubmissionNormalization.recall_append_action, ih]
      rcases entry with ⟨before, ⟨transmitted⟩, emitted⟩
      cases transmitted <;>
        simp only [ReactiveApplication.SubmissionNormalization.action,
          phaseCountServiceNormalization, ite_eq_right outside]

omit [Fintype Player] in
/-- A nonselected observer's complete native information is unchanged,
including its original raw actions rather than only an operational projection. -/
theorem phaseCountServiceNormalization_info_fixed (owners : Finset Player) (who : Player)
    (outside : who ∉ owners) (observed : (app).Info) :
    (phaseCountServiceNormalization setup mode runtime leaks owners).info who observed =
      observed := by
  cases observed with
  | none => rfl
  | some pair =>
      rcases pair with ⟨past, view⟩
      simp only [ReactiveApplication.SubmissionNormalization.info, Option.map_some,
        phaseCountServiceNormalization_recall_fixed setup mode runtime leaks owners who outside]

omit [Fintype Player] in
theorem phaseCountService_submissionCount_normal_recall (normal : (app).SubmissionNormalization)
    (who : Player) (past : List (app).PlayerEntry) :
    (app).submissionCount (normal.recall who past) = (app).submissionCount past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [normal.recall_append_action, (app).submissionCount_append,
        (app).submissionCount_append, ih]
      rcases entry with ⟨before, ⟨transmitted⟩, emitted⟩
      cases transmitted <;> rfl

omit [Fintype Player] in
private theorem normalized_localEnvelope (normal : (app).SubmissionNormalization)
    (who actor : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (material : (app).Submission) :
    PhaseCount.localEnvelope runtime leaks actor (normal.recall who past) view material =
      PhaseCount.localEnvelope runtime leaks actor past view material := by
  simp only [PhaseCount.localEnvelope, phaseCountService_submissionCount_normal_recall,
    ReactiveApplication.ResponseMenu.knownPackets, normal.recall_outputs]

/-- The actual counted raw menu, including its evidence-request aliases,
depends on original recall only through unchanged emissions and send counts. -/
theorem phaseCountService_actions_normal_recall (normal : (app).SubmissionNormalization)
    (who actor : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    PhaseCount.onePacketActions runtime leaks bounds actor (normal.recall who past) view =
      PhaseCount.onePacketActions runtime leaks bounds actor past view := by
  classical
  have raw : (PhaseCount.rawMenu runtime leaks bounds).actions actor
      (normal.recall who past) view =
        (PhaseCount.rawMenu runtime leaks bounds).actions actor past view := by
    simp only [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions,
      ReactiveApplication.ResponseMenu.knownPackets, normal.recall_outputs]
  ext response
  simp only [PhaseCount.mem_onePacketActions, raw, PhaseCount.OnePacketResponse,
    normal.recall_outputs, normalized_localEnvelope]

end Vegas
