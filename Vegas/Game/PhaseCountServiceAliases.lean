/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseSourcePolicy

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
