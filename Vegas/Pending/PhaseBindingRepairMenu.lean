/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairObservationStep

/-! # Actual raw and count support for a repaired private binding preparation -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- A binding's actual signed envelope contains no private preparation data.
Both original full recalls determine its same physical sender serial. -/
theorem binding_envelope (frame : Frame runtime leaks memory owner original repaired)
    (left : PhaseCount.CountRecall runtime leaks original)
    (right : PhaseCount.CountRecall runtime leaks repaired)
    (event : graph.EventId) (serial : Nat) (first second : Option (Raw L)) :
    PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
        (original.observe (phaseApplication runtime leaks) owner)
          ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩ =
      PhaseCount.localEnvelope runtime leaks owner (repaired.recall owner)
        (repaired.observe (phaseApplication runtime leaks) owner)
          ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩ := by
  have serials : (phaseApplication runtime leaks).submissionCount (original.recall owner) =
      (phaseApplication runtime leaks).submissionCount (repaired.recall owner) := by
    rw [← left.2.1 owner, ← right.2.1 owner, frame.network]
  have publics : original.application.current.native.publicView =
      repaired.application.current.native.publicView := frame.live.publicView
  unfold PhaseCount.localEnvelope
  change (⟨(owner, _), ⟨original.application.publicView.attempt,
    PhaseCount.maskPacket original.application.publicView
      ⟨.commitment event (owner, .prepared serial), none,
        original.application.current.native.publicView.tokenFor
          (.commitment event (owner, .prepared serial))⟩⟩⟩ :
            Message Player (CommitAttemptPacket graph)) = _
  rw [serials, frame.publicView, publics]
  rfl

variable [Fintype Player]

/-- Raw syntax and the permanent count verdict both transport to the chosen
bounded preparation. Target menu support is proved from the actual source member. -/
theorem binding_menu (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (left : PhaseCount.CountRecall runtime leaks original)
    (right : PhaseCount.CountRecall runtime leaks repaired)
    (event : graph.EventId) (serial : Nat) (first second : Option (Raw L))
    (bounded : bounds.AllowsOpening second)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        owner (original.recall owner) (original.observe (phaseApplication runtime leaks) owner)) :
    (⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        owner (repaired.recall owner)
          (repaired.observe (phaseApplication runtime leaks) owner) := by
  classical
  rw [PhaseCount.mem_onePacketActions] at member ⊢
  constructor
  · have rawAllowed := member.1
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at rawAllowed
    change (⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩ :
      WitnessedSubmission graph) ∈ bounds.submissions _ at rawAllowed
    have sourceBounds := (bounds.submissions_mem _ _).mp rawAllowed
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    change (⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩ :
      WitnessedSubmission graph) ∈ bounds.submissions _
    apply (bounds.submissions_mem _ _).mpr
    exact ⟨⟨sourceBounds.1.1, bounded⟩, trivial⟩
  · right
    refine ⟨⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩, rfl, ?_⟩
    have permitted : PhaseCount.permits
        ((phaseApplication runtime leaks).outputs (original.recall owner))
        (PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
          (original.observe (phaseApplication runtime leaks) owner)
            ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩) = true := by
      rcases member.2 with impossible | ⟨material, transmitted, allowed⟩
      · cases impossible
      · cases Option.some.inj transmitted
        exact allowed
    rw [← frame.outputs left.1 right.1 owner,
      ← frame.binding_envelope left right event serial first second]
    exact permitted

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
