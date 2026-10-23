/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowResponse

/-! # Actual counted menu support under private preparation repair

The two literal recalls reconstruct the same signed inputs. A binding's
private evidence alias is summed by its actual absent certificate, while the
replacement preparation is checked against the original finite raw bound.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Any bounded private preparation may replace the counted source binding
at the same slot. Full old raw response syntax remains on the source side;
target membership follows from the actual packet and recall equalities. -/
theorem binding_response_member (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (network : left.network = right.network)
    (leftRecall : PhaseCount.CountRecall runtime leaks left)
    (rightRecall : PhaseCount.CountRecall runtime leaks right)
    (bounds : MessageBounds graph) (event : graph.EventId) (serial : Nat)
    (first second : Option (Raw L)) (evidence : EvidenceRequest graph)
    (bounded : bounds.AllowsOpening second)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (left.recall owner) (left.observe app owner)) :
    (⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (right.recall owner) (right.observe app owner) := by
  classical
  let source : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), first⟩, evidence⟩
  let target : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩
  rw [PhaseCount.mem_onePacketActions] at member ⊢
  have permitted : PhaseCount.permits ((app).outputs (left.recall owner))
      (PhaseCount.localEnvelope runtime leaks owner (left.recall owner)
        (left.observe app owner) source) = true := by
    rcases member.2 with impossible | ⟨material, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  have call : (PhaseCount.nativeMessage (PhaseCount.localEnvelope runtime leaks owner
      (left.recall owner) (left.observe app owner) source)).payload.call =
      .commitment event (owner, .prepared serial) := PhaseCount.maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [call] at correct
  have absent := correct.2.1
  have resolved : evidence.resolve owner
      (source.call.candidateAfter owner (left.observe app owner).application.1.candidates)
      ((ReactiveApplication.ResponseMenu.knownPackets (left.recall owner)
        (left.observe app owner)).map PhaseCount.nativeMessage) = none := by
    change (PhaseCount.maskPacket (left.observe app owner).application.2
      ⟨source.call.packet, _, _⟩).evidence = none at absent
    unfold PhaseCount.maskPacket at absent
    split at absent <;> split at absent <;> exact absent
  have outputs : (app).outputs (left.recall owner) = (app).outputs (right.recall owner) := by
    rw [← leftRecall.1 owner, ← rightRecall.1 owner, network]
  have serials : (app).submissionCount (left.recall owner) =
      (app).submissionCount (right.recall owner) := by
    rw [← leftRecall.2.1 owner, ← rightRecall.2.1 owner, network]
  have publicEq := frame.publicView owned
  have nativePublic : left.application.current.native.publicView =
      right.application.current.native.publicView := by
    rw [frame.current]
    exact native_publicView owned _
  have envelope : PhaseCount.localEnvelope runtime leaks owner (left.recall owner)
      (left.observe app owner) source = PhaseCount.localEnvelope runtime leaks owner
        (right.recall owner) (right.observe app owner) target := by
    unfold PhaseCount.localEnvelope
    rw [resolved]
    change (⟨(owner, _), ⟨left.application.publicView.attempt,
      PhaseCount.maskPacket left.application.publicView
        ⟨.commitment event (owner, .prepared serial), none,
          left.application.current.native.publicView.tokenFor
            (.commitment event (owner, .prepared serial))⟩⟩⟩ :
        Message Player (CommitAttemptPacket graph)) = _
    rw [serials, publicEq, nativePublic]
    rfl
  constructor
  · have sourceBound := member.1
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at sourceBound
    have sourceBounds := (bounds.submissions_mem _ _).mp sourceBound
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    apply (bounds.submissions_mem _ _).mpr
    exact ⟨⟨sourceBounds.1.1, bounded⟩, trivial⟩
  · right
    refine ⟨target, rfl, ?_⟩
    rw [← outputs, ← envelope]
    exact permitted

end Vegas.EventGraphRuntime.BindingShadow
