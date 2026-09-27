/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCheckpoint
import Vegas.Game.RevealServiceObservation
import Vegas.Pending.ReactiveBindingTranscript
import Vegas.Pending.ReactiveResponseRecall

/-! # Source views and dynamic native catalogues

Equal source views reconstruct the actual owned catalogue after canonical
bindings, samples, and guarded resolutions. Matching auxiliary transcripts and
own raw recall then reconstruct the complete native input and the exact known
message list used for authentic evidence and replay. Those auxiliary matches
are operational coupling obligations; no posterior equality is assumed here.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source view plus a matched auxiliary transcript reconstructs all genuine
native information used by a submission. Initial private inputs may be arbitrarily
correlated. The emitted-evidence conclusion covers every raw submission, including
new private preparation material, forwarding, and failed evidence requests. -/
theorem source_checkpoint_input_evidence_eq
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
    (covered : refs.CoversPrefix setup.program rank) (who : Player)
    (left right : Config Player L Γ)
    (nativeLeft nativeRight : (application setup leaks).Execution)
    (leftCheckpoint : SourceCheckpoint setup left refs rank nativeLeft.application.config)
    (rightCheckpoint : SourceCheckpoint setup right refs rank nativeRight.application.config)
    {leftInputs rightInputs : (graph setup).Inputs}
    (leftReachable : nativeLeft.application.config.Reachable leftInputs)
    (rightReachable : nativeRight.application.config.Reachable rightInputs)
    (leftRepresented : nativeLeft.application.CandidatesRepresented)
    (rightRepresented : nativeRight.application.CandidatesRepresented)
    (leftRecorded : nativeLeft.application.AcceptedRecorded)
    (rightRecorded : nativeRight.application.AcceptedRecorded)
    (leftValid : nativeLeft.application.BindingInvariant)
    (rightValid : nativeRight.application.BindingInvariant)
    (leftRecall : nativeLeft.InputRecall (application setup leaks))
    (rightRecall : nativeRight.InputRecall (application setup leaks))
    (sameSource : left.view who = right.view who)
    (clock : nativeLeft.application.clock = nativeRight.application.clock)
    (activated : nativeLeft.application.activatedAt = nativeRight.application.activatedAt)
    (grant : nativeLeft.application.serviceGrant = nativeRight.application.serviceGrant)
    (ledger : nativeLeft.network.ledger = nativeRight.network.ledger)
    (leaked : nativeLeft.network.leaked who = nativeRight.network.leaked who)
    (receipts : nativeLeft.receipts = nativeRight.receipts)
    (past : nativeLeft.recall who = nativeRight.recall who) :
    nativeLeft.observe (application setup leaks) who =
      nativeRight.observe (application setup leaks) who ∧
    nativeLeft.network.known who = nativeRight.network.known who ∧
    ∀ submission : WitnessedSubmission (graph setup),
      submission.emit ((application setup leaks).submit nativeLeft.application who submission)
          who (nativeLeft.network.known who) =
        submission.emit ((application setup leaks).submit nativeRight.application who submission)
          who (nativeRight.network.known who) := by
  have observed := checkpoint_playerObservation_eq setup refs rank covered who left right
    nativeLeft.application.config nativeRight.application.config leftReachable rightReachable
    leftCheckpoint.ordered rightCheckpoint.ordered leftCheckpoint.agrees rightCheckpoint.agrees
    leftCheckpoint.history rightCheckpoint.history sameSource
  have publicEq := EventGraph.publicObserve_eq_of_playerObserve_eq who
    nativeLeft.application.config nativeRight.application.config observed
  have accepted := leftRecorded.accepted_eq_of_order rightRecorded
    (congrArg EventGraph.PublicObservation.completionOrder publicEq)
  have candidates := leftRecorded.candidates_eq_of_observation rightRecorded leftRepresented
    rightRepresented leftValid rightValid who observed
  have publicView : nativeLeft.application.publicView = nativeRight.application.publicView := by
    unfold EventGraphRuntime.State.publicView
    rw [publicEq, accepted, clock, activated, grant]
  have input : nativeLeft.observe (application setup leaks) who =
      nativeRight.observe (application setup leaks) who := by
    change ReactiveApplication.PlayerView.mk
        ⟨nativeLeft.network.leaked who, nativeLeft.network.ledger⟩
        ⟨who, nativeLeft.application.publicView,
          (graph setup).playerObserve who nativeLeft.application.config,
          fun slot => nativeLeft.application.candidates.lookup (who, slot)⟩ nativeLeft.receipts =
      ReactiveApplication.PlayerView.mk
        ⟨nativeRight.network.leaked who, nativeRight.network.ledger⟩
        ⟨who, nativeRight.application.publicView,
          (graph setup).playerObserve who nativeRight.application.config,
          fun slot => nativeRight.application.candidates.lookup (who, slot)⟩ nativeRight.receipts
    rw [leaked, ledger, publicView, observed, candidates, receipts]
  have known := known_eq_of_input_eq (runtime setup) leaks nativeLeft nativeRight who
    leftRecall rightRecall past input
  refine ⟨input, known, fun submission => ?_⟩
  let first := (application setup leaks).submit nativeLeft.application who submission
  let second := (application setup leaks).submit nativeRight.application who submission
  have afterCandidates :
      (fun slot => first.candidates.lookup (who, slot)) =
      (fun slot => second.candidates.lookup (who, slot)) := by
    funext slot
    change (submitStep (submission.call.register nativeLeft.application who) who
      submission.call.packet).candidates.lookup (who, slot) =
      (submitStep (submission.call.register nativeRight.application who) who
        submission.call.packet).candidates.lookup (who, slot)
    rw [submission.call.candidateAfter_eq, submission.call.candidateAfter_eq, candidates]
  rw [WitnessedSubmission.emit_eq_resolve, WitnessedSubmission.emit_eq_resolve,
    afterCandidates, known]

end Vegas.SourceProgram.RevealService
