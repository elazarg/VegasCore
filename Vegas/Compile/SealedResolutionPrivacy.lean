/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Vegas.Compile.SealedPolicyKnowledge
import Interaction.SealedResolutionCoupling

/-! # Assigned command agreement before a focal binding

The reference-command proof uses the continuing runtime's actual histories and views.
Known-value cache agreement follows from paired histories, so no separate
assumption that a local cache matches the ideal service is needed here.
The source-order publication argument still needs a valid sealed event prefix
and the absence of earlier timeout resolution.
-/

noncomputable section

namespace Vegas.EventGraph.SealedShape

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

theorem resolvingPolicy_knowledge (supported : SealedShape G ty)
    (nullValue : L.Val ty) (window : Nat)
    (known : CommitmentHandle Player Nat → Prop) (who : Player)
    (leftValues rightValues : Fin G.nodeCount → L.Val ty)
    (left right : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (related : SealedResolution.ExecutionRelated
      (supported.resolvingRuntime nullValue window) known left right)
    (hclear : left.native.application.visible.timeouts = [])
    (hvalues : ∀ node, known (who, node.val) → leftValues node = rightValues node)
    (hopenings : ∀ (node : Fin G.nodeCount) handle,
      supported.compile.openingHandle? left.native.application.visible.events who node.val =
        some handle → known handle) :
    ∃ leftCommand rightCommand,
      supported.resolvingProposalPolicy nullValue window who (supported.assignedProposals
        leftValues who)
          (left.principalHistory who)
          (MessageApplication.State.observe _ left.native who) = FinDist.pure leftCommand ∧
      supported.resolvingProposalPolicy nullValue window who (supported.assignedProposals
        rightValues who)
          (right.principalHistory who)
          (MessageApplication.State.observe _ right.native who) = FinDist.pure rightCommand ∧
      SealedProgram.CommandAgreement supported.compile known who leftCommand rightCommand := by
  let runtime := supported.resolvingRuntime nullValue window
  have hrightClear : right.native.application.visible.timeouts = [] := by
    rw [← related.native.publicState]
    exact hclear
  rw [supported.resolvingProposalPolicy_no_timeout nullValue window who _ _ _ hclear,
    supported.resolvingProposalPolicy_no_timeout nullValue window who _ _ _ hrightClear]
  rw [← related.native.observe_eq who]
  apply supported.playerPolicy_knowledge known who leftValues rightValues
    (runtime.eventHistory (left.principalHistory who))
    (runtime.eventHistory (right.principalHistory who)) _ ?_ ?_ hvalues hopenings
  · intro slot
    erw [runtime.eventHistory_cache, runtime.eventHistory_cache]
    exact ((related.histories who).cache slot).1
  · intro slot hknown
    erw [runtime.eventHistory_cache, runtime.eventHistory_cache]
    exact ((related.histories who).cache slot).2 hknown

/-- At a valid pre-timeout prefix before the focal commitment completes, the actual
compiled policies meet the native lockstep theorem's command and opening
premises. The focal slot may already be registered. The assignment may differ
at every source-future hidden value. -/
theorem resolvingPolicy_before_focal (supported : SealedShape G ty)
    (nullValue : L.Val ty) (window : Nat)
    (focal who : Player) (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (leftValues rightValues : Fin G.nodeCount → L.Val ty)
    (left right : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (related : SealedResolution.ExecutionRelated (supported.resolvingRuntime nullValue window)
      (supported.knownBefore focal decision) left right)
    (hclear : left.native.application.visible.timeouts = [])
    (hnotDone : SealedProgram.done left.native.application.visible.events decision.val = false)
    (hvalues : ∀ node, supported.knownBefore focal decision (who, node.val) →
      leftValues node = rightValues node) :
    ∃ leftCommand rightCommand,
      supported.resolvingProposalPolicy nullValue window who (supported.assignedProposals
        leftValues who)
          (left.principalHistory who)
          (MessageApplication.State.observe _ left.native who) = FinDist.pure leftCommand ∧
      supported.resolvingProposalPolicy nullValue window who (supported.assignedProposals
        rightValues who)
          (right.principalHistory who)
          (MessageApplication.State.observe _ right.native who) = FinDist.pure rightCommand ∧
      SealedProgram.CommandAgreement supported.compile (supported.knownBefore focal decision)
        who leftCommand rightCommand ∧
      (∀ payload, leftCommand = .submit payload →
        SealedProgram.OpeningKnown (supported.knownBefore focal decision)
          ⟨(who, left.native.pool.nextSerial who), payload⟩) := by
  have hopenings : ∀ (node : Fin G.nodeCount) handle,
      supported.compile.openingHandle? left.native.application.visible.events who node.val =
        some handle → supported.knownBefore focal decision handle := by
    intro node handle hhandle
    exact supported.openingHandle?_knownBefore focal decision guard hdecision _
      hnotDone who node.val handle hhandle
  obtain ⟨lc, rc, hl, hr, hc⟩ := supported.resolvingPolicy_knowledge nullValue window
    (supported.knownBefore focal decision) who leftValues rightValues left right related
    hclear hvalues hopenings
  refine ⟨lc, rc, hl, hr, hc, ?_⟩
  intro payload hp
  have hsubmit : .submit payload ∈
      (supported.resolvingProposalPolicy nullValue window who (supported.assignedProposals
        leftValues who)
        (left.principalHistory who)
        (MessageApplication.State.observe _ left.native who)).support := by
    rw [hl, hp, FinDist.mem_support_pure]
  rcases supported.resolvingProposalPolicy_submission nullValue window who _ _ _ payload hsubmit
    with
    ⟨node, rfl, _⟩ | ⟨node, handle, value, rfl, hhandle⟩
  · trivial
  · simp only [MessageApplication.State.observe, SealedResolution.messageApplication,
      hclear, SealedProgram.discharge_nil] at hhandle
    intro _
    exact supported.openingHandle?_knownBefore focal decision guard hdecision _
      hnotDone who node handle hhandle

end Vegas.EventGraph.SealedShape

/-- info: 'Vegas.EventGraph.SealedShape.resolvingPolicy_before_focal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedShape.resolvingPolicy_before_focal
