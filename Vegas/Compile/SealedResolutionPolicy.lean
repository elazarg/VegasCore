/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPolicy
import Interaction.SealedResolutionPolicy

/-! # Source policies on the continuing deadline runtime

The same node selector and sample-once commitment code consume public timeout
completion. Source reads combine public events, own registration memory, and
the null value for an unregistered timed-out own commitment. Registered values
remain private memory even when the corresponding publication defaults.

Source policies are translated to native policies; unilateral replacements
remain unrestricted. The before-timeout law is local policy equality;
whole-program strategic preservation additionally
needs service, termination, and the source/native probability coupling.
-/

noncomputable section

namespace Vegas.EventGraph.SealedShape

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

def resolvingRuntime (supported : SealedShape G ty) (nullValue : L.Val ty)
    (window : Nat) : SealedResolution Player (L.Val ty) :=
  ⟨supported.compile, nullValue, window⟩

/-- Complete one owned timed-out commitment field in a local store. -/
def resolvedPlayerStoreStep (supported : SealedShape G ty) (who : Player)
    (nullValue : L.Val ty)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (store : Store L) (node : Nat) : Store L :=
  match G.node? node with
  | some (.commit owner _) =>
      if owner = who then
        let memory := (supported.compile.registrationEncoding node).cachedValue
          (supported.compile.messageApplication (Value := L.Val ty)) history
        store.set (G.nodeTarget node) ⟨ty, memory.getD nullValue⟩
      else store
  | _ => store

/-- Complete only the owner's timed-out commitment fields in the local store.
No private registration is fabricated and no existing private value is erased. -/
def resolvedPlayerStore (supported : SealedShape G ty) (who : Player)
    (nullValue : L.Val ty) (completed : List Nat)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View) : Store L :=
  completed.foldl (supported.resolvedPlayerStoreStep who nullValue history)
    (supported.playerStore who history view)

def resolvingProposalPolicy (supported : SealedShape G ty) (nullValue : L.Val ty)
    (window : Nat) (who : Player) (policy : ProposalPolicy G who) :
    (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy :=
  fun history view =>
    let runtime := supported.resolvingRuntime nullValue window
    let history := runtime.eventHistory history
    let eventView := runtime.eventView view
    let store := supported.resolvedPlayerStore who nullValue view.application.timeouts
      history eventView
    (G.nodeOrder.findSome? (supported.nodeCommand? who view.application.timeouts
      policy history eventView store)).getD (FinDist.pure .wait)

/-- Translate a legal graph policy through the same native proposal generator. -/
def resolvingPolicy (supported : SealedShape G ty) (nullValue : L.Val ty)
    (window : Nat) (who : Player) (policy : CommitPolicy G who) :
    (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy :=
  supported.resolvingProposalPolicy nullValue window who policy.proposals

/-- With no recorded timeout, the proposal policy is exactly its untimed
implementation on the event/history projection. Clock and readiness timestamps
do not change which local kernel is used. -/
theorem resolvingProposalPolicy_no_timeout (supported : SealedShape G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player) (policy : ProposalPolicy G who)
    (history : List
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (view : (supported.resolvingRuntime nullValue window).messageApplication.View)
    (htimeouts : view.application.timeouts = []) :
    supported.resolvingProposalPolicy nullValue window who policy history view =
      supported.proposalPlayerPolicy who policy
        ((supported.resolvingRuntime nullValue window).eventHistory history)
        ((supported.resolvingRuntime nullValue window).eventView view) := by
  simp only [resolvingProposalPolicy, htimeouts, resolvedPlayerStore, List.foldl_nil,
    proposalPlayerPolicy]

theorem resolvingPolicy_no_timeout (supported : SealedShape G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player) (policy : CommitPolicy G who)
    (history : List
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (view : (supported.resolvingRuntime nullValue window).messageApplication.View)
    (htimeouts : view.application.timeouts = []) :
    supported.resolvingPolicy nullValue window who policy history view =
      supported.playerPolicy who policy
        ((supported.resolvingRuntime nullValue window).eventHistory history)
        ((supported.resolvingRuntime nullValue window).eventView view) :=
  supported.resolvingProposalPolicy_no_timeout nullValue window who policy.proposals
    history view htimeouts

theorem resolvingProposalPolicy_submission (supported : SealedShape G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player) (policy : ProposalPolicy G who)
    (history : List
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (view : (supported.resolvingRuntime nullValue window).messageApplication.View)
    (payload : SealedProgram.Payload Player (L.Val ty))
    (hsubmit : .submit payload ∈
      (supported.resolvingProposalPolicy nullValue window who policy history view).support) :
    (∃ node, payload = .commitment node (who, node) ∧
      ((supported.compile.registrationEncoding node).cachedValue
        (supported.resolvingRuntime nullValue window).messageApplication history).isSome = true) ∨
      ∃ node handle value, payload = .opening node handle value ∧
        (supported.compile.discharge view.application.timeouts).openingHandle?
          view.application.events who node = some handle := by
  unfold resolvingProposalPolicy at hsubmit
  dsimp only at hsubmit
  unfold Option.getD at hsubmit
  split at hsubmit
  · rename_i law hselected
    obtain ⟨node, _, hnode⟩ := List.exists_of_findSome?_eq_some hselected
    rcases supported.nodeCommand?_submission who view.application.timeouts policy _ _ _
      node law hnode payload hsubmit with ⟨hcommit, hcache⟩ | ⟨handle, value, hopen, hready⟩
    · refine Or.inl ⟨node.val, hcommit, ?_⟩
      exact (congrArg Option.isSome
        ((supported.resolvingRuntime nullValue window).eventHistory_cache
          (supported.compile.registrationEncoding node.val) history)).symm.trans hcache
    · exact Or.inr ⟨node.val, handle, value, hopen, hready⟩
  · simp only [FinDist.mem_support_pure] at hsubmit
    cases hsubmit

theorem resolvingPolicy_submission (supported : SealedShape G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player) (policy : CommitPolicy G who)
    (history : List
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (view : (supported.resolvingRuntime nullValue window).messageApplication.View)
    (payload : SealedProgram.Payload Player (L.Val ty))
    (hsubmit : .submit payload ∈
      (supported.resolvingPolicy nullValue window who policy history view).support) :
    (∃ node, payload = .commitment node (who, node) ∧
      ((supported.compile.registrationEncoding node).cachedValue
        (supported.resolvingRuntime nullValue window).messageApplication history).isSome = true) ∨
      ∃ node handle value, payload = .opening node handle value ∧
        (supported.compile.discharge view.application.timeouts).openingHandle?
          view.application.events who node = some handle :=
  supported.resolvingProposalPolicy_submission nullValue window who policy.proposals
    history view payload hsubmit

theorem resolvingPolicy_no_cleartext (supported : SealedShape G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player) (policy : CommitPolicy G who)
    (history : List
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (view : (supported.resolvingRuntime nullValue window).messageApplication.View)
    (node : Nat) (value : L.Val ty) :
    .submit (.cleartext node value) ∉
      (supported.resolvingPolicy nullValue window who policy history view).support := by
  intro hsubmit
  rcases supported.resolvingProposalPolicy_submission nullValue window who policy.proposals
    history view _
    hsubmit with ⟨_, h, _⟩ | ⟨_, _, _, h, _⟩ <;> cases h

end Vegas.EventGraph.SealedShape

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

def compileResolvingPolicy (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (policy : SourceBehavioralPolicy source.core.prog who) :
    (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy :=
  compilation.supported.resolvingPolicy nullValue window who
    (compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl who policy)

end Vegas.SealedCompilation

/-- info: 'Vegas.EventGraph.SealedShape.resolvingProposalPolicy_no_timeout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedShape.resolvingProposalPolicy_no_timeout

/-- info: 'Vegas.EventGraph.SealedShape.resolvingPolicy_no_cleartext' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedShape.resolvingPolicy_no_cleartext
