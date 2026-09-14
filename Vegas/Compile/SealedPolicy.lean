/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedView
import Vegas.Compile.SealedCompiler
import Vegas.Compile.SourcePolicy
import Interaction.SealedController

/-! # Source policies implemented by sealed-message commands

The translation selects the first owned ready node in source order. Each
commitment samples its declared-read kernel once into a private write-once
slot, then publishes only its opaque handle. An opening uses the same cached
value and the public prerequisite check. The policy receives no ideal-service
table and ignores unrelated wire observations when choosing source values.

This is a strategy translation for analysis of the open protocol. Players
are not required to execute it; the native policy interface still admits
arbitrary unilateral replacements. Its local kernel law below does not claim
the whole-program pending-message deviation law.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Actual player input reconstruction; all private data comes from this
principal's own registration history. -/
def playerStore (supported : SealedFragment G ty) (who : Player)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View) : Store L :=
  G.sealedPlayerStore ty who (fun slot =>
    (supported.compile.registrationEncoding slot).cachedValue
      (supported.compile.messageApplication (Value := L.Val ty)) history) view.application

/-- An empty slot draws once from the supplied local read store; an occupied
slot only publishes its handle. Runtime-specific store reconstruction is kept
separate from this shared command generation. -/
def commitCommand (supported : SealedFragment G ty) (who : Player)
    (policy : CommitPolicy G who) (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (store : Store L) :
    FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand :=
  match (supported.compile.registrationEncoding node.val).cachedValue
      (supported.compile.messageApplication (Value := L.Val ty)) history with
  | some _ => FinDist.pure (.submit (.commitment node.val (who, node.val)))
  | none =>
      match ReadEnv.ofStoreExec? store guard.choiceReads with
      | none => FinDist.pure .wait
      | some reads => (policy node guard hsem reads).map fun choice =>
          .privateCommand ⟨(node.val,
            cast (congrArg L.Val (supported.commitType node who guard hsem)) choice.1)⟩

/-- The optional command of one owned ready node. Publicly resolved nodes are
skipped and discharged from prerequisites. Prerequisites are checked before
publication, including before a value-bearing opening enters the pool. -/
def nodeCommand? (supported : SealedFragment G ty) (who : Player) (completed : List Nat)
    (policy : CommitPolicy G who)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (store : Store L)
    (node : Fin G.nodeCount) :
    Option (FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand) :=
  if completed.contains node.val then none
  else if SealedProgram.done view.application node.val = false ∧
      SealedProgram.prerequisitesDone view.application
        ((G.sealedRule node).discharge completed) = true then
    match hsem : (G.nodeRow node).sem with
    | .commit owner guard =>
        if howner : owner = who then
          some (supported.commitCommand who policy node guard (howner ▸ hsem) history store)
        else none
    | .reveal _ =>
        ((supported.compile.discharge completed).openingHandle?
          view.application who node.val).map fun handle =>
          match (supported.compile.registrationEncoding handle.2).cachedValue
              (supported.compile.messageApplication (Value := L.Val ty)) history with
          | none => FinDist.pure .wait
          | some value => FinDist.pure (.submit (.opening node.val handle value))
    | .sample _ => none
  else none

/-- Playerwise implementation of graph kernels on the actual message runtime. -/
def playerPolicy (supported : SealedFragment G ty) (who : Player)
    (policy : CommitPolicy G who) :
    (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy :=
  fun history view =>
    ((G.nodeOrder.findSome? (supported.nodeCommand? who [] policy history view
      (supported.playerStore who history view))).getD
      (FinDist.pure .wait))

/-- Whether a node is selected is determined by the public readiness and
ownership checks. Private history and the choice kernel cannot change it. -/
theorem nodeCommand?_none_iff (supported : SealedFragment G ty) (who : Player)
    (completed : List Nat)
    (left right : CommitPolicy G who)
    (leftHistory rightHistory :
      List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (leftStore rightStore : Store L)
    (node : Fin G.nodeCount) :
    supported.nodeCommand? who completed left leftHistory view leftStore node = none ↔
      supported.nodeCommand? who completed right rightHistory view rightStore node = none := by
  unfold nodeCommand?
  split
  · rfl
  split
  · split
    · split <;> simp
    · simp
    · rfl
  · rfl

private theorem nodeCommand?_registration_kernel (supported : SealedFragment G ty)
    (who : Player) (completed : List Nat) (original : CommitPolicy G who)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (store : Store L) (node : Fin G.nodeCount)
    (law : FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (slot : Nat) (value : L.Val ty)
    (hselected : supported.nodeCommand? who completed original history view store node = some law)
    (hcommand : .privateCommand ⟨(slot, value)⟩ ∈ law.support) :
    ∃ (guard : EventGuard L) (hsem : (G.nodeRow node).sem = .commit who guard)
      (reads : ReadEnv L guard.choiceReads),
      slot = node.val ∧
      (supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history = none ∧
      ReadEnv.ofStoreExec? store guard.choiceReads = some reads ∧
      ∀ policy : CommitPolicy G who,
        supported.nodeCommand? who completed policy history view store node =
          some ((policy node guard hsem reads).map (fun choice =>
            .privateCommand ⟨(node.val,
              cast (congrArg L.Val (supported.commitType node who guard hsem)) choice.1)⟩)) := by
  unfold nodeCommand? at hselected
  split at hselected
  · contradiction
  rename_i hcompleted
  split at hselected
  · rename_i hready
    split at hselected
    · rename_i owner guard hsem
      split at hselected
      · rename_i howner
        subst owner
        rw [← Option.some.inj hselected] at hcommand
        unfold commitCommand at hcommand
        split at hcommand
        · simp only [FinDist.mem_support_pure] at hcommand
          cases hcommand
        · rename_i hcache
          split at hcommand
          · simp only [FinDist.mem_support_pure] at hcommand
            cases hcommand
          · rename_i reads hreads
            rw [FinDist.support_map] at hcommand
            obtain ⟨choice, _, heq⟩ := hcommand
            have hslot : slot = node.val :=
              (congrArg (fun command => match command with
                | .privateCommand request => request.down.1
                | _ => slot) heq).symm
            refine ⟨guard, hsem, reads, hslot, hcache, hreads, ?_⟩
            intro policy
            simp only [nodeCommand?, if_neg hcompleted, if_pos hready]
            split
            · rename_i other otherGuard hother
              obtain ⟨rfl, rfl⟩ := NodeSem.commit.inj (hsem.symm.trans hother)
              simp only [↓reduceDIte, commitCommand, hcache, hreads]
            · rename_i source hother
              cases hsem.symm.trans hother
            · rename_i dist hother
              cases hsem.symm.trans hother
      · contradiction
    · cases hhandle : (supported.compile.discharge completed).openingHandle?
          view.application who node.val with
      | none => simp only [hhandle, Option.map_none] at hselected; contradiction
      | some handle =>
          simp only [hhandle, Option.map_some] at hselected
          split at hselected <;>
            rw [← Option.some.inj hselected, FinDist.mem_support_pure] at hcommand <;>
            cases hcommand
    · contradiction
  · contradiction

/-- An actual private registration identifies the selected commitment, fresh
cache, and successful declared reads. Replacing its source policy changes only
the draw kernel, not the selected site or its input. -/
theorem selected_registration_kernel (supported : SealedFragment G ty)
    (who : Player) (completed : List Nat) (original : CommitPolicy G who)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (store : Store L) (slot : Nat) (value : L.Val ty)
    (hcommand : .privateCommand ⟨(slot, value)⟩ ∈
      ((G.nodeOrder.findSome? (supported.nodeCommand? who completed original
        history view store)).getD (FinDist.pure .wait)).support) :
    ∃ (node : Fin G.nodeCount) (guard : EventGuard L)
      (hsem : (G.nodeRow node).sem = .commit who guard) (reads : ReadEnv L guard.choiceReads),
      slot = node.val ∧
      (supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history = none ∧
      ReadEnv.ofStoreExec? store guard.choiceReads = some reads ∧
      ∀ policy : CommitPolicy G who,
        (G.nodeOrder.findSome? (supported.nodeCommand? who completed policy
          history view store)).getD (FinDist.pure .wait) =
          (policy node guard hsem reads).map (fun choice =>
            .privateCommand ⟨(node.val,
              cast (congrArg L.Val (supported.commitType node who guard hsem)) choice.1)⟩) := by
  cases hselected : G.nodeOrder.findSome?
      (supported.nodeCommand? who completed original history view store) with
  | none =>
      simp only [hselected, Option.getD_none, FinDist.mem_support_pure] at hcommand
      cases hcommand
  | some law =>
      simp only [hselected, Option.getD_some] at hcommand
      obtain ⟨front, node, rest, hnodes, hnode, hfront⟩ :=
        List.findSome?_eq_some_iff.mp hselected
      obtain ⟨guard, hsem, reads, hslot, hcache, hreads, hkernel⟩ :=
        supported.nodeCommand?_registration_kernel who completed original history view store
          node law slot value hnode hcommand
      refine ⟨node, guard, hsem, reads, hslot, hcache, hreads, ?_⟩
      intro policy
      have hright := List.findSome?_eq_some_iff.mpr
        ⟨front, node, rest, hnodes, hkernel policy, fun prior hprior =>
          (supported.nodeCommand?_none_iff who completed original policy
            history history view store store prior).mp (hfront prior hprior)⟩
      rw [hright, Option.getD_some]

private theorem commitCommand_nonregistration_law (supported : SealedFragment G ty)
    (who : Player) (original replacement : CommitPolicy G who)
    (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (store : Store L)
    (command : (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hcommand : command ∈
      (supported.commitCommand who original node guard hsem history store).support)
    (hnonregistration : ∀ request, command ≠ .privateCommand request) :
    supported.commitCommand who replacement node guard hsem history store =
      FinDist.pure command := by
  unfold commitCommand at hcommand ⊢
  split at hcommand
  · exact congrArg FinDist.pure (FinDist.mem_support_pure.mp hcommand).symm
  · split at hcommand
    · exact congrArg FinDist.pure (FinDist.mem_support_pure.mp hcommand).symm
    · rw [FinDist.support_map] at hcommand
      obtain ⟨choice, _, heq⟩ := hcommand
      exact False.elim (hnonregistration _ heq.symm)

private theorem nodeCommand?_nonregistration_law (supported : SealedFragment G ty)
    (who : Player) (completed : List Nat) (original replacement : CommitPolicy G who)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (store : Store L) (node : Fin G.nodeCount)
    (law : FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (command : (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hselected : supported.nodeCommand? who completed original history view store node = some law)
    (hcommand : command ∈ law.support)
    (hnonregistration : ∀ request, command ≠ .privateCommand request) :
    supported.nodeCommand? who completed replacement history view store node =
      some (FinDist.pure command) := by
  unfold nodeCommand? at hselected ⊢
  split at hselected
  · cases hselected
  rename_i hcompleted
  rw [if_neg hcompleted]
  split at hselected
  · rename_i hready
    rw [if_pos hready]
    split at hselected
    · rename_i owner guard hsem
      split at hselected
      · rename_i howner
        rw [dif_pos howner]
        rw [← Option.some.inj hselected] at hcommand
        rw [supported.commitCommand_nonregistration_law who original replacement node guard
          (howner ▸ hsem) history store command hcommand hnonregistration]
      · contradiction
    · cases hhandle : (supported.compile.discharge completed).openingHandle?
          view.application who node.val with
      | none => simp only [hhandle, Option.map_none] at hselected; contradiction
      | some handle =>
          simp only [hhandle, Option.map_some] at hselected ⊢
          split at hselected <;>
            rw [← Option.some.inj hselected, FinDist.mem_support_pure] at hcommand <;>
            cases hcommand <;> rfl
    · contradiction
  · contradiction

/-- Outside a fresh registration, the actual selected command is deterministic
and independent of the source decision kernel. This includes cached commitment
submissions, openings, and waits, both before and after timeout. -/
theorem selected_nonregistration_law (supported : SealedFragment G ty)
    (who : Player) (completed : List Nat) (original replacement : CommitPolicy G who)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (store : Store L)
    (command : (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hcommand : command ∈ ((G.nodeOrder.findSome?
      (supported.nodeCommand? who completed original history view store)).getD
        (FinDist.pure .wait)).support)
    (hnonregistration : ∀ request, command ≠ .privateCommand request) :
    (G.nodeOrder.findSome?
      (supported.nodeCommand? who completed replacement history view store)).getD
        (FinDist.pure .wait) = FinDist.pure command := by
  cases hselected : G.nodeOrder.findSome?
      (supported.nodeCommand? who completed original history view store) with
  | none =>
      simp only [hselected, Option.getD_none, FinDist.mem_support_pure] at hcommand
      have hnone : G.nodeOrder.findSome?
          (supported.nodeCommand? who completed replacement history view store) = none := by
        apply List.findSome?_eq_none_iff.mpr
        intro node hnode
        exact (supported.nodeCommand?_none_iff who completed original replacement history history
          view store store node).mp (List.findSome?_eq_none_iff.mp hselected node hnode)
      simp only [hnone, Option.getD_none, hcommand]
  | some law =>
      simp only [hselected, Option.getD_some] at hcommand
      obtain ⟨front, node, rest, hnodes, hnode, hfront⟩ :=
        List.findSome?_eq_some_iff.mp hselected
      have hright := List.findSome?_eq_some_iff.mpr
        ⟨front, node, rest, hnodes,
          supported.nodeCommand?_nonregistration_law who completed original replacement history
            view store node law command hnode hcommand hnonregistration,
          fun prior hprior =>
            (supported.nodeCommand?_none_iff who completed original replacement history history
              view store store prior).mp (hfront prior hprior)⟩
      rw [hright, Option.getD_some]

theorem commitCommand_cached (supported : SealedFragment G ty) (who : Player)
    (policy : CommitPolicy G who) (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (store : Store L) (value : L.Val ty)
    (hcache : (supported.compile.registrationEncoding node.val).cachedValue
      (supported.compile.messageApplication (Value := L.Val ty)) history = some value) :
    supported.commitCommand who policy node guard hsem history store =
      FinDist.pure (.submit (.commitment node.val (who, node.val))) := by
  simp only [commitCommand, hcache]

/-- At an empty slot, native local reads give exactly the declared source
kernel, mapped into a private registration rather than a cleartext packet. -/
theorem commitCommand_fresh (supported : SealedFragment G ty) (who : Player)
    (policy : CommitPolicy G who) (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (execution : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hmemory : SealedProgram.RegistrationMemory supported.compile execution)
    (hbinding : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts execution.native))
    (cfg : Config G)
    (hdecode : G.decodeSealed ty (supported.compile.eraseReceipts execution.native) = some cfg)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.store guard.choiceReads = some reads)
    (hcache : (supported.compile.registrationEncoding node.val).cachedValue
      (supported.compile.messageApplication (Value := L.Val ty))
      (execution.principalHistory who) = none) :
    supported.commitCommand who policy node guard hsem (execution.principalHistory who)
      (supported.playerStore who (execution.principalHistory who)
        (MessageApplication.State.observe _ execution.native who)) =
      (policy node guard hsem reads).map (fun choice =>
        (.privateCommand ⟨(node.val,
          cast (congrArg L.Val (supported.commitType node who guard hsem)) choice.1)⟩ :
          (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)) := by
  have hlocal : ReadEnv.ofStoreExec?
      (supported.playerStore who (execution.principalHistory who)
        (MessageApplication.State.observe _ execution.native who)) guard.choiceReads =
      some reads :=
    ReadEnv.ofStoreExec?_eq_some_of_ofStore?_eq_some
      (supported.sealedPlayerStore_reads who execution hmemory hbinding cfg hdecode
        node guard hsem reads hreads)
  simp only [commitCommand, hcache, hlocal]

theorem commitCommand_submission (supported : SealedFragment G ty) (who : Player)
    (policy : CommitPolicy G who) (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (store : Store L)
    (payload : SealedProgram.Payload Player (L.Val ty))
    (hsubmit : .submit payload ∈
      (supported.commitCommand who policy node guard hsem history store).support) :
    payload = .commitment node.val (who, node.val) ∧
      ((supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history).isSome = true := by
  unfold commitCommand at hsubmit
  split at hsubmit
  · rename_i value hcache
    exact ⟨by simpa only [FinDist.mem_support_pure,
      MessageInterface.PlayerCommand.submit.injEq] using hsubmit,
      by simp only [hcache, Option.isSome_some]⟩
  · split at hsubmit
    · simp only [FinDist.mem_support_pure] at hsubmit
      cases hsubmit
    · rw [FinDist.support_map] at hsubmit
      obtain ⟨choice, _, hchoice⟩ := hsubmit
      cases hchoice

theorem nodeCommand?_submission (supported : SealedFragment G ty) (who : Player)
    (completed : List Nat)
    (policy : CommitPolicy G who)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (store : Store L)
    (node : Fin G.nodeCount)
    (law : FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hselected : supported.nodeCommand? who completed policy history view store node = some law)
    (payload : SealedProgram.Payload Player (L.Val ty))
    (hsubmit : .submit payload ∈ law.support) :
    (payload = .commitment node.val (who, node.val) ∧
      ((supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history).isSome = true) ∨
      ∃ handle value, payload = .opening node.val handle value ∧
        (supported.compile.discharge completed).openingHandle?
          view.application who node.val = some handle := by
  unfold nodeCommand? at hselected
  split at hselected
  · contradiction
  split at hselected
  · split at hselected
    · rename_i owner guard hsem
      split at hselected
      · rename_i howner
        have hlaw := Option.some.inj hselected
        rw [← hlaw] at hsubmit
        exact Or.inl (supported.commitCommand_submission who policy node guard
          (howner ▸ hsem) history store payload hsubmit)
      · contradiction
    · cases hhandle : (supported.compile.discharge completed).openingHandle?
          view.application who node.val with
      | none => simp only [hhandle, Option.map_none] at hselected; contradiction
      | some handle =>
          simp only [hhandle, Option.map_some] at hselected
          split at hselected
          · rw [← Option.some.inj hselected, FinDist.mem_support_pure] at hsubmit
            cases hsubmit
          · rename_i value hcache
            rw [← Option.some.inj hselected, FinDist.mem_support_pure] at hsubmit
            exact Or.inr ⟨handle, value, MessageInterface.PlayerCommand.submit.inj hsubmit,
              rfl⟩
    · contradiction
  · contradiction

/-- Every emitted packet is an opaque commitment or an opening whose public
publication barrier is already satisfied. This holds even on arbitrary inputs. -/
theorem playerPolicy_submission (supported : SealedFragment G ty) (who : Player)
    (policy : CommitPolicy G who)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (payload : SealedProgram.Payload Player (L.Val ty))
    (hsubmit : .submit payload ∈ (supported.playerPolicy who policy history view).support) :
    (∃ node, payload = .commitment node (who, node)) ∨
      ∃ node handle value, payload = .opening node handle value ∧
        supported.compile.openingHandle? view.application who node = some handle := by
  unfold playerPolicy at hsubmit
  cases hselected : G.nodeOrder.findSome? (supported.nodeCommand? who [] policy history view
      (supported.playerStore who history view)) with
  | none =>
      simp only [hselected, Option.getD_none, FinDist.mem_support_pure] at hsubmit
      cases hsubmit
  | some law =>
      simp only [hselected, Option.getD_some] at hsubmit
      obtain ⟨node, _, hnode⟩ := List.exists_of_findSome?_eq_some hselected
      rcases supported.nodeCommand?_submission who [] policy history view
        (supported.playerStore who history view) node law hnode
        payload hsubmit with ⟨hcommit, _⟩ | ⟨handle, value, hopen, hready⟩
      · exact Or.inl ⟨node.val, hcommit⟩
      · exact Or.inr ⟨node.val, handle, value, hopen, by simpa using hready⟩

theorem playerPolicy_no_cleartext (supported : SealedFragment G ty) (who : Player)
    (policy : CommitPolicy G who)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (node : Nat) (value : L.Val ty) :
    .submit (.cleartext node value) ∉ (supported.playerPolicy who policy history view).support := by
  intro hsubmit
  rcases supported.playerPolicy_submission who policy history view _ hsubmit with
    ⟨_, h⟩ | ⟨_, _, _, h, _⟩ <;> cases h

theorem playerPolicy_opening_ready (supported : SealedFragment G ty) (who : Player)
    (policy : CommitPolicy G who)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (node : Nat) (handle : CommitmentHandle Player Nat) (value : L.Val ty)
    (hsubmit : .submit (.opening node handle value) ∈
      (supported.playerPolicy who policy history view).support) :
    supported.compile.openingReady view.application who node = true := by
  rcases supported.playerPolicy_submission who policy history view _ hsubmit with
    ⟨_, h⟩ | ⟨other, actualHandle, actualValue, h, hready⟩
  · cases h
  · cases h
    simp only [SealedProgram.openingReady, hready, Option.isSome_some]

end Vegas.EventGraph.SealedFragment

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Compile one written-source policy to the native principal-scoped policy
interface, through the same graph compilation as the operational theorem. -/
def compilePolicy (compilation : SealedCompilation source ty) (who : Player)
    (policy : SourceBehavioralPolicy source.core.prog who) :
    (compilation.program.messageApplication (Value := L.Val ty)).PlayerPolicy :=
  compilation.supported.playerPolicy who
    (compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl who policy)

end Vegas.SealedCompilation

/-- info: 'Vegas.EventGraph.SealedFragment.commitCommand_fresh' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.commitCommand_fresh
