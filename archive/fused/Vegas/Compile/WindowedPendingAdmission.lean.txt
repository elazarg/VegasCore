/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedOwnerFrame
import Vegas.Compile.WindowedPrivacy
import Interaction.MessageApplicationPending

/-! # Admission stability during pending-message reactions

Delivery changes a recipient's inbox, not application state. Other principals
may then execute arbitrary private commands, submissions, replays, and waits.
These reactions retain the message author's relevant commitment state and the
existing pending envelope. An accepted author-local request therefore remains
accepted, with the same public result, when that envelope is included.

The results retain native histories and do not filter players' observations.
They concern a segment without clock advancement or intervening inclusion;
deadline-respecting service and whole-program strategic comparison are separate
obligations.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Other-player reactions preserve the author's public and relevant private
application state, even if they were chosen after receiving its pending packet. -/
theorem runPolicies_other_agrees (runtime : WindowedApplication P L) (owner : P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (henvironment : Invocation.environment ∉ schedule)
    (howner : Invocation.player owner ∉ schedule)
    (execution next : runtime.application.PolicyExecution)
    (hnext : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    execution.native.application.AgreesFor owner next.native.application := by
  obtain ⟨hpublic, hprepared, _, _⟩ := runtime.runPolicies_other_frame owner players environment
    schedule henvironment howner execution next hnext
  refine ⟨⟨(congrArg Prod.fst hpublic).symm, fun slot => (hprepared slot).symm, ?_⟩, ?_⟩
  · intro field slot _
    exact congrFun (congrArg (fun state => state.2.2) hpublic).symm field
  · exact (congrArg (fun state => state.2.1) hpublic).symm

/-- One reaction per roster member retains the author's relevant state when
the author waits at its reaction coordinate. All other policies are arbitrary;
the waiting condition applies only at the author's current history length. -/
theorem runPolicies_reactions_agrees (runtime : WindowedApplication P L) (owner : P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (roster : List P) (hroster : roster.Nodup)
    (execution next : runtime.application.PolicyExecution)
    (hwait : ∀ history view, history.length = (execution.principalHistory owner).length →
      players owner history view = FinDist.pure .wait)
    (hnext : next ∈
      (runtime.application.runPolicies players environment
        (roster.map .player) execution).support) :
    execution.native.application.AgreesFor owner next.native.application := by
  induction roster generalizing execution with
  | nil =>
      simp only [List.map_nil, MessageApplication.runPolicies,
        FinDist.mem_support_pure] at hnext
      subst next
      exact .refl owner _
  | cons actor rest ih =>
      rw [List.nodup_cons] at hroster
      simp only [List.map_cons, MessageApplication.runPolicies,
        FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      by_cases heq : actor = owner
      · subst actor
        simp only [MessageApplication.invoke, hwait _ _ rfl, FinDist.pure_bind,
          MessageApplication.playerStep, PlayerCommand.toAction,
          MessageApplication.advance, FinDist.mem_support_pure] at hmiddle
        subst middle
        have hremaining := runtime.runPolicies_other_agrees owner players environment
          (rest.map .player)
          (by simp) (by simpa using hroster.1) _ next hnext
        exact hremaining
      · have hfirst := runtime.runPolicies_other_agrees owner players environment [.player actor]
          (by simp) (by simpa using Ne.symm heq) execution middle
          (by simpa [MessageApplication.runPolicies] using hmiddle)
        have hhistory : middle.principalHistory owner = execution.principalHistory owner := by
          simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          exact runtime.application.playerStep_other_history actor owner (Ne.symm heq)
            execution command middle hstep
        exact hfirst.trans (ih hroster.2 middle (by
          intro history view hlength
          exact hwait history view (hlength.trans (congrArg List.length hhistory))) hnext)

/-- Already-admissible requests stay admissible across arbitrary foreign
reactions. Successor private tables need not be equal; the public result and
the retained owner's private projections agree. -/
theorem runPolicies_reactions_handle_accepted (runtime : WindowedApplication P L) (owner : P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (roster : List P) (hroster : roster.Nodup)
    (execution next : runtime.application.PolicyExecution)
    (hwait : ∀ history view, history.length = (execution.principalHistory owner).length →
      players owner history view = FinDist.pure .wait)
    (hnext : next ∈
      (runtime.application.runPolicies players environment
        (roster.map .player) execution).support)
    (message : Message P (ApplicationImage.Payload P L))
    (hauthor : message.payload.OpensCommitment → message.sender = owner)
    (resolved : State P L)
    (haccepted : runtime.handle execution.native.application message = some resolved) :
    ∃ resolvedNext,
      runtime.handle next.native.application message = some resolvedNext ∧
        resolved.AgreesFor owner resolvedNext := by
  have hrelated := (runtime.runPolicies_reactions_agrees owner players environment roster
    hroster execution next hwait hnext).handle runtime message hauthor
  rw [haccepted] at hrelated
  cases hhandle : runtime.handle next.native.application message with
  | none => rw [hhandle] at hrelated; cases hrelated
  | some resolvedNext =>
      refine ⟨resolvedNext, rfl, ?_⟩
      rw [hhandle] at hrelated
      cases hrelated
      assumption

/-- Deliver a pending request, allow one reaction per roster member, and
include that actual envelope. Every supported branch accepts it, retains the
delivered knowledge, and has the original accepted request's public result.
The author waits at its reaction coordinate; all other policies are arbitrary. -/
theorem delivery_reactions_include (runtime : WindowedApplication P L)
    (owner recipient : P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (roster : List P) (hroster : roster.Nodup)
    (execution final : runtime.application.PolicyExecution)
    (hwait : ∀ history view, history.length = (execution.principalHistory owner).length →
      players owner history view = FinDist.pure .wait)
    (id : MessageId P) (message : Message P (ApplicationImage.Payload P L))
    (hlookup : execution.native.pool.lookup id = some message)
    (hauthor : message.payload.OpensCommitment → message.sender = owner)
    (resolved : State P L)
    (haccepted : runtime.handle execution.native.application message = some resolved)
    (hfinal : final ∈
      ((runtime.application.environmentPolicyStep execution (.deliver recipient id)).bind
        fun delivered =>
          (runtime.application.runPolicies players environment
            (roster.map .player) delivered).bind
            fun reacted =>
              runtime.application.environmentPolicyStep reacted (.include id)).support) :
    final.native.application.base.memory = resolved.base.memory ∧
      final.native.application.active = resolved.active ∧
      message ∈ final.native.pool.inbox recipient ∧
      (id, true) ∈ final.native.receipts := by
  simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
  obtain ⟨delivered, hdelivered, reacted, hreacted, hincluded⟩ := hfinal
  simp only [MessageApplication.environmentPolicyStep, EnvironmentPolicyCommand.toAction,
    MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hdelivered
  have hdeliveredLookup : delivered.native.pool.lookup id = some message := by
    rw [hdelivered]
    change (execution.native.pool.deliver recipient id).state.pending.find? _ = some message
    rw [MessagePool.deliver_preserves_pending]
    exact hlookup
  obtain ⟨resolvedNext, hhandle, hagrees⟩ := runtime.runPolicies_reactions_handle_accepted owner
    players environment roster hroster delivered reacted (by
      intro history view hlength
      exact hwait history view (by simpa only [hdelivered] using hlength))
    hreacted message hauthor resolved (by simpa only [hdelivered] using haccepted)
  have hretained := runtime.application.runPolicies_playerOnly_pending_lookup
    players environment (roster.map .player) (by simp) _ reacted id message
    hdeliveredLookup hreacted
  have hinbox := runtime.application.runPolicies_playerOnly_inbox players environment
    (roster.map .player) (by simp) recipient _ reacted hreacted
  have hdeliveredInbox : reacted.native.pool.inbox recipient =
      execution.native.pool.inbox recipient ++
        ([message] : List (Message P runtime.application.Payload)) := by
    rw [hinbox, hdelivered]
    simp only [MessagePool.deliver, hlookup, if_pos]
  simp only [MessageApplication.environmentPolicyStep, EnvironmentPolicyCommand.toAction,
    MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hincluded
  subst final
  rw [MessageApplication.includePending_accept _ _ _ _ _ hretained hhandle]
  refine ⟨hagrees.base.memory.symm, hagrees.active.symm, ?_, ?_⟩
  · change message ∈ (reacted.native.pool.includePending id).state.inbox recipient
    rw [MessagePool.include_preserves_inbox, hdeliveredInbox]
    simp
  · simp

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_reactions_handle_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_reactions_handle_accepted

/-- info: 'Vegas.WindowedApplication.delivery_reactions_include'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.delivery_reactions_include
