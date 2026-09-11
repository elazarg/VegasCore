/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryService
import Vegas.Compile.WindowedPendingAdmission
import Vegas.Compile.WindowedDeliveryPhase

/-! # Delivery-service admission stability

The delivery-enabled service may expose a pending envelope before its normal
inclusion coordinate. Arbitrary reactions can add or replay traffic, but an
unchanged current owner waits at its reaction coordinate. Consequently the
owner's allocation counter and the already-selected pending envelope remain
stable, so normal service selects the same identifier after reactions.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem lift_latestSubmissionCommand (runtime : WindowedApplication P L)
    (owner : P) (view : runtime.application.EnvironmentObservation) :
    runtime.liftEnvironmentCommand
      (runtime.image.application.latestSubmissionCommand owner
        (runtime.eraseEnvironmentView view)) =
      runtime.application.latestSubmissionCommand owner view := by
  unfold MessageApplication.latestSubmissionCommand
  dsimp only [eraseEnvironmentView]
  cases hs : view.pool.nextSerial owner with
  | zero => rfl
  | succ serial =>
      by_cases hfound : (view.pool.lookup (owner, serial)).isSome = true <;>
        simp [hfound, liftEnvironmentCommand]

private theorem serviceCommand_include_of_latest (runtime : WindowedApplication P L)
    (instruction : ApplicationInstruction P L) (owner : P)
    (howner : instruction.submitter = some owner)
    (view : runtime.application.EnvironmentObservation) (id : MessageId P)
    (hselected : runtime.application.latestSubmissionCommand owner view = .include id) :
    runtime.liftEnvironmentCommand
      (runtime.image.serviceCommand instruction (runtime.eraseEnvironmentView view)) =
      .include id := by
  cases instruction with
  | sample code => simp [ApplicationInstruction.submitter] at howner
  | bind code | publicChoice code | conditional code =>
      simp only [ApplicationInstruction.submitter, Option.some.injEq] at howner
      subst owner
      exact (runtime.lift_latestSubmissionCommand _ view).trans hselected

/-- One reaction per roster member preserves the waiting owner's allocation
counter and every envelope that was pending before the reactions. Other
players' policies are unrestricted. -/
theorem runPolicies_reactions_counter_lookup (runtime : WindowedApplication P L)
    (owner : P) (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (roster : List P) (hroster : roster.Nodup)
    (execution next : runtime.application.PolicyExecution)
    (hwait : ∀ history view,
      history.length = (execution.principalHistory owner).length →
        players owner history view = FinDist.pure .wait)
    (hnext : next ∈ (runtime.application.runPolicies players environment
      (roster.map .player) execution).support) :
    next.native.pool.nextSerial owner = execution.native.pool.nextSerial owner ∧
      ∀ id message, execution.native.pool.lookup id = some message →
        next.native.pool.lookup id = some message := by
  induction roster generalizing execution with
  | nil =>
      simp only [List.map_nil, MessageApplication.runPolicies,
        FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨rfl, fun _ _ hlookup => hlookup⟩
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
        have hremaining := runtime.runPolicies_other_frame owner players environment
          (rest.map .player) (by simp) (by simpa using hroster.1) _ next hnext
        exact ⟨hremaining.2.2.1, hremaining.2.2.2⟩
      · have hframe := runtime.runPolicies_other_frame owner players environment
          [.player actor] (by simp) (by simpa using Ne.symm heq) execution middle
          (by simpa [MessageApplication.runPolicies] using hmiddle)
        have hhistory : middle.principalHistory owner = execution.principalHistory owner := by
          simp only [MessageApplication.invoke, FinDist.support_bind,
            Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          exact runtime.application.playerStep_other_history actor owner (Ne.symm heq)
            execution command middle hstep
        obtain ⟨hserial, hlookup⟩ := ih hroster.2 middle (by
          intro history view hlength
          exact hwait history view
            (hlength.trans (congrArg List.length hhistory))) hnext
        exact ⟨hserial.trans hframe.2.2.1, fun id message hold =>
          hlookup id message (hframe.2.2.2 id message hold)⟩

/-- A successful latest-submission selection is stable across the reaction
segment. The identifier is derived from the original counter and pending
lookup rather than assumed for the successor. -/
theorem runPolicies_reactions_latestSubmissionCommand
    (runtime : WindowedApplication P L) (owner : P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (roster : List P) (hroster : roster.Nodup)
    (execution next : runtime.application.PolicyExecution)
    (hwait : ∀ history view,
      history.length = (execution.principalHistory owner).length →
        players owner history view = FinDist.pure .wait)
    (hnext : next ∈ (runtime.application.runPolicies players environment
      (roster.map .player) execution).support)
    (id : MessageId P)
    (hselected : runtime.application.latestSubmissionCommand owner
      (State.environmentView runtime.application execution.native) = .include id) :
    runtime.application.latestSubmissionCommand owner
      (State.environmentView runtime.application next.native) = .include id := by
  obtain ⟨hserial, hlookup⟩ := runtime.runPolicies_reactions_counter_lookup owner players
    environment roster hroster execution next hwait hnext
  cases hs : execution.native.pool.nextSerial owner with
  | zero =>
      simp [MessageApplication.latestSubmissionCommand, State.environmentView, hs]
        at hselected
  | succ serial =>
      cases hm : execution.native.pool.lookup (owner, serial) with
      | none =>
          simp [MessageApplication.latestSubmissionCommand, State.environmentView, hs, hm]
            at hselected
      | some message =>
          have hnextLookup := hlookup (owner, serial) message hm
          simp only [MessageApplication.latestSubmissionCommand, State.environmentView,
            hs, hm, Option.isSome_some, if_true,
            MessageInterface.EnvironmentPolicyCommand.include.injEq] at hselected
          rw [← hselected]
          simp only [MessageApplication.latestSubmissionCommand, State.environmentView,
            hserial, hs, hnextLookup, Option.isSome_some, if_true]

/-- At the actual normal environment coordinate, service selects the same
owner envelope that was selected before arbitrary reactions. -/
theorem deliveryBlockEnvironment_normal_include_after_reactions
    (runtime : WindowedApplication P L) (owner : P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (roster recipients : List P) (hroster : roster.Nodup)
    (execution reacted : runtime.application.PolicyExecution)
    (hwait : ∀ history view,
      history.length = (execution.principalHistory owner).length →
        players owner history view = FinDist.pure .wait)
    (hreacted : reacted ∈ (runtime.application.runPolicies players environment
      (roster.map .player) execution).support)
    (instruction : ApplicationInstruction P L)
    (hsubmitter : instruction.submitter = some owner)
    (id : MessageId P)
    (hselected : runtime.application.latestSubmissionCommand owner
      (State.environmentView runtime.application execution.native) = .include id)
    (hindex : runtime.image.instructions[reacted.environmentHistory.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress?
      (State.environmentView runtime.application reacted.native).application.1 =
        some instruction.address)
    (hslot : reacted.environmentHistory.length %
      (recipients.length + roster.length + 2) = recipients.length) :
    runtime.deliveryBlockEnvironment roster recipients reacted.environmentHistory
      (State.environmentView runtime.application reacted.native) =
        FinDist.pure (.include id) := by
  rw [runtime.deliveryBlockEnvironment_normal roster recipients
    reacted.environmentHistory (State.environmentView runtime.application reacted.native)
    instruction hindex hactive hslot]
  have hstable := runtime.runPolicies_reactions_latestSubmissionCommand owner players
    environment roster hroster execution reacted hwait hreacted id hselected
  exact congrArg FinDist.pure
    (runtime.serviceCommand_include_of_latest instruction owner hsubmitter _ id hstable)

/-- The concrete service delivers a selected admissible envelope, allows one
raw reaction per player, and accepts that same envelope at its normal slot.
Only the request owner's reaction is a wait. Other players may randomize,
submit arbitrary payloads, replay known packets, or change their preparation.
The conclusion records the actual accepted public state and receipt. -/
theorem delivery_reaction_normal_accepts (runtime : WindowedApplication P L)
    (owner : P) (players : P → runtime.application.PlayerPolicy)
    (roster recipients : List P) (hroster : roster.Nodup) (blockIndex : Nat)
    (instruction : ApplicationInstruction P L)
    (hsubmitter : instruction.submitter = some owner)
    (execution final : runtime.application.PolicyExecution)
    (hlength : execution.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2))
    (hindex : runtime.image.instructions[blockIndex]? = some instruction)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hwait : ∀ history view, history.length = (execution.principalHistory owner).length →
      players owner history view = FinDist.pure .wait)
    (id : MessageId P) (message : Message P (ApplicationImage.Payload P L))
    (hselected : runtime.application.latestSubmissionCommand owner
      (State.environmentView runtime.application execution.native) = .include id)
    (hlookup : execution.native.pool.lookup id = some message)
    (hauthor : message.payload.OpensCommitment → message.sender = owner)
    (resolved : State P L)
    (haccepted : runtime.handle execution.native.application message = some resolved)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients)
      ((recipients.map fun _ => Invocation.environment) ++
        roster.map Invocation.player ++ [.environment]) execution).support) :
    final.native.application.base.memory = resolved.base.memory ∧
      final.native.application.active = resolved.active ∧
      (id, true) ∈ final.native.receipts := by
  rw [List.append_assoc] at hfinal
  simp only [MessageApplication.runPolicies_append, FinDist.support_bind,
    Set.mem_iUnion] at hfinal
  obtain ⟨delivered, hdelivered, reacted, hreacted, hfinal⟩ := hfinal
  rw [runtime.runPolicies_deliveryPrefix players roster recipients blockIndex instruction id
    execution hlength hindex hactive
    (runtime.serviceCommand_include_of_latest instruction owner hsubmitter _ id hselected)]
    at hdelivered
  obtain ⟨happlication, hpending, hserial, _, hhistory, hdeliveryLength⟩ :=
    runtime.application.runEnvironmentCommands_deliver_frame recipients id execution delivered
      hdelivered
  have hwaitDelivered : ∀ history view,
      history.length = (delivered.principalHistory owner).length →
        players owner history view = FinDist.pure .wait := by
    intro history view hlen
    exact hwait history view (by simpa only [hhistory] using hlen)
  have hselectedDelivered : runtime.application.latestSubmissionCommand owner
      (State.environmentView runtime.application delivered.native) = .include id := by
    simpa only [MessageApplication.latestSubmissionCommand, State.environmentView,
      hserial, MessagePool.lookup, hpending] using hselected
  have hagrees := runtime.runPolicies_reactions_agrees owner players
    (runtime.deliveryBlockEnvironment roster recipients) roster hroster delivered reacted
    hwaitDelivered hreacted
  have hreactive : runtime.image.activeAddress? reacted.native.application.base.memory =
      some instruction.address := by
    rw [← hagrees.base.memory, happlication]
    exact hactive
  have hreactionCount : (roster.map Invocation.player).countP
      (Invocation.isEnvironment (Principal := P)) = 0 := by
    simp [Invocation.isEnvironment]
  have hreactedLength : reacted.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2) + recipients.length := by
    rw [runtime.application.runPolicies_environmentHistory_length players
      (runtime.deliveryBlockEnvironment roster recipients) _ delivered reacted hreacted,
      hreactionCount, Nat.add_zero, hdeliveryLength, hlength]
  have hwidth : 0 < recipients.length + roster.length + 2 := by omega
  have hdiv : reacted.environmentHistory.length /
      (recipients.length + roster.length + 2) = blockIndex := by
    rw [hreactedLength, Nat.mul_comm blockIndex, Nat.mul_add_div hwidth,
      Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hslot : reacted.environmentHistory.length %
      (recipients.length + roster.length + 2) = recipients.length := by
    rw [hreactedLength, Nat.mul_comm blockIndex, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hnormal := runtime.deliveryBlockEnvironment_normal_include_after_reactions owner players
    (runtime.deliveryBlockEnvironment roster recipients) roster recipients hroster delivered
    reacted hwaitDelivered hreacted instruction hsubmitter id hselectedDelivered
    (by rwa [hdiv]) hreactive hslot
  obtain ⟨resolvedNext, hhandle, hresolved⟩ := runtime.runPolicies_reactions_handle_accepted owner
    players (runtime.deliveryBlockEnvironment roster recipients) roster hroster delivered reacted
    hwaitDelivered hreacted message hauthor resolved (by rwa [happlication])
  have hdeliveredLookup : delivered.native.pool.lookup id = some message := by
    simpa only [MessagePool.lookup, hpending] using hlookup
  have hretained := runtime.application.runPolicies_playerOnly_pending_lookup players
    (runtime.deliveryBlockEnvironment roster recipients) (roster.map .player) (by simp)
    delivered reacted id message hdeliveredLookup hreacted
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, hnormal,
    FinDist.pure_bind, FinDist.bind_pure] at hfinal
  simp only [MessageApplication.environmentPolicyStep, EnvironmentPolicyCommand.toAction,
    MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hfinal
  subst final
  rw [MessageApplication.includePending_accept _ _ _ _ _ hretained hhandle]
  exact ⟨hresolved.base.memory.symm, hresolved.active.symm, by simp⟩

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_reactions_latestSubmissionCommand'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_reactions_latestSubmissionCommand

/-- info: 'Vegas.WindowedApplication.deliveryBlockEnvironment_normal_include_after_reactions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.deliveryBlockEnvironment_normal_include_after_reactions

/-- info: 'Vegas.WindowedApplication.delivery_reaction_normal_accepts'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.delivery_reaction_normal_accepts
