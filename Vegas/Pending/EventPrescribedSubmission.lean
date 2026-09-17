/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventCanonicalResources
import Vegas.Pending.EventDisclosure
import Interaction.MessageApplicationAuthorship

/-! # Pending prescribed packets and competing inclusions

An inclusion cannot discard an acceptable prescribed packet without completing
its event. Binding acceptance follows from the canonical admission resources;
resolution acceptance follows from the stored action and binding provenance.
The selected envelope may be a replay and need not be the prescribed packet.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A newly recorded submission is an actual pending authenticated envelope.
The statement makes no assumption about the owner's policy or the payload's
validity; history changes only when that owner submits. -/
theorem serviceStep_new_submission (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution) (owner : Player)
    (event : graph.EventId)
    (notSubmitted : submittedAt (before.principalHistory owner) event = false)
    (submitted : submittedAt (after.principalHistory owner) event = true)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    ∃ message ∈ after.native.pool.pending, Payload.Matches event owner message := by
  have impossible (histories : after.principalHistory owner = before.principalHistory owner) :
      False := by
    rw [histories, notSubmitted] at submitted
    contradiction
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      by_cases same : who = owner
      · subst who
        have history := runtime.application.playerStep_history_self owner before command after step
        rw [history] at submitted
        cases command with
        | privateCommand command | wait | replay id =>
            simp only [submittedAt, List.any_append, List.any_cons, List.any_nil,
              Bool.or_false] at submitted
            change submittedAt (before.principalHistory owner) event = true at submitted
            rw [notSubmitted] at submitted
            contradiction
        | submit packet =>
            have addressed : packet.event? graph = some event := by
              simpa only [submittedAt_append_submit, notSubmitted, Bool.false_or,
                decide_eq_true_eq] using submitted
            rw [runtime.application.playerStep_submit_eq, FinDist.mem_support_pure] at step
            subst after
            refine ⟨⟨(owner, before.native.pool.nextSerial owner), packet⟩, ?_, rfl, addressed⟩
            exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact (impossible (runtime.application.playerStep_other_history who owner (Ne.symm same)
          before command after step)).elim
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      exact (impossible (congrFun (runtime.application.environmentStep_principalHistory before
        command after step) owner)).elim
  | grant query | includeLatest query who | sample query | tick | expire query =>
      exact (impossible (congrFun (runtime.application.environmentStep_principalHistory before
        _ after member) owner)).elim

/-- A pending accepted packet survives another inclusion, unless that
inclusion completes its event. Duplicate identifiers need no special case. -/
theorem include_pending_or_completed (runtime : EventGraphRuntime graph)
    (native : runtime.application.State) (message : Message Player (Payload graph))
    (event : graph.EventId) (next : State graph)
    (pending : message ∈ native.pool.pending)
    (addressed : message.payload.event? graph = some event)
    (accepted : runtime.handle native.application message = some next)
    (selected : MessageId Player) :
    event ∈ (runtime.application.includePending native selected).application.config.cut.completed ∨
      message ∈ (runtime.application.includePending native selected).pool.pending := by
  rcases native.pool.pending_retained_or_selected selected message pending with retained | found
  · exact Or.inr (by simpa only [MessageApplication.includePending_pool] using retained)
  · rw [runtime.application.includePending_accept native selected message next found accepted]
    obtain ⟨actual, actualAddress, ready, action, member⟩ :=
      runtime.handle_config_mem_step native.application next message accepted
    have same : actual = event := Option.some.inj (actualAddress.symm.trans addressed)
    subst actual
    left
    rw [native.application.config.step_cut event ready action next.config member]
    exact Finset.mem_insert_self _ _

/-- Any native action retains an acceptable pending packet or completes its
event. Only inclusion can remove it; replay and submission can add traffic. -/
theorem applicationStep_pending_or_completed (runtime : EventGraphRuntime graph)
    (native after : runtime.application.State) (message : Message Player (Payload graph))
    (event : graph.EventId) (next : State graph)
    (pending : message ∈ native.pool.pending)
    (addressed : message.payload.event? graph = some event)
    (accepted : runtime.handle native.application message = some next)
    (command : runtime.application.Action)
    (member : after ∈ (runtime.application.step native command).support) :
    event ∈ after.application.config.cut.completed ∨ message ∈ after.pool.pending := by
  cases command with
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst after
      exact Or.inr pending
  | submit who packet =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst after
      exact Or.inr (List.mem_append_left _ pending)
  | replay who id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst after
      right
      unfold MessagePool.replay
      split
      · exact List.mem_append_left _ pending
      · exact pending
  | deliver who id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst after
      right
      simpa only [MessagePool.deliver_preserves_pending] using pending
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at member
      subst after
      exact runtime.include_pending_or_completed native message event next pending addressed
        accepted id
  | environment command =>
      simp only [MessageApplication.step, FinDist.support_map, Set.mem_image] at member
      obtain ⟨application, _, rfl⟩ := member
      exact Or.inr pending

/-- Every concrete service instruction satisfies the same packet retention
law, regardless of the invoked player and public wire policies. -/
theorem serviceStep_pending_or_completed (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (message : Message Player (Payload graph)) (event : graph.EventId) (next : State graph)
    (pending : message ∈ before.native.pool.pending)
    (addressed : message.payload.event? graph = some event)
    (accepted : runtime.handle before.native.application message = some next)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    event ∈ after.native.application.config.cut.completed ∨
      message ∈ after.native.pool.pending := by
  rcases runtime.serviceStep_native_step players wire instruction before after member with
    same | ⟨command, supported⟩
  · exact Or.inr (by simpa only [same] using pending)
  · exact runtime.applicationStep_pending_or_completed before.native after.native message event
      next pending addressed accepted command supported

/-- A canonical commitment is accepted whenever its event is ready and
timely. The candidate may denote either a value or binding failure. -/
theorem handle_canonical_commitment_isSome (runtime : EventGraphRuntime graph)
    (state : State graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (view : nodeView graph event = .bind owner payload outputEq codeEq)
    (ready : state.config.cut.Ready event) (timely : state.WithinDeadline runtime event)
    (resources : state.CanonicalResources owner) (nonce : Nat) :
    (runtime.handle state ⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩).isSome := by
  obtain ⟨vacant, unused⟩ := resources event ready.1
  rw [runtime.handle_commitment_eq state (owner, nonce) event (owner, eventSlot event)
    owner payload outputEq codeEq view ready timely rfl rfl vacant unused]
  rfl

/-- An arbitrary selected inclusion retains the exact prescribed binding
packet or completes its event. This supplies the packet-availability part of
one-shot submission protection. -/
theorem include_canonical_commitment_pending_or_completed (runtime : EventGraphRuntime graph)
    (native : runtime.application.State) (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (view : nodeView graph event = .bind owner payload outputEq codeEq)
    (ready : native.application.config.cut.Ready event)
    (timely : native.application.WithinDeadline runtime event)
    (resources : native.application.CanonicalResources owner)
    (nonce : Nat)
    (pending : (⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ :
      Message Player (Payload graph)) ∈ native.pool.pending)
    (selected : MessageId Player) :
    event ∈ (runtime.application.includePending native selected).application.config.cut.completed ∨
      (⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ :
        Message Player (Payload graph)) ∈
          (runtime.application.includePending native selected).pool.pending := by
  have existsNext := runtime.handle_canonical_commitment_isSome native.application owner
    event payload outputEq codeEq view ready timely resources nonce
  obtain ⟨next, accepted⟩ := Option.isSome_iff_exists.mp existsNext
  exact runtime.include_pending_or_completed native _ event next pending rfl accepted selected

/-- A prescribed disclosure packet is retained or completes its event, even
when its cached `true` action resolves to failure and sends withholding. -/
theorem include_resolution_pending_or_completed (runtime : EventGraphRuntime graph)
    (native : runtime.application.State) (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (view : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : native.application.config.cut.Ready event)
    (timely : native.application.WithinDeadline runtime event)
    (action : graph.Action event)
    (remembered : native.application.remembered event = some action)
    (invariant : native.application.BindingInvariant)
    (packet : Payload graph) (nonce : Nat)
    (submission : runtime.resolutionSubmission owner event payload binding checks outputEq action
      (MessageApplication.State.observe runtime.application native owner) = .submit packet)
    (pending : (⟨(owner, nonce), packet⟩ : Message Player (Payload graph)) ∈ native.pool.pending)
    (selected : MessageId Player) :
    event ∈ (runtime.application.includePending native selected).application.config.cut.completed ∨
      (⟨(owner, nonce), packet⟩ : Message Player (Payload graph)) ∈
        (runtime.application.includePending native selected).pool.pending := by
  obtain ⟨result, actual, _, actualSubmission, accepted⟩ :=
    runtime.handle_resolutionSubmission_eq native event owner payload binding checks outputEq
      codeEq view ready timely action remembered invariant nonce
  have same : actual = packet :=
    MessageInterface.PlayerCommand.submit.inj (actualSubmission.symm.trans submission)
  subst actual
  obtain ⟨addressed, chosen, address⟩ := runtime.resolutionSubmission_address owner event payload
    binding checks outputEq action
    (MessageApplication.State.observe runtime.application native owner)
  have packetEq : packet = addressed :=
    MessageInterface.PlayerCommand.submit.inj (submission.symm.trans chosen)
  subst addressed
  exact runtime.include_pending_or_completed native _ event _ pending address accepted selected

/-- Reserved service completes the requested event when a matching packet is
pending and each matching authenticated packet satisfies the local handler.
Authentication ensures the identifier lookup retrieves the selected envelope. -/
theorem serviceStep_includeLatest_completes (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (event : graph.EventId) (owner : Player)
    (before after : runtime.application.PolicyExecution)
    (authorship : runtime.application.Authorship before)
    (pending : ∃ message ∈ before.native.pool.pending, Payload.Matches event owner message)
    (accepted : ∀ message ∈ before.native.pool.pending, Payload.Matches event owner message →
      ∃ next, runtime.handle before.native.application message = some next)
    (member : after ∈
      (runtime.serviceStep players wire (.includeLatest event owner) before).support) :
    event ∈ after.native.application.config.cut.completed := by
  obtain ⟨witness, witnessMem, witnessMatches⟩ := pending
  obtain ⟨selected, found⟩ := latestEventSubmission?_exists before.native.pool event owner
    witness witnessMem witnessMatches
  have spec := latestEventSubmission?_spec before.native.pool event owner selected found
  obtain ⟨next, handled⟩ := accepted selected spec.1 spec.2
  have lookup := MessageApplication.Authorship.lookup_eq_of_mem_pending runtime.application
    before authorship selected spec.1
  have command : runtime.latestEventSubmissionCommand event owner
      (MessageApplication.State.environmentView runtime.application before.native) =
        .include selected.id := by
    unfold latestEventSubmissionCommand
    change (match latestEventSubmission? before.native.pool event owner with
      | some message => MessageInterface.EnvironmentPolicyCommand.include message.id
      | none => MessageInterface.EnvironmentPolicyCommand.wait) = _
    rw [found]
  change after ∈ (runtime.application.environmentPolicyStep before _).support at member
  rw [command] at member
  have native : after.native ∈
      ((runtime.application.environmentPolicyStep before (.include selected.id)).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨after, member, rfl⟩
  rw [runtime.application.environmentStep_native] at native
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, FinDist.mem_support_pure] at native
  rw [native, runtime.application.includePending_accept before.native selected.id selected
    next lookup handled]
  obtain ⟨actual, address, ready, action, step⟩ :=
    runtime.handle_config_mem_step before.native.application next selected handled
  have same : actual = event := Option.some.inj (address.symm.trans spec.2.2)
  subst actual
  rw [before.native.application.config.step_cut event ready action next.config step]
  exact Finset.mem_insert_self _ _

end Vegas.EventGraphRuntime
