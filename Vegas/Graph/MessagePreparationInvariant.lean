/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessagePolicyCommands
import Vegas.Graph.MessageHistoryExtension
import Vegas.Graph.MessageVerification
import Interaction.MessageApplicationAuthorship

/-! # Prepared-candidate agreement for compiled graph players -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- A compiled policy can emit a binding commitment only for its canonical
phase handle, and only after that phase has a recorded preparation. -/
theorem compileAt_commitment_prepared
    (runtime : GraphRuntime Player L Δ) (who : Player)
    {Γ₀ : VCtx Player L} (whole : Graph Player L Γ₀ Δ) :
    ∀ {context : VCtx Player L} (graph : Graph Player L context Δ)
      (policy : BehavioralPolicy who graph) (site : Nat)
      (history : List (Entry runtime)) (view : runtime.application.View)
      (command : Command runtime) (submittedSite : Nat) (handle : Handle Player),
      command ∈ (compileAt runtime who whole graph policy site history view).support →
      command = .submit (.commitment submittedSite handle) →
      handle = (who, .prepared submittedSite) ∧
        ∃ raw, preparedRaw history submittedSite = some raw := by
  intro context graph
  induction graph with
  | ret =>
      intro policy site history view command submittedSite handle supported commandEq
      simp only [compileAt, FinDist.mem_support_pure] at supported
      subst command
      cases supported
  | sample name fresh law next ih =>
      intro policy site history view command submittedSite handle supported commandEq
      simp only [compileAt] at supported
      split at supported
      · simp only [FinDist.mem_support_pure] at supported
        subst command
        contradiction
      · exact ih runtime whole policy (site + 1) history view command submittedSite handle
          supported commandEq
  | bind name owner fresh next ih =>
      intro policy site history view command submittedSite handle supported commandEq
      simp only [compileAt] at supported
      split at supported
      · split at supported
        · split at supported
          · simp only [FinDist.mem_support_pure] at supported
            subst command
            contradiction
          · split at supported
            · rename_i raw prepared
              simp only [FinDist.mem_support_pure] at supported
              rw [supported] at commandEq
              injection commandEq with payloadEq
              injection payloadEq with submittedSiteEq handleEq
              subst submittedSite
              subst handle
              exact ⟨rfl, raw, prepared⟩
            · split at supported
              · split at supported
                · simp only [FinDist.support_map, Set.mem_image] at supported
                  obtain ⟨choice, _, rfl⟩ := supported
                  cases commandEq
                · simp only [FinDist.mem_support_pure] at supported
                  subst command
                  cases supported
              · simp only [FinDist.mem_support_pure] at supported
                subst command
                cases supported
        · simp only [FinDist.mem_support_pure] at supported
          subst command
          contradiction
      · exact ih runtime whole policy.2 (site + 1) history view command submittedSite handle
          supported commandEq
  | resolve output owner binding fresh source checks next ih =>
      intro policy site history view command submittedSite handle supported commandEq
      simp only [compileAt] at supported
      split at supported
      · split at supported
        · split at supported
          · simp only [FinDist.mem_support_pure] at supported
            subst command
            contradiction
          · split at supported
            · split at supported
              · split at supported
                · simp only [FinDist.support_map, Set.mem_image] at supported
                  obtain ⟨choice, _, rfl⟩ := supported
                  contradiction
                · simp only [FinDist.mem_support_pure] at supported
                  subst command
                  cases supported
              · simp only [FinDist.mem_support_pure] at supported
                subst command
                cases supported
            · split at supported
              · split at supported
                · split at supported
                  · simp only [disclosureCommand] at supported
                    split at supported
                    · simp only [FinDist.mem_support_pure] at supported
                      subst command
                      cases supported
                    · split at supported <;>
                        simp only [FinDist.mem_support_pure] at supported <;>
                        subst command <;> cases supported
                  · simp only [FinDist.mem_support_pure] at supported
                    subst command
                    cases supported
                · simp only [FinDist.mem_support_pure] at supported
                  subst command
                  contradiction
              · simp only [FinDist.mem_support_pure] at supported
                subst command
                contradiction
        · simp only [FinDist.mem_support_pure] at supported
          subst command
          cases supported
      · exact ih runtime whole policy.2 (site + 1) history view command submittedSite handle
          supported commandEq

/-- The owner's preparation history exactly describes every canonical
prepared slot in the native candidate catalog. -/
def PreparationAgreement (runtime : GraphRuntime Player L Δ) (who : Player)
    (execution : runtime.application.PolicyExecution) : Prop :=
  ∀ site,
    match preparedRaw (execution.principalHistory who) site with
    | none => execution.native.application.candidates.lookup (who, .prepared site) = .fresh
    | some raw =>
        execution.native.application.candidates.lookup (who, .prepared site) = .openable raw

/-- Every binding commitment in the compiled owner's authenticated submission
history names the canonical slot and follows an earlier preparation. -/
def CommitmentHistory (runtime : GraphRuntime Player L Δ) (who : Player)
    (history : List (Entry runtime)) : Prop :=
  ∀ site handle, .commitment site handle ∈ runtime.application.submittedPayloads history →
    handle = (who, .prepared site) ∧ ∃ raw, preparedRaw history site = some raw

private theorem preparedRaw_append_of_some (runtime : GraphRuntime Player L Δ)
    (history : List (Entry runtime)) (entry : Entry runtime) (site : Nat) (raw : Raw L)
    (prepared : preparedRaw history site = some raw) :
    preparedRaw (history ++ [entry]) site = some raw := by
  unfold preparedRaw at prepared ⊢
  rw [List.findSome?_append, prepared]
  rfl

private theorem preparedRaw_append_other_prepare_none
    (runtime : GraphRuntime Player L Δ) (history : List (Entry runtime))
    (view : runtime.application.View) (slot site : Nat) (raw : Raw L)
    (different : slot ≠ site) (prior : preparedRaw history site = none) :
    preparedRaw (history ++ [⟨view, .privateCommand (.prepare slot raw)⟩]) site = none := by
  unfold preparedRaw at prior ⊢
  rw [List.findSome?_append, prior]
  simp [different]

private theorem preparedRaw_append_nonprepare_none
    (runtime : GraphRuntime Player L Δ) (history : List (Entry runtime))
    (view : runtime.application.View) (command : Command runtime) (site : Nat)
    (notPrepare : ∀ slot raw, command ≠ .privateCommand (.prepare slot raw))
    (prior : preparedRaw history site = none) :
    preparedRaw (history ++ [⟨view, command⟩]) site = none := by
  unfold preparedRaw at prior ⊢
  rw [List.findSome?_append, prior]
  cases command
  · rename_i privateCommand
    cases privateCommand with
    | prepare slot raw => exact (notPrepare slot raw rfl).elim
    | rememberDisclosure disclose => change none = none; rfl
  all_goals change none = none; rfl

def PreparationInvariant (runtime : GraphRuntime Player L Δ) (who : Player)
    (execution : runtime.application.PolicyExecution) : Prop :=
  runtime.application.Authorship execution ∧
    PreparationAgreement runtime who execution ∧
    CommitmentHistory runtime who (execution.principalHistory who)

private theorem playerStep_preparationInvariant
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ Δ)
    (who : Player) (policy : BehavioralPolicy who whole)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : players who = runtime.compilePlayerPolicy whole who policy)
    (execution next : runtime.application.PolicyExecution) (actor : Player)
    (command : Command runtime)
    (chosen : command ∈ (players actor (execution.principalHistory actor)
      (MessageApplication.State.observe runtime.application execution.native actor)).support)
    (invariant : PreparationInvariant runtime who execution)
    (supported : next ∈ (runtime.application.playerStep actor execution command).support) :
    PreparationInvariant runtime who next := by
  rcases invariant with ⟨authorship, agreement, commitments⟩
  have nextAuthorship := runtime.application.playerStep_authorship actor execution next command
    authorship supported
  have historySelf := runtime.application.playerStep_history_self actor execution command next
    supported
  by_cases sameActor : actor = who
  · subst actor
    have nativeMem : next.native ∈
        ((runtime.application.playerStep who execution command).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨next, supported, rfl⟩
    rw [runtime.application.playerStep_native] at nativeMem
    refine ⟨nextAuthorship, ?_, ?_⟩
    · intro site
      cases command with
      | privateCommand privateCommand =>
          cases privateCommand with
          | prepare slot raw =>
              simp only [MessageApplication.PlayerCommand.toAction,
                MessageApplication.step, FinDist.mem_support_pure] at nativeMem
              have candidatesNext : next.native.application.candidates =
                  execution.native.application.candidates.prepare who (.prepared slot) raw := by
                rw [nativeMem]
                exact runtime.privateStep_prepare_candidates execution.native.application
                  who slot raw
              rw [candidatesNext]
              have agree := agreement site
              cases prior : preparedRaw (execution.principalHistory who) site with
              | none =>
                  rw [prior] at agree
                  by_cases sameSlot : slot = site
                  · subst slot
                    rw [historySelf,
                      preparedRaw_append_prepare runtime _ _ site raw prior,
                      CommitmentCandidates.lookup_prepare_self, agree]
                  · rw [historySelf, preparedRaw_append_other_prepare_none runtime _ _ slot
                      site raw sameSlot prior]
                    exact (execution.native.application.candidates.lookup_prepare_other who
                      (.prepared slot) raw (who, .prepared site) (by
                        intro equality
                        have slots := congrArg Prod.snd equality
                        exact sameSlot (Slot.prepared.inj slots).symm)).trans agree
              | some stored =>
                  rw [prior] at agree
                  rw [historySelf,
                    preparedRaw_append_of_some runtime _ _ site stored prior]
                  rw [execution.native.application.candidates.lookup_prepare_eq_of_not_fresh
                    (who, .prepared site) who (.prepared slot) raw (by rw [agree]; simp), agree]
          | rememberDisclosure disclose =>
              simp only [MessageApplication.PlayerCommand.toAction,
                MessageApplication.step, FinDist.mem_support_pure] at nativeMem
              have candidatesNext : next.native.application.candidates =
                  execution.native.application.candidates := by
                rw [nativeMem]
                exact runtime.privateStep_rememberDisclosure_candidates
                  execution.native.application who disclose
              rw [candidatesNext, historySelf]
              have agree := agreement site
              cases prior : preparedRaw (execution.principalHistory who) site with
              | none =>
                  rw [prior] at agree
                  rw [preparedRaw_append_nonprepare_none runtime _ _ _ site
                    (by intros; simp) prior, agree]
              | some raw =>
                  rw [prior] at agree
                  rw [preparedRaw_append_of_some runtime _ _ site raw prior,
                    agree]
      | submit payload | replay payload | wait =>
          simp only [MessageApplication.PlayerCommand.toAction,
            MessageApplication.step, FinDist.mem_support_pure] at nativeMem
          have candidatesNext : next.native.application.candidates =
              execution.native.application.candidates := by rw [nativeMem]
          rw [candidatesNext, historySelf]
          have agree := agreement site
          cases prior : preparedRaw (execution.principalHistory who) site with
          | none =>
              rw [prior] at agree
              rw [preparedRaw_append_nonprepare_none runtime _ _ _ site
                (by intros; simp) prior, agree]
          | some raw =>
              rw [prior] at agree
              rw [preparedRaw_append_of_some runtime _ _ site raw prior,
                agree]
    · intro site handle submitted
      cases command with
      | privateCommand privateCommand =>
          rw [historySelf]
          rw [historySelf, runtime.application.submittedPayloads_append_privateCommand]
            at submitted
          obtain ⟨canonical, raw, prepared⟩ := commitments site handle submitted
          exact ⟨canonical, raw, preparedRaw_append_of_some runtime _ _ site raw prepared⟩
      | submit payload =>
          rw [historySelf]
          rw [historySelf, runtime.application.submittedPayloads_append_submit] at submitted
          rcases List.mem_append.mp submitted with old | new
          · obtain ⟨canonical, raw, prepared⟩ := commitments site handle old
            exact ⟨canonical, raw,
              preparedRaw_append_of_some runtime _ _ site raw prepared⟩
          · simp only [List.mem_singleton] at new
            subst payload
            rw [compiled] at chosen
            obtain ⟨canonical, raw, prepared⟩ := compileAt_commitment_prepared runtime who
              whole whole policy 0 (execution.principalHistory who)
              (MessageApplication.State.observe runtime.application execution.native who)
              (.submit (.commitment site handle)) site handle chosen rfl
            exact ⟨canonical, raw,
              preparedRaw_append_of_some runtime _ _ site raw prepared⟩
      | replay id =>
          rw [historySelf]
          rw [historySelf, runtime.application.submittedPayloads_append_replay] at submitted
          obtain ⟨canonical, raw, prepared⟩ := commitments site handle submitted
          exact ⟨canonical, raw, preparedRaw_append_of_some runtime _ _ site raw prepared⟩
      | wait =>
          rw [historySelf]
          rw [historySelf, runtime.application.submittedPayloads_append_wait] at submitted
          obtain ⟨canonical, raw, prepared⟩ := commitments site handle submitted
          exact ⟨canonical, raw, preparedRaw_append_of_some runtime _ _ site raw prepared⟩
  · have historyOther := runtime.application.playerStep_other_history actor who
      (Ne.symm sameActor) execution command next supported
    refine ⟨nextAuthorship, ?_, ?_⟩
    · intro site
      rw [historyOther]
      have nativeMem : next.native ∈
          ((runtime.application.playerStep actor execution command).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨next, supported, rfl⟩
      rw [runtime.application.playerStep_native] at nativeMem
      cases command with
      | privateCommand privateCommand =>
          cases privateCommand with
          | prepare slot raw =>
              simp only [MessageApplication.PlayerCommand.toAction,
                MessageApplication.step, FinDist.mem_support_pure] at nativeMem
              have candidatesNext : next.native.application.candidates =
                  execution.native.application.candidates.prepare actor (.prepared slot) raw := by
                rw [nativeMem]
                exact runtime.privateStep_prepare_candidates execution.native.application
                  actor slot raw
              rw [candidatesNext]
              have different : (who, Slot.prepared site) ≠ (actor, .prepared slot) := by
                intro equality
                exact sameActor (congrArg Prod.fst equality).symm
              rw [execution.native.application.candidates.lookup_prepare_other actor
                (.prepared slot) raw (who, .prepared site) different]
              exact agreement site
          | rememberDisclosure disclose =>
              simp only [MessageApplication.PlayerCommand.toAction,
                MessageApplication.step, FinDist.mem_support_pure] at nativeMem
              have candidatesNext : next.native.application.candidates =
                  execution.native.application.candidates := by
                rw [nativeMem]
                exact runtime.privateStep_rememberDisclosure_candidates
                  execution.native.application actor disclose
              rw [candidatesNext]
              exact agreement site
      | submit payload | replay payload | wait =>
          simp only [MessageApplication.PlayerCommand.toAction,
            MessageApplication.step, FinDist.mem_support_pure] at nativeMem
          have candidatesNext : next.native.application.candidates =
              execution.native.application.candidates := by rw [nativeMem]
          rw [candidatesNext]
          exact agreement site
    · simpa [historyOther] using commitments

/-- An accepted commitment using one of a compiled player's canonical handles
has an authenticated preparation marker for that slot. -/
theorem accepted_commitment_was_prepared
    (runtime : GraphRuntime Player L Δ) (who : Player)
    (execution : runtime.application.PolicyExecution)
    (authorship : runtime.application.Authorship execution)
    (commitments : CommitmentHistory runtime who (execution.principalHistory who))
    (message : Message Player (Payload Player L)) (next : State Player L Δ)
    (id : MessageId Player)
    (packetSite site : Nat) (handle : Handle Player)
    (lookup : execution.native.pool.lookup id = some message)
    (payload : message.payload = .commitment packetSite handle)
    (accepted : runtime.handle execution.native.application message = some next)
    (sameHandle : handle = (who, .prepared site)) :
    ∃ raw, preparedRaw (execution.principalHistory who) site = some raw := by
  have safe := authorship.2.1 message (List.mem_of_find?_eq_some lookup)
  have sender := runtime.handle_commitment_sender execution.native.application next message
    packetSite handle payload accepted
  rw [sameHandle] at sender
  have senderEq : message.sender = who := sender.symm
  have submitted : message.payload ∈
      runtime.application.submittedPayloads
        (execution.principalHistory message.sender) := by
    change (runtime.application.submittedPayloads
      (execution.principalHistory message.id.1))[message.id.2]? = some message.payload at safe
    rw [List.getElem?_eq_some_iff] at safe
    rw [List.mem_iff_getElem]
    exact ⟨message.id.2, safe.1, safe.2⟩
  rw [senderEq, payload] at submitted
  obtain ⟨canonical, raw, prepared⟩ := commitments packetSite handle submitted
  rw [sameHandle] at canonical
  have sites : packetSite = site :=
    Slot.prepared.inj (congrArg Prod.snd canonical).symm
  subst packetSite
  exact ⟨raw, prepared⟩

private theorem environmentStep_preparationInvariant
    (runtime : GraphRuntime Player L Δ) (who : Player)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (invariant : PreparationInvariant runtime who execution)
    (supported : next ∈
      (runtime.application.environmentPolicyStep execution command).support) :
    PreparationInvariant runtime who next := by
  rcases invariant with ⟨authorship, agreement, commitments⟩
  have nextAuthorship := runtime.application.environmentStep_authorship execution next command
    authorship supported
  have histories := runtime.application.environmentStep_principalHistory execution command next
    supported
  refine ⟨nextAuthorship, ?_, ?_⟩
  · intro site
    rw [congrFun histories who]
    have nativeMem : next.native ∈
        ((runtime.application.environmentPolicyStep execution command).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨next, supported, rfl⟩
    rw [runtime.application.environmentStep_native] at nativeMem
    cases command with
    | deliver observer id | wait =>
        simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
          MessageApplication.step, FinDist.mem_support_pure] at nativeMem
        rw [nativeMem]
        exact agreement site
    | application applicationCommand =>
        cases applicationCommand with
        | tick =>
            simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
              MessageApplication.step, FinDist.support_map, Set.mem_image] at nativeMem
            obtain ⟨applicationNext, tickMem, nativeEq⟩ := nativeMem
            rw [← nativeEq, runtime.tick_candidates execution.native.application applicationNext
              tickMem]
            exact agreement site
    | «include» id =>
        simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
          MessageApplication.step, FinDist.mem_support_pure] at nativeMem
        rw [nativeMem]
        cases lookup : execution.native.pool.lookup id with
        | none =>
            rw [runtime.application.includePending_missing execution.native id lookup]
            exact agreement site
        | some message =>
            cases accepted : runtime.handle execution.native.application message with
            | none =>
                rw [runtime.application.includePending_reject execution.native id message lookup
                  accepted]
                exact agreement site
            | some applicationNext =>
                rw [runtime.application.includePending_accept execution.native id message
                  applicationNext lookup accepted]
                have candidatesNext := runtime.handle_candidates execution.native.application
                  applicationNext message accepted
                cases payload : message.payload with
                | commitment packetSite handle =>
                    rw [payload] at candidatesNext
                    rw [candidatesNext]
                    have agree := agreement site
                    cases prior : preparedRaw (execution.principalHistory who) site with
                    | some raw =>
                        rw [prior] at agree
                        rw [execution.native.application.candidates.lookup_accept_eq_of_not_fresh
                          (who, .prepared site) handle (by rw [agree]; simp), agree]
                    | none =>
                        rw [prior] at agree
                        have different : handle ≠ (who, .prepared site) := by
                          intro sameHandle
                          obtain ⟨raw, prepared⟩ := accepted_commitment_was_prepared runtime who
                            execution authorship commitments message applicationNext id packetSite
                            site handle lookup payload accepted sameHandle
                          rw [prior] at prepared
                          contradiction
                        rw [execution.native.application.candidates.lookup_accept_other handle
                          (who, .prepared site) (Ne.symm different), agree]
                | opening packetSite handle raw | withhold packetSite | malformed raw =>
                    rw [payload] at candidatesNext
                    rw [candidatesNext]
                    exact agreement site
  · simpa [histories] using commitments

theorem initial_preparationInvariant (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (input : VEnv L Γ) (who : Player) :
    PreparationInvariant runtime who
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial graph input))) := by
  refine ⟨MessageApplication.PolicyExecution.initial_authorship runtime.application _, ?_, ?_⟩
  · intro site
    change (State.initial graph input).candidates.lookup (who, .prepared site) = .fresh
    exact State.initial_prepared_fresh graph input who site
  · intro site handle submitted
    simp [MessageApplication.PolicyExecution.initial,
      MessageApplication.State.initial, MessageApplication.submittedPayloads] at submitted

/-- Arbitrary other players and an arbitrary environment cannot break the
agreement between one compiled player's preparation history and its canonical
candidate slots. -/
theorem runPolicies_initial_preparationInvariant
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    (input : VEnv L Γ) (who : Player) (policy : BehavioralPolicy who graph)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : players who = runtime.compilePlayerPolicy graph who policy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial graph input)))).support) :
    PreparationInvariant runtime who next := by
  apply runtime.application.runPolicies_execution_invariant
    (PreparationInvariant runtime who) players environment
  · intro current actor command after currentInvariant commandMem stepMem
    exact playerStep_preparationInvariant runtime graph who policy players compiled current after
      actor command commandMem currentInvariant stepMem
  · intro current command after currentInvariant _commandMem stepMem
    exact environmentStep_preparationInvariant runtime who current after command currentInvariant
      stepMem
  · exact initial_preparationInvariant runtime graph input who
  · exact supported

end Vegas.GraphRuntime
