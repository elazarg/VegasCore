/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventCandidateProtection
import Vegas.Pending.EventServiceLaw

/-! # Admission resources for prescribed event handles

Every unfinished event has an empty acceptance cell. The canonical prepared
handle of a prescribed owner remains unused until its own event completes.
The latter fact uses authenticated packet provenance, including replay.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- The two admission resources needed to accept a prescribed commitment.
Candidate meaning and policy history are separate from these resources. -/
def State.CanonicalResources (state : State graph) (owner : Player) : Prop :=
  ∀ event, event ∉ state.config.cut.completed →
    state.accepted (.inr event) = none ∧ state.HandleUnused (owner, eventSlot event)

theorem State.canonicalResources_initial (inputs : graph.Inputs) (owner : Player) :
    (State.initial inputs).CanonicalResources owner := by
  intro event _
  refine ⟨rfl, ?_⟩
  intro field accepted
  obtain ⟨input, actualOwner, payload, _, _, impossible⟩ :=
    initial_accepted_eq_some inputs field (owner, eventSlot event) accepted
  have slots := congrArg Prod.snd impossible
  cases slots

theorem privateStep_canonicalResources (state : State graph) (owner who : Player)
    (command : PrivateCommand graph) (resources : state.CanonicalResources owner) :
    (privateStep state who command).CanonicalResources owner := by
  simpa only [State.CanonicalResources, State.HandleUnused,
    (privateStep_facts state who command).1, privateStep_accepted] using resources

theorem handle_canonicalResources (runtime : EventGraphRuntime graph)
    (state next : State graph) (owner : Player) (message : Message Player (Payload graph))
    (resources : state.CanonicalResources owner)
    (canonical : CanonicalCommitments owner message)
    (accepted : runtime.handle state message = some next) :
    next.CanonicalResources owner := by
  intro event unfinished
  have prior := resources event (fun completed =>
    unfinished (handle_completed_subset runtime state next message accepted completed))
  have frames := runtime.handle_unfinished_canonical_resources
    state next message owner event canonical accepted unfinished
  exact ⟨frames.2.1.trans prior.1, frames.2.2 prior.2⟩

omit [DecidableEq Player] in
theorem environmentStep_canonicalResources (runtime : EventGraphRuntime graph)
    (state next : State graph) (owner : Player) (command : EnvironmentCommand graph)
    (resources : state.CanonicalResources owner)
    (supported : next ∈ (environmentStep runtime state command).support) :
    next.CanonicalResources owner := by
  have completed := environmentStep_completed_subset runtime state next command supported
  have tables := (environmentStep_tables runtime state next command supported).1
  intro event unfinished
  have prior := resources event (fun done => unfinished (completed done))
  simpa only [State.HandleUnused, tables] using prior

theorem playerStep_canonicalResources (runtime : EventGraphRuntime graph)
    (state next : runtime.application.PolicyExecution) (owner who : Player)
    (command : runtime.application.PlayerCommand)
    (resources : state.native.application.CanonicalResources owner)
    (supported : next ∈ (runtime.application.playerStep who state command).support) :
    next.native.application.CanonicalResources owner := by
  have native : next.native ∈
      ((runtime.application.playerStep who state command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.playerStep_native] at native
  cases command with
  | privateCommand command =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native]
      exact privateStep_canonicalResources state.native.application owner who command resources
  | submit packet | replay id | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native]
      exact resources

theorem environmentPolicyStep_canonicalResources (runtime : EventGraphRuntime graph)
    (state next : runtime.application.PolicyExecution) (owner : Player)
    (command : runtime.application.EnvironmentPolicyCommand)
    (safe : state.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner))
    (resources : state.native.application.CanonicalResources owner)
    (supported : next ∈ (runtime.application.environmentPolicyStep state command).support) :
    next.native.application.CanonicalResources owner := by
  have native : next.native ∈
      ((runtime.application.environmentPolicyStep state command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at native
  cases command with
  | deliver observer id | wait =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native]
      exact resources
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native]
      cases found : state.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing state.native id found]
          exact resources
      | some message =>
          cases accepted : runtime.handle state.native.application message with
          | none =>
              rw [runtime.application.includePending_reject state.native id message found accepted]
              exact resources
          | some application =>
              rw [runtime.application.includePending_accept state.native id message application
                found accepted]
              exact runtime.handle_canonicalResources state.native.application application owner
                message resources (safe.1 message (List.mem_of_find?_eq_some found)) accepted
  | application command =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.support_map, Set.mem_image] at native
      obtain ⟨application, member, same⟩ := native
      rw [← same]
      exact environmentStep_canonicalResources runtime state.native.application application
        owner command resources member

theorem serviceStep_canonicalResources (runtime : EventGraphRuntime graph)
    (owner : Player) (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (safe : before.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner))
    (resources : before.native.application.CanonicalResources owner)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    after.native.application.CanonicalResources owner := by
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      exact runtime.playerStep_canonicalResources before after owner who command resources step
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      exact runtime.environmentPolicyStep_canonicalResources before after owner command
        safe resources step
  | grant event | includeLatest event who | sample event | tick | expire event =>
      exact runtime.environmentPolicyStep_canonicalResources before after owner _ safe
        resources member

private theorem serviceStep_resources_and_provenance (runtime : EventGraphRuntime graph)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (holds : before.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner) ∧
      before.native.application.CanonicalResources owner)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    after.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner) ∧
      after.native.application.CanonicalResources owner := by
  refine ⟨?_, runtime.serviceStep_canonicalResources owner players wire instruction before after
    holds.1 holds.2 member⟩
  apply runtime.runServicePlan_canonicalCommitments owner policy players prescribed wire
    [instruction] before after holds.1
  simpa [runServicePlan] using member

/-- Admission resources survive arbitrary intermediate instructions whenever
the owner follows its compiled policy. Every other player remains unrestricted. -/
theorem runServicePlan_canonicalResources (runtime : EventGraphRuntime graph)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (safe : before.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner))
    (resources : before.native.application.CanonicalResources owner)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    after.native.application.CanonicalResources owner := by
  exact (runtime.runServicePlan_invariant players wire _
    (runtime.serviceStep_resources_and_provenance owner policy players prescribed wire)
    plan before after ⟨safe, resources⟩ member).2

/-- Canonical vacant/non-aliasing resources hold throughout initialized
adaptive service, including replayed copies of the owner's messages. -/
theorem runService_initial_canonicalResources (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (owner : Player) (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.runService roster reactionRounds players wire order count
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs)))).support) :
    after.native.application.CanonicalResources owner := by
  exact (runtime.runService_invariant roster reactionRounds players wire order _
    (runtime.serviceStep_resources_and_provenance owner policy players prescribed wire)
    count _ after ⟨MessagePool.Satisfies.empty, State.canonicalResources_initial inputs owner⟩
    member).2

end Vegas.EventGraphRuntime
