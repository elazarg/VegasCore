/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationLaws
import Interaction.SealedResolutionEvents
import Interaction.SealedResolutionProgress

/-! # Inclusion of ready sealed-resolution submissions

Canonical commitment and opening messages complete their nodes when the
private value and public prerequisites are ready.  The result is stated at the
actual pending-message inclusion boundary, including the case where a timeout
has already completed the node before inclusion.
-/

noncomputable section

namespace Interaction.SealedResolution

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- A completed commit event determines the canonical public handle without a
global event-node uniqueness assumption. -/
theorem EventInvariant.accepted?_eq_some_of_done_commit
    {runtime : SealedResolution Principal Value}
    {state : ApplicationState Principal Value}
    (invariant : EventInvariant runtime state)
    (node : Nat) (owner : Principal) (requires : List Nat)
    (hrule : runtime.program.rules[node]? =
      some { kind := .commit owner, requires })
    (hdone : SealedProgram.done state.visible.events node = true) :
    SealedProgram.accepted? state.visible.events node = some (owner, node) := by
  have hcanonical := invariant.accepted_of_done_commit node owner requires hrule hdone
  cases hfound : SealedProgram.accepted? state.visible.events node with
  | none =>
      unfold SealedProgram.accepted? at hfound
      have himpossible := List.findSome?_eq_none_iff.mp hfound _ hcanonical
      simp at himpossible
  | some handle =>
      have hmem := SealedProgram.accepted_mem_of_accepted?_eq_some hfound
      obtain ⟨eventOwner, value, rule, heventRule, hkind, hhandle, hlookup⟩ :=
        invariant.acceptedBinding.accepted node handle hmem
      rw [hrule] at heventRule
      have hrules := Option.some.inj heventRule
      have hkinds := congrArg SealedRule.kind hrules
      simp only [hkind, SealedRuleKind.commit.injEq] at hkinds
      subst eventOwner
      subst handle
      rfl

variable [DecidableEq Principal] [DecidableEq Value]

omit [DecidableEq Principal] [DecidableEq Value] in
theorem handle_preserves_completed {Service : Type (max uPrincipal uValue)}
    (runtime : SealedResolution Principal Value)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
        Option (ApplicationState Principal Value Service))
    (hrecords : runtime.HandlerRecords applyMessage)
    (state next : ApplicationState Principal Value Service)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (hcompleted : state.visible.completed node = true)
    (hhandle : applyMessage state message = some next) :
    next.visible.completed node = true := by
  obtain ⟨event, heffect⟩ := hrecords state message next hhandle
  rw [heffect]
  apply runtime.refresh_completed false _ node
  unfold PublicState.completed SealedProgram.done at hcompleted ⊢
  cases hevents : state.visible.events.any (fun event => event.node == node) <;>
    cases htimeouts : state.visible.timeouts.contains node <;> simp_all

private theorem handle_completed_of_valid
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (event : SealedProgram.Event Principal Value) (node : Nat)
    (hvalid : runtime.validateMessage? state message = some event)
    (hevent : event.node = node) :
    ∃ next, runtime.handle state message = some next ∧
      next.visible.completed node = true := by
  let recorded : PublicState Principal Value :=
    { state.visible with events := state.visible.events ++ [event] }
  let next : ApplicationState Principal Value :=
    { state with visible := runtime.refresh false recorded }
  refine ⟨next, ?_, ?_⟩
  · simp [SealedResolution.handle, hvalid, next, recorded]
  · apply runtime.refresh_completed false recorded node
    unfold PublicState.completed SealedProgram.done
    simp [recorded, hevent]

private theorem validateMessage?_commitment
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value)
    (owner : Principal) (serial node : Nat) (requires : List Nat) (value : Value)
    (hrule : runtime.program.rules[node]? =
      some { kind := .commit owner, requires })
    (hstored : state.service.lookup (owner, node) = some value)
    (hrequires : requires.all state.visible.completed = true)
    (hcompleted : state.visible.completed node = false) :
    runtime.validateMessage? state
      ⟨(owner, serial), .commitment node (owner, node)⟩ =
        some (.accepted node (owner, node)) := by
  have hdone : SealedProgram.done state.visible.events node = false := by
    cases h : SealedProgram.done state.visible.events node <;>
      simp_all [PublicState.completed]
  have htimeout : state.visible.timeouts.contains node = false := by
    cases h : state.visible.timeouts.contains node <;>
      simp_all [PublicState.completed]
  have hdischarged :
      (runtime.program.discharge state.visible.timeouts).rules[node]? =
        some (({ kind := .commit owner, requires } : SealedRule Principal).discharge
          state.visible.timeouts) := by
    simp [SealedProgram.discharge, hrule]
  have hprerequisites :
      SealedProgram.prerequisitesDone state.visible.events
          (({ kind := .commit owner, requires } : SealedRule Principal).discharge
            state.visible.timeouts) = true := by
    rw [state.visible.prerequisitesDone_discharge]
    exact hrequires
  unfold SealedResolution.validateMessage?
  simp only [SealedProgram.Payload.node?, Option.any_some, htimeout,
    Bool.false_eq_true, ↓reduceIte]
  unfold SealedProgram.validateMessage?
  dsimp only
  rw [hdischarged]
  simp [Message.sender, hdone, hstored, hprerequisites]
  simp [SealedRule.discharge]

private theorem validateMessage?_opening
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value)
    (owner : Principal) (serial node source : Nat) (requires : List Nat) (value : Value)
    (hrule : runtime.program.rules[node]? =
      some { kind := .reveal owner source, requires })
    (haccepted : SealedProgram.accepted? state.visible.events source =
      some (owner, source))
    (hstored : state.service.lookup (owner, source) = some value)
    (hrequires : requires.all state.visible.completed = true)
    (hcompleted : state.visible.completed node = false) :
    runtime.validateMessage? state
      ⟨(owner, serial), .opening node (owner, source) value⟩ =
        some (.opened node value) := by
  have hdone : SealedProgram.done state.visible.events node = false := by
    cases h : SealedProgram.done state.visible.events node <;>
      simp_all [PublicState.completed]
  have htimeout : state.visible.timeouts.contains node = false := by
    cases h : state.visible.timeouts.contains node <;>
      simp_all [PublicState.completed]
  have hdischarged :
      (runtime.program.discharge state.visible.timeouts).rules[node]? =
        some (({ kind := .reveal owner source, requires } : SealedRule Principal).discharge
          state.visible.timeouts) := by
    simp [SealedProgram.discharge, hrule]
  have hprerequisites :
      SealedProgram.prerequisitesDone state.visible.events
          (({ kind := .reveal owner source, requires } : SealedRule Principal).discharge
            state.visible.timeouts) = true := by
    rw [state.visible.prerequisitesDone_discharge]
    exact hrequires
  unfold SealedResolution.validateMessage?
  simp only [SealedProgram.Payload.node?, Option.any_some, htimeout,
    Bool.false_eq_true, ↓reduceIte]
  unfold SealedProgram.validateMessage?
  dsimp only
  rw [hdischarged]
  simp [Message.sender, hdone, hstored, hprerequisites,
    IdealCommitments.verify_stored]
  simp [SealedRule.discharge, haccepted]

/-- Including a pending canonical commitment completes its node whenever its
private slot and prerequisites are ready.  Existing timeout completion is
preserved when the validator rejects the now-late message. -/
theorem includePending_commitment_completed
    (runtime : SealedResolution Principal Value)
    (state : runtime.messageApplication.State)
    (owner : Principal) (serial node : Nat) (requires : List Nat) (value : Value)
    (hrule : runtime.program.rules[node]? =
      some { kind := .commit owner, requires })
    (hlookup : state.pool.lookup (owner, serial) =
      some ⟨(owner, serial), .commitment node (owner, node)⟩)
    (hstored : state.application.service.lookup (owner, node) = some value)
    (hrequires : requires.all state.application.visible.completed = true) :
    (runtime.messageApplication.includePending state (owner, serial)).application.visible.completed
      node = true := by
  cases hcompleted : state.application.visible.completed node with
  | true =>
      exact runtime.messageApplication.includePending_application_invariant
        (fun application => application.visible.completed node = true)
        (fun application message next hbefore hhandle =>
          handle_preserves_completed runtime runtime.handle runtime.handle_records
            application next message node hbefore hhandle)
        state (owner, serial) hcompleted
  | false =>
      have hvalid := validateMessage?_commitment runtime state.application owner serial node
        requires value hrule hstored hrequires hcompleted
      obtain ⟨next, hhandle, hnext⟩ :=
        handle_completed_of_valid runtime state.application _ _ node hvalid rfl
      rw [runtime.messageApplication.includePending_accept state (owner, serial) _ next
        hlookup hhandle]
      exact hnext

/-- Including a pending canonical opening completes its reveal node whenever
the source handle is publicly accepted, the private value agrees, and all
prerequisites are complete. -/
theorem includePending_opening_completed
    (runtime : SealedResolution Principal Value)
    (state : runtime.messageApplication.State)
    (owner : Principal) (serial node source : Nat) (requires : List Nat) (value : Value)
    (hrule : runtime.program.rules[node]? =
      some { kind := .reveal owner source, requires })
    (hlookup : state.pool.lookup (owner, serial) =
      some ⟨(owner, serial), .opening node (owner, source) value⟩)
    (haccepted : SealedProgram.accepted? state.application.visible.events source =
      some (owner, source))
    (hstored : state.application.service.lookup (owner, source) = some value)
    (hrequires : requires.all state.application.visible.completed = true) :
    (runtime.messageApplication.includePending state (owner, serial)).application.visible.completed
      node = true := by
  cases hcompleted : state.application.visible.completed node with
  | true =>
      exact runtime.messageApplication.includePending_application_invariant
        (fun application => application.visible.completed node = true)
        (fun application message next hbefore hhandle =>
          handle_preserves_completed runtime runtime.handle runtime.handle_records
            application next message node hbefore hhandle)
        state (owner, serial) hcompleted
  | false =>
      have hvalid := validateMessage?_opening runtime state.application owner serial node source
        requires value hrule haccepted hstored hrequires hcompleted
      obtain ⟨next, hhandle, hnext⟩ :=
        handle_completed_of_valid runtime state.application _ _ node hvalid rfl
      rw [runtime.messageApplication.includePending_accept state (owner, serial) _ next
        hlookup hhandle]
      exact hnext

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem tick_preserves_completed {Service : Type (max uPrincipal uValue)}
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value Service) (node : Nat)
    (hcompleted : state.visible.completed node = true) :
    (runtime.tick state).visible.completed node = true := by
  apply runtime.refresh_completed true _ node
  exact hcompleted

omit [DecidableEq Value] in
/-- Every supported native action preserves completion of an already completed
node, independently of which principal or environment policy selected it. -/
theorem step_completed
    {Service : Type (max uPrincipal uValue)}
    (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
        Option (ApplicationState Principal Value Service))
    (hrecords : runtime.HandlerRecords applyMessage)
    (state next : (runtime.host prepare applyMessage).State)
    (action : (runtime.host prepare applyMessage).Action) (node : Nat)
    (hcompleted : state.application.visible.completed node = true)
    (hnext : next ∈ ((runtime.host prepare applyMessage).step state action).support) :
    next.application.visible.completed node = true := by
  apply (runtime.host prepare applyMessage).step_application_invariant
    (fun application => application.visible.completed node = true) ?_ ?_ ?_
      state next action hcompleted hnext
  · intro application owner command hbefore
    simpa [host] using hbefore
  · intro application message after hbefore hhandle
    exact handle_preserves_completed runtime applyMessage hrecords application after message
      node hbefore hhandle
  · intro application command after hbefore hafter
    simp only [host, GameTheory.Math.Probability.FinDist.mem_support_pure]
      at hafter
    subst after
    exact tick_preserves_completed runtime application node hbefore

omit [DecidableEq Value] in
/-- Executing the optional action selected by one policy call preserves
completion in every supported native result. -/
theorem advance_completed
    {Service : Type (max uPrincipal uValue)}
    (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
        Option (ApplicationState Principal Value Service))
    (hrecords : runtime.HandlerRecords applyMessage)
    (execution : (runtime.host prepare applyMessage).PolicyExecution)
    (action : Option (runtime.host prepare applyMessage).Action)
    (advanced : (runtime.host prepare applyMessage).State ×
      List (runtime.host prepare applyMessage).Action)
    (node : Nat)
    (hcompleted : execution.native.application.visible.completed node = true)
    (hadvanced : advanced ∈
      ((runtime.host prepare applyMessage).advance execution action).support) :
    advanced.1.application.visible.completed node = true := by
  cases action with
  | none =>
      simp only [MessageApplication.advance,
        GameTheory.Math.Probability.FinDist.mem_support_pure] at hadvanced
      subst advanced
      exact hcompleted
  | some action =>
      simp only [MessageApplication.advance,
        GameTheory.Math.Probability.FinDist.support_bind, Set.mem_iUnion,
        GameTheory.Math.Probability.FinDist.mem_support_pure] at hadvanced
      obtain ⟨next, hnext, rfl⟩ := hadvanced
      exact runtime.step_completed prepare applyMessage hrecords execution.native next action
        node hcompleted hnext

omit [DecidableEq Value] in
/-- Arbitrary randomized player and environment policies cannot undo a node's
completion during a finite invocation schedule. -/
theorem runPolicies_completed
    {Service : Type (max uPrincipal uValue)}
    (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
        Option (ApplicationState Principal Value Service))
    (hrecords : runtime.HandlerRecords applyMessage)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (node : Nat)
    (hcompleted : execution.native.application.visible.completed node = true)
    (hnext : next ∈ ((runtime.host prepare applyMessage).runPolicies players environment
      schedule execution).support) :
    next.native.application.visible.completed node = true := by
  apply (runtime.host prepare applyMessage).runPolicies_application_invariant
    (fun application => application.visible.completed node = true) ?_ ?_ ?_
      players environment schedule execution next hcompleted hnext
  · intro application owner command hbefore
    simpa [host] using hbefore
  · intro application message after hbefore hhandle
    exact handle_preserves_completed runtime applyMessage hrecords application after message
      node hbefore hhandle
  · intro application command after hbefore hafter
    simp only [host, GameTheory.Math.Probability.FinDist.mem_support_pure]
      at hafter
    subst after
    exact tick_preserves_completed runtime application node hbefore

private theorem handle_preserves_all_completed
    (runtime : SealedResolution Principal Value)
    (state next : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (nodes : List Nat) (hcompleted : nodes.all state.visible.completed = true)
    (hhandle : runtime.handle state message = some next) :
    nodes.all next.visible.completed = true := by
  apply List.all_eq_true.mpr
  intro node hnode
  exact handle_preserves_completed runtime runtime.handle runtime.handle_records
    state next message node
    (List.all_eq_true.mp hcompleted node hnode) hhandle

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem tick_preserves_all_completed
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value) (nodes : List Nat)
    (hcompleted : nodes.all state.visible.completed = true) :
    nodes.all (runtime.tick state).visible.completed = true := by
  apply List.all_eq_true.mpr
  intro node hnode
  exact tick_preserves_completed runtime state node
    (List.all_eq_true.mp hcompleted node hnode)

private theorem handle_preserves_accepted
    (runtime : SealedResolution Principal Value)
    (state next : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (haccepted : .accepted node handle ∈ state.visible.events)
    (hhandle : runtime.handle state message = some next) :
    .accepted node handle ∈ next.visible.events := by
  unfold SealedResolution.handle at hhandle
  cases hvalid : runtime.validateMessage? state message with
  | none => simp [hvalid] at hhandle
  | some event =>
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some,
        Option.some.injEq] at hhandle
      subst next
      rw [runtime.refresh_accepted_iff]
      exact List.mem_append_left _ haccepted

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem tick_preserves_accepted
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value)
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (haccepted : .accepted node handle ∈ state.visible.events) :
    .accepted node handle ∈ (runtime.tick state).visible.events := by
  unfold SealedResolution.tick
  rw [runtime.refresh_accepted_iff]
  exact haccepted

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem accepted_done
    (events : List (SealedProgram.Event Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (haccepted : .accepted node handle ∈ events) :
    SealedProgram.done events node = true := by
  unfold SealedProgram.done
  rw [List.any_eq_true]
  exact ⟨.accepted node handle, haccepted, by simp [SealedProgram.Event.node]⟩

omit [DecidableEq Value] in
private theorem step_pendingReadyOrCompleted
    {Service : Type (max uPrincipal uValue)}
    (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
        Option (ApplicationState Principal Value Service))
    (hrecords : runtime.HandlerRecords applyMessage)
    (ready : ApplicationState Principal Value Service → Prop)
    (target : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat)
    (hprivate : ∀ application actor command, ready application →
      ready ((runtime.host prepare applyMessage).privateStep application actor command))
    (hhandler : ∀ application message next, ready application →
      applyMessage application message = some next → ready next)
    (htick : ∀ application, ready application → ready (runtime.tick application))
    (hresolve : ∀ state id, ready state.application →
      state.pool.lookup id = some target →
      ((runtime.host prepare applyMessage).includePending state id).application.visible.completed
        node = true)
    (state next : (runtime.host prepare applyMessage).State)
    (action : (runtime.host prepare applyMessage).Action)
    (hstate : state.application.visible.completed node = true ∨
      (target ∈ state.pool.pending ∧ ready state.application))
    (hnext : next ∈ ((runtime.host prepare applyMessage).step state action).support) :
    next.application.visible.completed node = true ∨
      (target ∈ next.pool.pending ∧ ready next.application) := by
  rcases hstate with hcompleted | ⟨hpending, hready⟩
  · exact Or.inl (runtime.step_completed prepare applyMessage hrecords state next action node
    hcompleted hnext)
  · cases action with
    | privateCommand actor command =>
        simp only [MessageApplication.step, GameTheory.Math.Probability.FinDist.mem_support_pure]
          at hnext
        subst next
        exact Or.inr ⟨hpending, hprivate state.application actor command hready⟩
    | submit actor payload =>
        simp only [MessageApplication.step, GameTheory.Math.Probability.FinDist.mem_support_pure]
          at hnext
        subst next
        refine Or.inr ⟨?_, hready⟩
        exact List.mem_append_left _ hpending
    | replay actor id =>
        simp only [MessageApplication.step, GameTheory.Math.Probability.FinDist.mem_support_pure]
          at hnext
        subst next
        refine Or.inr ⟨?_, hready⟩
        unfold MessagePool.replay
        split
        · exact List.mem_append_left _ hpending
        · exact hpending
    | deliver actor id =>
        simp only [MessageApplication.step, GameTheory.Math.Probability.FinDist.mem_support_pure]
          at hnext
        subst next
        refine Or.inr ⟨?_, hready⟩
        unfold MessagePool.deliver
        split <;> exact hpending
    | «include» id =>
        simp only [MessageApplication.step, GameTheory.Math.Probability.FinDist.mem_support_pure]
          at hnext
        subst next
        rcases MessagePool.pending_retained_or_selected state.pool id target hpending with
          hretained | hselected
        · right
          constructor
          · simpa only [MessageApplication.includePending_pool] using hretained
          · exact (runtime.host prepare applyMessage).includePending_application_invariant ready
              hhandler state id hready
        · exact Or.inl (hresolve state id hready hselected)
    | environment command =>
        simp only [MessageApplication.step, host,
          GameTheory.Math.Probability.FinDist.map_pure,
          GameTheory.Math.Probability.FinDist.mem_support_pure] at hnext
        subst next
        exact Or.inr ⟨hpending, htick state.application hready⟩

omit [DecidableEq Value] in
/-- A submitted packet remains pending until its site completes whenever its
readiness is stable and inclusion completes that site. The commitment service
and all intervening native actions are arbitrary. -/
theorem run_pending_or_completed
    {Service : Type (max uPrincipal uValue)}
    (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
        Option (ApplicationState Principal Value Service))
    (hrecords : runtime.HandlerRecords applyMessage)
    (ready : ApplicationState Principal Value Service → Prop)
    (target : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat)
    (hprivate : ∀ application actor command, ready application →
      ready ((runtime.host prepare applyMessage).privateStep application actor command))
    (hhandler : ∀ application message next, ready application →
      applyMessage application message = some next → ready next)
    (htick : ∀ application, ready application → ready (runtime.tick application))
    (hresolve : ∀ state id, ready state.application →
      state.pool.lookup id = some target →
      ((runtime.host prepare applyMessage).includePending state id).application.visible.completed
        node = true)
    (actions : List (runtime.host prepare applyMessage).Action)
    (state next : (runtime.host prepare applyMessage).State)
    (hstate : state.application.visible.completed node = true ∨
      (target ∈ state.pool.pending ∧ ready state.application))
    (hnext : next ∈ ((runtime.host prepare applyMessage).run actions state).support) :
    next.application.visible.completed node = true ∨
      (target ∈ next.pool.pending ∧ ready next.application) := by
  induction actions generalizing state with
  | nil =>
      simp only [MessageApplication.run_nil,
        GameTheory.Math.Probability.FinDist.mem_support_pure] at hnext
      subst next
      exact hstate
  | cons action rest ih =>
      simp only [MessageApplication.run_cons,
        GameTheory.Math.Probability.FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      exact ih middle
        (step_pendingReadyOrCompleted runtime prepare applyMessage hrecords ready target node
          hprivate hhandler htick
          hresolve state middle action hstate hmiddle) hnext

/-- A ready canonical commitment remains as that exact pending envelope under
arbitrary native policies unless its node completes. -/
theorem runPolicies_commitment_pendingOrCompleted
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (owner : Principal) (serial node : Nat) (requires : List Nat) (value : Value)
    (hrule : runtime.program.rules[node]? =
      some { kind := .commit owner, requires })
    (hpending : (⟨(owner, serial), .commitment node (owner, node)⟩ :
      Message Principal (SealedProgram.Payload Principal Value)) ∈
        execution.native.pool.pending)
    (hstored : execution.native.application.service.lookup (owner, node) = some value)
    (hrequires : requires.all execution.native.application.visible.completed = true)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) :
    next.native.application.visible.completed node = true ∨
      ((⟨(owner, serial), .commitment node (owner, node)⟩ :
          Message Principal (SealedProgram.Payload Principal Value)) ∈
          next.native.pool.pending ∧
        next.native.application.service.lookup (owner, node) = some value ∧
        requires.all next.native.application.visible.completed = true) := by
  let ready : ApplicationState Principal Value → Prop := fun state =>
    state.service.lookup (owner, node) = some value ∧
      requires.all state.visible.completed = true
  let target : Message Principal (SealedProgram.Payload Principal Value) :=
    ⟨(owner, serial), .commitment node (owner, node)⟩
  obtain ⟨actions, _, hrun⟩ := runtime.messageApplication.runPolicies_native_support
    players environment schedule execution next hnext
  have hresult := run_pending_or_completed runtime
    (fun (service : IdealCommitments Principal Nat Value) owner slot value =>
      (service.sealValue owner slot value).state) runtime.handle runtime.handle_records ready
        target node
    (fun state actor command hready => ⟨
      IdealCommitments.lookup_sealValue_of_eq_some state.service actor command.down.1
        command.down.2 (owner, node) value hready.1,
      hready.2⟩)
    (fun state message after hready hhandle => ⟨
      by
        rw [runtime.handle_service state after message hhandle]
        exact hready.1,
      handle_preserves_all_completed runtime state after message requires hready.2 hhandle⟩)
    (fun state hready => ⟨by simpa using hready.1,
      tick_preserves_all_completed runtime state requires hready.2⟩)
    (fun state id hready hlookup => by
      have hid : id = (owner, serial) := by
        unfold MessagePool.lookup at hlookup
        have hmatched := List.find?_some hlookup
        have htargetId : target.id = id := by
          simpa only [decide_eq_true_eq] using hmatched
        simpa [target] using htargetId.symm
      subst id
      exact includePending_commitment_completed runtime state owner serial node requires value
        hrule hlookup hready.1 hready.2)
    actions execution.native next.native (Or.inr ⟨hpending, hstored, hrequires⟩) hrun
  simpa [ready, target] using hresult

/-- A ready canonical opening likewise remains pending unless its node
completes.  The
event invariant recovers the exact canonical accepted-source query after every
intervening native command, without assuming unique event nodes. -/
theorem runPolicies_opening_pendingOrCompleted
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (owner : Principal) (serial node source : Nat)
    (requires sourceRequires : List Nat) (value : Value)
    (hrule : runtime.program.rules[node]? =
      some { kind := .reveal owner source, requires })
    (hsourceRule : runtime.program.rules[source]? =
      some { kind := .commit owner, requires := sourceRequires })
    (hinvariant : EventInvariant runtime execution.native.application)
    (hpending : (⟨(owner, serial), .opening node (owner, source) value⟩ :
      Message Principal (SealedProgram.Payload Principal Value)) ∈
        execution.native.pool.pending)
    (haccepted : SealedProgram.accepted?
      execution.native.application.visible.events source = some (owner, source))
    (hstored : execution.native.application.service.lookup (owner, source) = some value)
    (hrequires : requires.all execution.native.application.visible.completed = true)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) :
    next.native.application.visible.completed node = true ∨
      ((⟨(owner, serial), .opening node (owner, source) value⟩ :
          Message Principal (SealedProgram.Payload Principal Value)) ∈
          next.native.pool.pending ∧
        next.native.application.service.lookup (owner, source) = some value ∧
        requires.all next.native.application.visible.completed = true ∧
        SealedProgram.accepted? next.native.application.visible.events source =
          some (owner, source)) := by
  let ready : ApplicationState Principal Value → Prop := fun state =>
    EventInvariant runtime state ∧
      state.service.lookup (owner, source) = some value ∧
      requires.all state.visible.completed = true ∧
      SealedProgram.accepted? state.visible.events source = some (owner, source)
  let target : Message Principal (SealedProgram.Payload Principal Value) :=
    ⟨(owner, serial), .opening node (owner, source) value⟩
  obtain ⟨actions, _, hrun⟩ := runtime.messageApplication.runPolicies_native_support
    players environment schedule execution next hnext
  have hresult := run_pending_or_completed runtime
    (fun (service : IdealCommitments Principal Nat Value) owner slot value =>
      (service.sealValue owner slot value).state) runtime.handle runtime.handle_records ready
        target node
    (fun state actor command hready => ⟨
      hready.1.register actor command.down.1 command.down.2,
      IdealCommitments.lookup_sealValue_of_eq_some state.service actor command.down.1
        command.down.2 (owner, source) value hready.2.1,
      hready.2.2.1, hready.2.2.2⟩)
    (fun state message after hready hhandle => by
      have hinvariantAfter := hready.1.handle message hhandle
      have hacceptedBefore :=
        SealedProgram.accepted_mem_of_accepted?_eq_some hready.2.2.2
      have hacceptedAfter := handle_preserves_accepted runtime state after message source
        (owner, source) hacceptedBefore hhandle
      have hdone := accepted_done after.visible.events source (owner, source) hacceptedAfter
      exact ⟨hinvariantAfter,
        by
          rw [runtime.handle_service state after message hhandle]
          exact hready.2.1,
        handle_preserves_all_completed runtime state after message requires hready.2.2.1 hhandle,
        hinvariantAfter.accepted?_eq_some_of_done_commit source owner sourceRequires
          hsourceRule hdone⟩)
    (fun state hready => by
      have hinvariantAfter := hready.1.tick
      have hacceptedBefore :=
        SealedProgram.accepted_mem_of_accepted?_eq_some hready.2.2.2
      have hacceptedAfter := tick_preserves_accepted runtime state source
        (owner, source) hacceptedBefore
      have hdone := accepted_done (runtime.tick state).visible.events source
        (owner, source) hacceptedAfter
      exact ⟨hinvariantAfter, by simpa using hready.2.1,
        tick_preserves_all_completed runtime state requires hready.2.2.1,
        hinvariantAfter.accepted?_eq_some_of_done_commit source owner sourceRequires
          hsourceRule hdone⟩)
    (fun state id hready hlookup => by
      have hid : id = (owner, serial) := by
        unfold MessagePool.lookup at hlookup
        have hmatched := List.find?_some hlookup
        have htargetId : target.id = id := by
          simpa only [decide_eq_true_eq] using hmatched
        simpa [target] using htargetId.symm
      subst id
      exact includePending_opening_completed runtime state owner serial node source requires value
        hrule hlookup hready.2.2.2 hready.2.1 hready.2.2.1)
    actions execution.native next.native
      (Or.inr ⟨hpending, hinvariant, hstored, hrequires, haccepted⟩) hrun
  rcases hresult with hcompleted | ⟨hpending, hinvariant, hstored, hrequires, haccepted⟩
  · exact Or.inl hcompleted
  · exact Or.inr ⟨hpending, hstored, hrequires, haccepted⟩

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_opening_pendingOrCompleted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_opening_pendingOrCompleted
