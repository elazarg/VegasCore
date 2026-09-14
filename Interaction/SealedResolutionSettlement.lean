/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionDeadline

/-! # Public timeout settlement values

Ordinary openings are backed by an accepted source commitment and cannot later
be reclassified as timeouts.  Openings introduced by resolution carry the
runtime's designated null value.  These facts remain valid under arbitrary
native player traffic, wire scheduling, and clock advancement.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

@[simp] theorem PublicState.opened_stamp_iff
    (state : PublicState Principal Value) (stamped node : Nat) (value : Value) :
    .opened node value ∈ (state.stamp stamped).events ↔
      .opened node value ∈ state.events := by
  unfold PublicState.stamp
  split <;> rfl

theorem expire_opened_iff_of_ne
    (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (visited node : Nat)
    (kind : SealedRuleKind Principal) (value : Value)
    (hvalue : value ≠ runtime.nullValue) :
    .opened node value ∈ (runtime.expire state visited kind).events ↔
      .opened node value ∈ state.events := by
  cases kind <;> simp [SealedResolution.expire, hvalue]

theorem visit_opened_iff_of_ne
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (visited node : Nat) (value : Value)
    (hvalue : value ≠ runtime.nullValue) :
    .opened node value ∈ (runtime.visit resolveExpired state visited).events ↔
      .opened node value ∈ state.events := by
  unfold SealedResolution.visit
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · dsimp only
        split
        · simp [hvalue]
        · split
          · exact (runtime.expire_opened_iff_of_ne (state.stamp visited)
              visited node _ value hvalue).trans (state.opened_stamp_iff visited node value)
          · exact state.opened_stamp_iff visited node value
      · dsimp only
        split
        · exact (runtime.expire_opened_iff_of_ne (state.stamp visited)
            visited node _ value hvalue).trans (state.opened_stamp_iff visited node value)
        · exact state.opened_stamp_iff visited node value

theorem refresh_opened_iff_of_ne
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node : Nat) (value : Value)
    (hvalue : value ≠ runtime.nullValue) :
    .opened node value ∈ (runtime.refresh resolveExpired state).events ↔
      .opened node value ∈ state.events := by
  unfold SealedResolution.refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => rfl
  | cons visited rest ih =>
      simp only [List.foldl_cons]
      exact (ih (runtime.visit resolveExpired state visited)).trans
        (runtime.visit_opened_iff_of_ne resolveExpired state visited node value hvalue)

private theorem SealedProgram.validated_payload_node
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (service : IdealCommitments Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (event : SealedProgram.Event Principal Value)
    (hvalid : program.validateMessage? service events message = some event) :
    message.payload.node? = some event.node := by
  cases message with
  | mk id payload =>
      cases payload with
      | cleartext | malformed => cases hvalid
      | commitment node handle =>
          simp only [SealedProgram.validateMessage?] at hvalid
          split at hvalid <;> try contradiction
          split at hvalid <;> try contradiction
          split at hvalid <;> cases hvalid
          rfl
      | opening node handle claimed =>
          simp only [SealedProgram.validateMessage?] at hvalid
          split at hvalid <;> try contradiction
          split at hvalid <;> try contradiction
          split at hvalid <;> try contradiction
          cases hvalid
          rfl

private theorem SealedProgram.validateMessage?_opened_source_accepted
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (service : IdealCommitments Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (value : Value)
    (hvalid : program.validateMessage? service events message = some (.opened node value)) :
    ∃ owner source requires,
      program.rules[node]? = some { kind := .reveal owner source, requires } ∧
        SealedProgram.accepted? events source = some (owner, source) := by
  cases message with
  | mk id payload =>
      cases payload with
      | cleartext | malformed => cases hvalid
      | commitment index handle =>
          simp only [SealedProgram.validateMessage?] at hvalid
          split at hvalid <;> try contradiction
          split at hvalid <;> try contradiction
          split at hvalid <;> cases hvalid
      | opening index handle claimed =>
          simp only [SealedProgram.validateMessage?] at hvalid
          split at hvalid <;> try contradiction
          rename_i rule hrule
          split at hvalid <;> try contradiction
          rename_i owner source hkind
          split at hvalid <;> try contradiction
          rename_i hchecks
          cases hvalid
          refine ⟨owner, source, rule.requires, ?_, ?_⟩
          · cases rule
            simp_all
          · simpa [hchecks.2.1] using hchecks.2.2.2.2.1

private theorem validateMessage?_event_payload_node
    [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (event : SealedProgram.Event Principal Value)
    (hvalid : runtime.validateMessage? state message = some event) :
    message.payload.node? = some event.node := by
  unfold SealedResolution.validateMessage? at hvalid
  split at hvalid
  · contradiction
  · exact SealedProgram.validated_payload_node _ _ _ _ _ hvalid

private theorem validateMessage?_opened_source_accepted
    [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (value : Value)
    (hvalid : runtime.validateMessage? state message = some (.opened node value)) :
    ∃ owner source requires,
      runtime.program.rules[node]? =
          some { kind := .reveal owner source, requires } ∧
        SealedProgram.accepted? state.visible.events source = some (owner, source) := by
  unfold SealedResolution.validateMessage? at hvalid
  split at hvalid
  · contradiction
  · obtain ⟨owner, source, requires, hrule, haccepted⟩ :=
      SealedProgram.validateMessage?_opened_source_accepted
        (runtime.program.discharge state.visible.timeouts) state.service
        state.visible.events message node value hvalid
    simp only [SealedProgram.discharge, List.getElem?_map] at hrule
    cases horiginal : runtime.program.rules[node]? with
    | none => simp [horiginal] at hrule
    | some rule =>
        simp only [horiginal, Option.map_some, Option.some.injEq] at hrule
        refine ⟨owner, source, rule.requires, ?_, haccepted⟩
        have hshape :
            rule = ({ kind := .reveal owner source, requires := rule.requires } :
              SealedRule Principal) := by
          cases rule
          simp_all [SealedRule.discharge]
        exact congrArg some hshape

private theorem validateMessage?_event_not_timeout
    [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (event : SealedProgram.Event Principal Value)
    (hvalid : runtime.validateMessage? state message = some event) :
    event.node ∉ state.visible.timeouts := by
  intro htimeout
  have hpayload := runtime.validateMessage?_event_payload_node state message event hvalid
  have hnone := runtime.validateMessage?_expired state message event.node hpayload htimeout
  rw [hvalid] at hnone
  contradiction

/-- Public settlement safety is independent of the private commitment service.
Accepted sites cannot time out; non-null openings name an accepted source site.
The selected candidate need not be a canonical source-slot handle. -/
structure SettlementInvariant (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) : Prop where
  accepted_not_timeout : ∀ node handle,
    .accepted node handle ∈ state.events → node ∉ state.timeouts
  nonNullOpened : ∀ node owner source requires value,
    runtime.program.rules[node]? =
        some { kind := .reveal owner source, requires } →
      .opened node value ∈ state.events → value ≠ runtime.nullValue →
      node ∉ state.timeouts ∧ ∃ handle, .accepted source handle ∈ state.events

namespace SettlementInvariant

variable {runtime : SealedResolution Principal Value}
variable {state : PublicState Principal Value}

private theorem completed_of_event
    (visible : PublicState Principal Value)
    (event : SealedProgram.Event Principal Value) (hevent : event ∈ visible.events) :
    visible.completed event.node = true := by
  unfold PublicState.completed SealedProgram.done
  simp only [Bool.or_eq_true]
  left
  rw [List.any_eq_true]
  exact ⟨event, hevent, by simp⟩

/-- A timeout at either endpoint of a reveal forces every recorded opening at
that reveal node to be the runtime null value. -/
theorem opened_eq_null_of_timeout
    (invariant : SettlementInvariant runtime state)
    (node : Nat) (owner : Principal) (source : Nat) (requires : List Nat)
    (value : Value)
    (hrule : runtime.program.rules[node]? =
      some { kind := .reveal owner source, requires })
    (hopened : .opened node value ∈ state.events)
    (htimeout : node ∈ state.timeouts ∨ source ∈ state.timeouts) :
    value = runtime.nullValue := by
  by_contra hvalue
  obtain ⟨hnode, handle, haccepted⟩ :=
    invariant.nonNullOpened node owner source requires value hrule hopened hvalue
  rcases htimeout with htimeout | htimeout
  · exact hnode htimeout
  · exact invariant.accepted_not_timeout source handle haccepted htimeout

theorem initial (runtime : SealedResolution Principal Value) :
    SettlementInvariant runtime runtime.initial.visible := by
  have hevents : runtime.initial.visible.events = [] := by
    unfold SealedResolution.initial
    exact runtime.refresh_false_events {} rfl
  constructor
  · intro node handle haccepted
    rw [hevents] at haccepted
    simp at haccepted
  · intro node owner source requires value hrule hopened hvalue
    rw [hevents] at hopened
    simp at hopened

theorem clock (invariant : SettlementInvariant runtime state) :
    SettlementInvariant runtime { state with clock := state.clock + 1 } :=
  ⟨invariant.accepted_not_timeout, invariant.nonNullOpened⟩

theorem refresh (invariant : SettlementInvariant runtime state)
    (resolveExpired : Bool) :
    SettlementInvariant runtime (runtime.refresh resolveExpired state) := by
  constructor
  · intro node handle haccepted
    have hprior := (runtime.refresh_accepted_iff resolveExpired state node handle).mp haccepted
    exact refresh_no_timeout_of_completed runtime resolveExpired state node
      (completed_of_event state (.accepted node handle) hprior)
      (invariant.accepted_not_timeout node handle hprior)
  · intro node owner source requires value hrule hopened hvalue
    have hprior := (runtime.refresh_opened_iff_of_ne resolveExpired state
      node value hvalue).mp hopened
    obtain ⟨hnode, handle, haccepted⟩ :=
      invariant.nonNullOpened node owner source requires value hrule hprior hvalue
    exact ⟨refresh_no_timeout_of_completed runtime resolveExpired state node
        (completed_of_event state (.opened node value) hprior) hnode,
      handle, (runtime.refresh_accepted_iff resolveExpired state source handle).mpr haccepted⟩

/-- Public event admission is the only host-specific obligation needed to
preserve timeout settlement. The clock and source-settlement proofs use this
same contract for both registered and candidate commitment services. -/
theorem record (invariant : SettlementInvariant runtime state)
    (event : SealedProgram.Event Principal Value)
    (hnotTimeout : event.node ∉ state.timeouts)
    (hsource : ∀ node value, event = .opened node value →
      ∃ owner source requires handle,
        runtime.program.rules[node]? = some { kind := .reveal owner source, requires } ∧
          .accepted source handle ∈ state.events) :
    SettlementInvariant runtime { state with events := state.events ++ [event] } := by
  constructor
  · intro node handle haccepted
    simp only [List.mem_append, List.mem_singleton] at haccepted
    rcases haccepted with hprior | hnew
    · exact invariant.accepted_not_timeout node handle hprior
    · subst event
      exact hnotTimeout
  · intro node owner source requires value hrule hopened hvalue
    simp only [List.mem_append, List.mem_singleton] at hopened
    rcases hopened with hprior | hnew
    · obtain ⟨hnode, handle, haccepted⟩ :=
        invariant.nonNullOpened node owner source requires value hrule hprior hvalue
      exact ⟨hnode, handle, List.mem_append_left [event] haccepted⟩
    · subst event
      obtain ⟨eventOwner, eventSource, eventRequires, handle, heventRule, haccepted⟩ :=
        hsource node value rfl
      have hkinds := congrArg (fun found => found.map SealedRule.kind)
        (heventRule.symm.trans hrule)
      simp only [Option.map_some, Option.some.injEq, SealedRuleKind.reveal.injEq] at hkinds
      obtain ⟨rfl, rfl⟩ := hkinds
      exact ⟨hnotTimeout, handle, List.mem_append_left [.opened node value] haccepted⟩

variable [DecidableEq Principal] [DecidableEq Value]

theorem handle
    {before next : ApplicationState Principal Value}
    (invariant : SettlementInvariant runtime before.visible)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.handle before message = some next) :
    SettlementInvariant runtime next.visible := by
  unfold SealedResolution.handle at hnext
  cases hvalid : runtime.validateMessage? before message with
  | none => simp [hvalid] at hnext
  | some event =>
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
      subst next
      apply SettlementInvariant.refresh (resolveExpired := false)
      apply invariant.record event
        (runtime.validateMessage?_event_not_timeout before message event hvalid)
      intro node value hevent
      subst event
      obtain ⟨owner, source, requires, hrule, haccepted⟩ :=
        runtime.validateMessage?_opened_source_accepted before message node value hvalid
      exact ⟨owner, source, requires, (owner, source), hrule,
        SealedProgram.accepted_mem_of_accepted?_eq_some haccepted⟩

end SettlementInvariant

variable [DecidableEq Principal] [DecidableEq Value]

/-- Settlement validity survives arbitrary randomized player and environment
policies, including any number of resolving clock commands. -/
theorem runPolicies_settlementInvariant
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : SettlementInvariant runtime execution.native.application.visible)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) :
    SettlementInvariant runtime next.native.application.visible := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (fun state => SettlementInvariant runtime state.visible) ?_ ?_ ?_
      players environment schedule execution next hinitial hnext
  · intro state owner command hstate
    exact hstate
  · intro state message after hstate hafter
    exact hstate.handle message hafter
  · intro state command after hstate hafter
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    exact hstate.clock.refresh true

/-- Settlement validity survives bounded rounds from any valid entry state. -/
theorem runRounds_settlementInvariant
    (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : SettlementInvariant runtime execution.native.application.visible)
    (hnext : next ∈ (runtime.roundDriver.runRounds principals serviceSlots players environment
      count execution).support) :
    SettlementInvariant runtime next.native.application.visible := by
  induction count generalizing execution with
  | zero =>
      simp only [MessageApplication.RoundDriver.runRounds, FinDist.mem_support_pure] at hnext
      subst next
      exact hinitial
  | succ count ih =>
      simp only [MessageApplication.RoundDriver.runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hinitial
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        simp only [MessageApplication.RoundDriver.round, FinDist.support_bind,
          Set.mem_iUnion] at hmiddle
        obtain ⟨serviced, hserviced, hmiddle⟩ := hmiddle
        have hservicedInvariant := runtime.runPolicies_settlementInvariant players
          (runtime.messageApplication.wireEnvironment environment) _ execution serviced
          hinitial hserviced
        have hmiddleNative := runtime.clockStep_native
          (fun (service : IdealCommitments Principal Nat Value) owner slot value =>
            (service.sealValue owner slot value).state) runtime.handle serviced middle hmiddle
        apply ih middle ?_ hnext
        rw [hmiddleNative]
        exact hservicedInvariant.clock.refresh true

/-- Every bounded round outcome from the canonical empty runtime satisfies the
settlement invariant, without restrictions on players or wire scheduling. -/
theorem runRounds_initial_settlementInvariant
    (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.roundDriver.runRounds principals serviceSlots players environment count
      (MessageApplication.PolicyExecution.initial runtime.messageApplication
        (MessageApplication.State.initial runtime.messageApplication runtime.initial))).support) :
    SettlementInvariant runtime next.native.application.visible := by
  exact runtime.runRounds_settlementInvariant principals serviceSlots players environment count
    _ next (SettlementInvariant.initial runtime) hnext

/-- In every canonical bounded-round execution, an opening whose reveal or
source commitment timed out carries exactly the runtime null value. -/
theorem runRounds_opened_eq_null_of_timeout
    (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.roundDriver.runRounds principals serviceSlots players environment count
      (MessageApplication.PolicyExecution.initial runtime.messageApplication
        (MessageApplication.State.initial runtime.messageApplication runtime.initial))).support)
    (node : Nat) (owner : Principal) (source : Nat) (requires : List Nat)
    (value : Value)
    (hrule : runtime.program.rules[node]? =
      some { kind := .reveal owner source, requires })
    (hopened : .opened node value ∈ next.native.application.visible.events)
    (htimeout : node ∈ next.native.application.visible.timeouts ∨
      source ∈ next.native.application.visible.timeouts) :
    value = runtime.nullValue := by
  exact (runtime.runRounds_initial_settlementInvariant principals serviceSlots players
    environment count next hnext).opened_eq_null_of_timeout node owner source requires
      value hrule hopened htimeout

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runRounds_opened_eq_null_of_timeout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runRounds_opened_eq_null_of_timeout
