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

/-- Accepted commitments remain disjoint from timeouts.  A non-null opening
retains both an unexpired reveal node and its canonical accepted source. -/
structure SettlementInvariant (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value) : Prop where
  accepted_not_timeout : ∀ node handle,
    .accepted node handle ∈ state.visible.events → node ∉ state.visible.timeouts
  nonNullOpened : ∀ node owner source requires value,
    runtime.program.rules[node]? =
        some { kind := .reveal owner source, requires } →
      .opened node value ∈ state.visible.events → value ≠ runtime.nullValue →
      node ∉ state.visible.timeouts ∧
        .accepted source (owner, source) ∈ state.visible.events

namespace SettlementInvariant

variable {runtime : SealedResolution Principal Value}
variable {state next : ApplicationState Principal Value}

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
    (hopened : .opened node value ∈ state.visible.events)
    (htimeout : node ∈ state.visible.timeouts ∨ source ∈ state.visible.timeouts) :
    value = runtime.nullValue := by
  by_contra hvalue
  obtain ⟨hnode, haccepted⟩ :=
    invariant.nonNullOpened node owner source requires value hrule hopened hvalue
  rcases htimeout with htimeout | htimeout
  · exact hnode htimeout
  · exact invariant.accepted_not_timeout source (owner, source) haccepted htimeout

theorem initial (runtime : SealedResolution Principal Value) :
    SettlementInvariant runtime runtime.initial := by
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

theorem register [DecidableEq Principal]
    (invariant : SettlementInvariant runtime state)
    (owner : Principal) (slot : Nat) (value : Value) :
    SettlementInvariant runtime
      { state with service := (state.service.sealValue owner slot value).state } := by
  exact ⟨invariant.accepted_not_timeout, invariant.nonNullOpened⟩

theorem clock (invariant : SettlementInvariant runtime state) :
    SettlementInvariant runtime
      { state with visible := { state.visible with clock := state.visible.clock + 1 } } := by
  exact ⟨invariant.accepted_not_timeout, invariant.nonNullOpened⟩

theorem refresh (invariant : SettlementInvariant runtime state)
    (resolveExpired : Bool) :
    SettlementInvariant runtime
      { state with visible := runtime.refresh resolveExpired state.visible } := by
  constructor
  · intro node handle haccepted
    have hprior := (runtime.refresh_accepted_iff resolveExpired state.visible
      node handle).mp haccepted
    exact refresh_no_timeout_of_completed runtime resolveExpired state.visible node
      (completed_of_event state.visible (.accepted node handle) hprior)
      (invariant.accepted_not_timeout node handle hprior)
  · intro node owner source requires value hrule hopened hvalue
    have hprior := (runtime.refresh_opened_iff_of_ne resolveExpired state.visible
      node value hvalue).mp hopened
    obtain ⟨hnode, haccepted⟩ :=
      invariant.nonNullOpened node owner source requires value hrule hprior hvalue
    exact ⟨refresh_no_timeout_of_completed runtime resolveExpired state.visible node
        (completed_of_event state.visible (.opened node value) hprior) hnode,
      (runtime.refresh_accepted_iff resolveExpired state.visible source
        (owner, source)).mpr haccepted⟩

theorem tick (invariant : SettlementInvariant runtime state) :
    SettlementInvariant runtime (runtime.tick state) := by
  unfold SealedResolution.tick
  exact invariant.clock.refresh true

variable [DecidableEq Principal] [DecidableEq Value]

private theorem record
    (invariant : SettlementInvariant runtime state)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (event : SealedProgram.Event Principal Value)
    (hvalid : runtime.validateMessage? state message = some event) :
    SettlementInvariant runtime
      { state with visible := { state.visible with
          events := state.visible.events ++ [event] } } := by
  constructor
  · intro node handle haccepted
    simp only [List.mem_append, List.mem_singleton] at haccepted
    rcases haccepted with hprior | hnew
    · exact invariant.accepted_not_timeout node handle hprior
    · subst event
      exact runtime.validateMessage?_event_not_timeout state message
        (.accepted node handle) hvalid
  · intro node owner source requires value hrule hopened hvalue
    simp only [List.mem_append, List.mem_singleton] at hopened
    rcases hopened with hprior | hnew
    · obtain ⟨hnode, haccepted⟩ :=
        invariant.nonNullOpened node owner source requires value hrule hprior hvalue
      exact ⟨hnode, List.mem_append_left [event] haccepted⟩
    · subst event
      obtain ⟨eventOwner, eventSource, eventRequires, heventRule, haccepted⟩ :=
        runtime.validateMessage?_opened_source_accepted state message node value hvalid
      have hrules :
          ({ kind := .reveal eventOwner eventSource, requires := eventRequires } :
              SealedRule Principal) =
            { kind := .reveal owner source, requires } :=
        Option.some.inj (heventRule.symm.trans hrule)
      have hkinds := congrArg SealedRule.kind hrules
      simp only [SealedRuleKind.reveal.injEq] at hkinds
      obtain ⟨rfl, rfl⟩ := hkinds
      exact ⟨runtime.validateMessage?_event_not_timeout state message
          (.opened node value) hvalid,
        List.mem_append_left [.opened node value]
          (SealedProgram.accepted_mem_of_accepted?_eq_some haccepted)⟩

theorem handle
    (invariant : SettlementInvariant runtime state)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.handle state message = some next) :
    SettlementInvariant runtime next := by
  unfold SealedResolution.handle at hnext
  cases hvalid : runtime.validateMessage? state message with
  | none => simp [hvalid] at hnext
  | some event =>
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
      subst next
      exact (invariant.record message event hvalid).refresh false

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
    (hinitial : SettlementInvariant runtime execution.native.application)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) :
    SettlementInvariant runtime next.native.application := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (SettlementInvariant runtime) ?_ ?_ ?_
      players environment schedule execution next hinitial hnext
  · intro state owner command hstate
    exact hstate.register owner command.down.1 command.down.2
  · intro state message after hstate hafter
    exact hstate.handle message hafter
  · intro state command after hstate hafter
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    exact hstate.tick

/-- Settlement validity survives bounded rounds from any valid entry state. -/
theorem runRounds_settlementInvariant
    (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : SettlementInvariant runtime execution.native.application)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment
      count execution).support) :
    SettlementInvariant runtime next.native.application := by
  induction count generalizing execution with
  | zero =>
      simp only [runRounds, FinDist.mem_support_pure] at hnext
      subst next
      exact hinitial
  | succ count ih =>
      simp only [runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hinitial
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        simp only [round, FinDist.support_bind, Set.mem_iUnion] at hmiddle
        obtain ⟨serviced, hserviced, hmiddle⟩ := hmiddle
        have hservicedInvariant := runtime.runPolicies_settlementInvariant players
          (runtime.messageApplication.wireEnvironment environment) _ execution serviced
          hinitial hserviced
        have hmiddleNative := runtime.clockStep_native serviced middle hmiddle
        apply ih middle ?_ hnext
        rw [hmiddleNative]
        exact hservicedInvariant.tick

/-- Every bounded round outcome from the canonical empty runtime satisfies the
settlement invariant, without restrictions on players or wire scheduling. -/
theorem runRounds_initial_settlementInvariant
    (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment count
      (MessageApplication.PolicyExecution.initial runtime.messageApplication
        (MessageApplication.State.initial runtime.messageApplication runtime.initial))).support) :
    SettlementInvariant runtime next.native.application := by
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
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment count
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
