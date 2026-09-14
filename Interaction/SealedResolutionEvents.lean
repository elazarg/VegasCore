/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionAccepted

/-! # Public event invariants through deadline resolution

Every opening event belongs to a reveal rule.  Moreover, timeout completion of
a reveal is accompanied by a public opening.  Together with accepted-handle
binding, these facts characterize enough of the public log to read completed
nodes after arbitrary native execution.

The invariant intentionally does not relate a timeout opening's value to the
private commitment service.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- Public events have rule provenance, and every timed-out reveal has an
opening witness. No candidate identity or private-value claim is required. -/
structure PublicEventInvariant (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) : Prop where
  opened : ∀ node value, .opened node value ∈ state.events →
    ∃ owner source requires,
      runtime.program.rules[node]? = some { kind := .reveal owner source, requires }
  timeoutOpened : ∀ node owner source requires,
    node ∈ state.timeouts →
    runtime.program.rules[node]? = some { kind := .reveal owner source, requires } →
    ∃ value, .opened node value ∈ state.events
  accepted : ∀ node handle, .accepted node handle ∈ state.events →
    ∃ owner rule, runtime.program.rules[node]? = some rule ∧ rule.kind = .commit owner

/-- At a commitment rule, public completion means acceptance, not an opening
event or a timeout. Timeouts are recorded separately from this predicate. -/
theorem PublicEventInvariant.done_eq_accepted_isSome
    (runtime : SealedResolution Principal Value)
    {state : PublicState Principal Value} (invariant : PublicEventInvariant runtime state)
    (node : Nat) (owner : Principal) (requires : List Nat)
    (hrule : runtime.program.rules[node]? = some ⟨.commit owner, requires⟩) :
    SealedProgram.done state.events node = (SealedProgram.accepted? state.events node).isSome := by
  cases hread : SealedProgram.accepted? state.events node with
  | some handle =>
      exact SealedProgram.done_of_accepted _ node handle
        (SealedProgram.accepted_mem_of_accepted?_eq_some hread)
  | none =>
      cases hdone : SealedProgram.done state.events node with
      | false => rfl
      | true =>
          obtain ⟨event, hmem, hnode⟩ := List.any_eq_true.mp hdone
          have heq : event.node = node := by simpa using hnode
          cases event with
          | accepted index handle =>
              change index = node at heq
              subst index
              have hnone := List.findSome?_eq_none_iff.mp hread (.accepted node handle) hmem
              simp at hnone
          | opened index value =>
              change index = node at heq
              subst index
              obtain ⟨eventOwner, source, eventRequires, hopen⟩ := invariant.opened node value hmem
              rw [hrule] at hopen
              cases hopen

namespace PublicEventInvariant

variable {runtime : SealedResolution Principal Value}
variable {state : PublicState Principal Value}

theorem stamp (invariant : PublicEventInvariant runtime state) (node : Nat) :
    PublicEventInvariant runtime (state.stamp node) := by
  unfold PublicState.stamp
  split
  · exact invariant
  · exact ⟨invariant.opened, invariant.timeoutOpened, invariant.accepted⟩

theorem clock (invariant : PublicEventInvariant runtime state) :
    PublicEventInvariant runtime { state with clock := state.clock + 1 } :=
  ⟨invariant.opened, invariant.timeoutOpened, invariant.accepted⟩

theorem appendOpened (invariant : PublicEventInvariant runtime state)
    (node : Nat) (value : Value) (owner : Principal) (source : Nat) (requires : List Nat)
    (hrule : runtime.program.rules[node]? =
      some { kind := .reveal owner source, requires }) :
    PublicEventInvariant runtime
      { state with events := state.events ++ [.opened node value] } := by
  constructor
  · intro target openedValue hopened
    simp only [List.mem_append, List.mem_singleton] at hopened
    rcases hopened with hprior | heq
    · exact invariant.opened target openedValue hprior
    · cases heq
      exact ⟨owner, source, requires, hrule⟩
  · intro target eventOwner eventSource eventRequires htimeout htarget
    obtain ⟨openedValue, hopened⟩ :=
      invariant.timeoutOpened target eventOwner eventSource eventRequires htimeout htarget
    exact ⟨openedValue, List.mem_append_left _ hopened⟩
  · intro target handle haccepted
    simp only [List.mem_append, List.mem_singleton] at haccepted
    rcases haccepted with hprior | himpossible
    · exact invariant.accepted target handle hprior
    · contradiction

theorem appendAccepted (invariant : PublicEventInvariant runtime state)
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (owner : Principal) (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule) (hkind : rule.kind = .commit owner) :
    PublicEventInvariant runtime
      { state with events := state.events ++ [.accepted node handle] } := by
  constructor
  · intro target value hopened
    simp only [List.mem_append, List.mem_singleton] at hopened
    rcases hopened with hprior | himpossible
    · exact invariant.opened target value hprior
    · contradiction
  · intro target owner source requires htimeout hrule
    obtain ⟨value, hopened⟩ :=
      invariant.timeoutOpened target owner source requires htimeout hrule
    exact ⟨value, List.mem_append_left _ hopened⟩
  · intro target targetHandle haccepted
    simp only [List.mem_append, List.mem_singleton] at haccepted
    rcases haccepted with hprior | heq
    · exact invariant.accepted target targetHandle hprior
    · cases heq
      exact ⟨owner, rule, hrule, hkind⟩

theorem expire (invariant : PublicEventInvariant runtime state)
    (node : Nat) (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule) :
    PublicEventInvariant runtime (runtime.expire state node rule.kind) := by
  cases hkind : rule.kind with
  | disabled => simpa [SealedResolution.expire, hkind] using invariant
  | commit owner =>
      constructor
      · simpa [SealedResolution.expire, hkind] using invariant.opened
      · intro target eventOwner source requires htimeout htarget
        simp only [SealedResolution.expire, List.mem_append,
          List.mem_singleton] at htimeout
        rcases htimeout with hprior | rfl
        · exact invariant.timeoutOpened target eventOwner source requires hprior htarget
        · rw [hrule] at htarget
          have hkinds := congrArg (fun found => found.map SealedRule.kind) htarget
          simp [hkind] at hkinds
      · exact invariant.accepted
  | reveal owner source =>
      have happended := invariant.appendOpened node runtime.nullValue owner source rule.requires
        (by
          have hshape :
              rule = ({ kind := .reveal owner source, requires := rule.requires } :
                SealedRule Principal) := by
            cases rule
            simp_all
          rwa [← hshape])
      constructor
      · simpa [SealedResolution.expire, hkind] using happended.opened
      · intro target eventOwner eventSource requires htimeout htarget
        simp only [SealedResolution.expire, List.mem_append,
          List.mem_singleton] at htimeout
        rcases htimeout with hprior | rfl
        · exact happended.timeoutOpened target eventOwner eventSource requires hprior htarget
        · exact ⟨runtime.nullValue,
            List.mem_append_right state.events
              (show SealedProgram.Event.opened target runtime.nullValue ∈
                [SealedProgram.Event.opened target runtime.nullValue] by simp)⟩
      · exact happended.accepted

theorem visit (invariant : PublicEventInvariant runtime state)
    (resolveExpired : Bool) (node : Nat) :
    PublicEventInvariant runtime (runtime.visit resolveExpired state node) := by
  cases hrule : runtime.program.rules[node]? with
  | none => simp [SealedResolution.visit, hrule, invariant]
  | some rule =>
      cases hkind : rule.kind with
      | disabled => simpa [SealedResolution.visit, hrule, hkind] using invariant
      | commit owner =>
          simp only [SealedResolution.visit, hrule]
          split
          · exact invariant
          · simp only [hkind]
            split
            · simpa only [hkind] using (invariant.stamp node).expire node rule hrule
            · exact invariant.stamp node
      | reveal owner source =>
          simp only [SealedResolution.visit, hrule]
          split
          · exact invariant
          · simp only [hkind]
            split
            · exact (invariant.stamp node).appendOpened node runtime.nullValue owner source
                rule.requires (by
                  have hshape :
                      rule = ({ kind := .reveal owner source, requires := rule.requires } :
                        SealedRule Principal) := by
                    cases rule
                    simp_all
                  rwa [← hshape])
            · split
              · simpa only [hkind] using (invariant.stamp node).expire node rule hrule
              · exact invariant.stamp node

theorem refresh (invariant : PublicEventInvariant runtime state)
    (resolveExpired : Bool) :
    PublicEventInvariant runtime (runtime.refresh resolveExpired state) := by
  unfold SealedResolution.refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => exact invariant
  | cons node rest ih =>
      exact ih (invariant.visit resolveExpired node)

theorem initial (runtime : SealedResolution Principal Value) :
    PublicEventInvariant runtime runtime.initial.visible := by
  apply (show PublicEventInvariant runtime ({} : PublicState Principal Value) by
    constructor <;> simp).refresh false

/-- A completed reveal has a public opening. The proof needs only public rule
provenance, not successful registration or an openable accepted commitment. -/
theorem opened_of_completed_reveal (invariant : PublicEventInvariant runtime state)
    (node : Nat) (owner : Principal) (source : Nat) (requires : List Nat)
    (hrule : runtime.program.rules[node]? =
      some { kind := .reveal owner source, requires })
    (hcompleted : state.completed node = true) :
    ∃ value, .opened node value ∈ state.events := by
  unfold PublicState.completed at hcompleted
  simp only [Bool.or_eq_true] at hcompleted
  rcases hcompleted with hdone | htimeout
  · unfold SealedProgram.done at hdone
    rw [List.any_eq_true] at hdone
    obtain ⟨event, hevent, hnode⟩ := hdone
    have heq : event.node = node := by simpa using hnode
    cases event with
    | accepted eventNode handle =>
        simp only [SealedProgram.Event.node] at heq
        subst eventNode
        obtain ⟨eventOwner, rule, heventRule, hkind⟩ := invariant.accepted node handle hevent
        rw [hrule] at heventRule
        have hkinds := congrArg SealedRule.kind (Option.some.inj heventRule)
        simp [hkind] at hkinds
    | opened eventNode value =>
        simp only [SealedProgram.Event.node] at heq
        subst eventNode
        exact ⟨value, hevent⟩
  · exact invariant.timeoutOpened node owner source requires
      (by simpa using htimeout) hrule

end PublicEventInvariant

variable [DecidableEq Principal] [DecidableEq Value]

/-- Resolution validation preserves an opening target's original reveal kind
while timeout-completed prerequisites are discharged. -/
theorem validateMessage?_opened_sound
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (value : Value)
    (hvalid : runtime.validateMessage? state message = some (.opened node value)) :
    ∃ owner source requires,
      runtime.program.rules[node]? = some { kind := .reveal owner source, requires } := by
  unfold SealedResolution.validateMessage? at hvalid
  split at hvalid
  · contradiction
  · obtain ⟨owner, source, requires, hrule, _⟩ :=
      SealedProgram.validateMessage?_opened_sound
        (runtime.program.discharge state.visible.timeouts) state.service state.visible.events
        message node value hvalid
    simp only [SealedProgram.discharge, List.getElem?_map] at hrule
    cases horiginal : runtime.program.rules[node]? with
    | none => simp [horiginal] at hrule
    | some rule =>
        simp only [horiginal, Option.map_some, Option.some.injEq] at hrule
        refine ⟨owner, source, rule.requires, ?_⟩
        have hkind := congrArg SealedRule.kind hrule
        have hshape :
            rule = ({ kind := .reveal owner source, requires := rule.requires } :
              SealedRule Principal) := by
          cases rule
          simp_all [SealedRule.discharge]
        exact congrArg some hshape

/-- The full native event invariant combines private accepted-handle binding
with public opening provenance and timeout coverage. -/
structure EventInvariant (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value) : Prop where
  acceptedBinding : AcceptedBinding runtime state
  publicEvents : PublicEventInvariant runtime state.visible

namespace EventInvariant

variable {runtime : SealedResolution Principal Value}
variable {state next : ApplicationState Principal Value}

omit [DecidableEq Principal] [DecidableEq Value] in
theorem initial : EventInvariant runtime runtime.initial :=
  ⟨AcceptedBinding.initial, PublicEventInvariant.initial runtime⟩

omit [DecidableEq Value] in
theorem register (invariant : EventInvariant runtime state)
    (owner : Principal) (slot : Nat) (value : Value) :
    EventInvariant runtime
      { state with service := (state.service.sealValue owner slot value).state } :=
  ⟨invariant.acceptedBinding.register owner slot value, invariant.publicEvents⟩

omit [DecidableEq Principal] [DecidableEq Value] in
theorem clock (invariant : EventInvariant runtime state) :
    EventInvariant runtime
      { state with visible := { state.visible with clock := state.visible.clock + 1 } } :=
  ⟨invariant.acceptedBinding.clock, invariant.publicEvents.clock⟩

omit [DecidableEq Principal] [DecidableEq Value] in
theorem refresh (invariant : EventInvariant runtime state) (resolveExpired : Bool) :
    EventInvariant runtime
      { state with visible := runtime.refresh resolveExpired state.visible } :=
  ⟨invariant.acceptedBinding.refresh resolveExpired,
    invariant.publicEvents.refresh resolveExpired⟩

theorem handle (invariant : EventInvariant runtime state)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.handle state message = some next) : EventInvariant runtime next := by
  unfold SealedResolution.handle at hnext
  cases hvalid : runtime.validateMessage? state message with
  | none => simp [hvalid] at hnext
  | some event =>
      have haccepted := invariant.acceptedBinding.handle message hnext
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
      subst next
      let recorded : ApplicationState Principal Value :=
        { state with visible := { state.visible with events := state.visible.events ++ [event] } }
      have hpublic : PublicEventInvariant runtime recorded.visible := by
        cases event with
        | accepted node handle =>
            obtain ⟨owner, value, rule, hrule, hkind, _⟩ :=
              runtime.validateMessage?_accepted_sound state message node handle hvalid
            exact invariant.publicEvents.appendAccepted node handle owner rule hrule hkind
        | opened node value =>
            obtain ⟨owner, source, requires, hrule⟩ :=
              runtime.validateMessage?_opened_sound state message node value hvalid
            exact invariant.publicEvents.appendOpened node value owner source requires hrule
      constructor
      · exact haccepted
      · exact hpublic.refresh false

omit [DecidableEq Principal] [DecidableEq Value] in
theorem tick (invariant : EventInvariant runtime state) :
    EventInvariant runtime (runtime.tick state) := by
  unfold SealedResolution.tick
  exact invariant.clock.refresh true

omit [DecidableEq Principal] [DecidableEq Value] in
/-- Ordinary event-log completion of a commit node is its canonical acceptance
event.  Timeout completion is deliberately excluded from this statement. -/
theorem accepted_of_done_commit (invariant : EventInvariant runtime state)
    (node : Nat) (owner : Principal) (requires : List Nat)
    (hrule : runtime.program.rules[node]? = some { kind := .commit owner, requires })
    (hdone : SealedProgram.done state.visible.events node = true) :
    .accepted node (owner, node) ∈ state.visible.events := by
  unfold SealedProgram.done at hdone
  rw [List.any_eq_true] at hdone
  obtain ⟨event, hevent, hnode⟩ := hdone
  have heq : event.node = node := by simpa using hnode
  cases event with
  | accepted eventNode handle =>
      simp only [SealedProgram.Event.node] at heq
      subst eventNode
      obtain ⟨eventOwner, value, rule, heventRule, hkind, hhandle, hlookup⟩ :=
        invariant.acceptedBinding.accepted node handle hevent
      rw [hrule] at heventRule
      have hrules := Option.some.inj heventRule
      have hkinds := congrArg SealedRule.kind hrules
      simp only [hkind, SealedRuleKind.commit.injEq] at hkinds
      subst eventOwner
      subst handle
      exact hevent
  | opened eventNode value =>
      simp only [SealedProgram.Event.node] at heq
      subst eventNode
      obtain ⟨eventOwner, source, eventRequires, heventRule⟩ :=
        invariant.publicEvents.opened node value hevent
      rw [hrule] at heventRule
      simp at heventRule

end EventInvariant

omit [DecidableEq Principal] [DecidableEq Value] in
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

/-- The native event invariant survives arbitrary randomized player and
environment policies, including resolving clock commands and timeouts. -/
theorem runPolicies_eventInvariant
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : EventInvariant runtime execution.native.application)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) : EventInvariant runtime next.native.application := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (EventInvariant runtime) ?_ ?_ ?_ players environment schedule execution next hinitial hnext
  · intro state owner command hstate
    exact hstate.register owner command.down.1 command.down.2
  · intro state message after hstate hafter
    exact hstate.handle message hafter
  · intro state command after hstate hafter
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    exact hstate.tick

/-- The public event invariant survives every supported bounded round run from
an arbitrary invariant entry state.  In particular, the canonical run uses
`EventInvariant.initial` as its entry witness. -/
theorem runRounds_eventInvariant
    (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (hinvariant : EventInvariant runtime execution.native.application)
    (hnext : next ∈ (runtime.roundDriver.runRounds principals serviceSlots players environment
      count execution).support) : EventInvariant runtime next.native.application := by
  induction count generalizing execution with
  | zero =>
      simp only [MessageApplication.RoundDriver.runRounds, FinDist.mem_support_pure] at hnext
      subst next
      exact hinvariant
  | succ count ih =>
      simp only [MessageApplication.RoundDriver.runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hinvariant
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        simp only [MessageApplication.RoundDriver.round, FinDist.support_bind,
          Set.mem_iUnion] at hmiddle
        obtain ⟨serviced, hserviced, hmiddle⟩ := hmiddle
        have hservicedInvariant := runtime.runPolicies_eventInvariant players
          (runtime.messageApplication.wireEnvironment environment) _ execution serviced
          hinvariant hserviced
        have hmiddleNative := runtime.clockStep_native
          (fun (service : IdealCommitments Principal Nat Value) owner slot value =>
            (service.sealValue owner slot value).state) runtime.handle serviced middle hmiddle
        apply ih middle ?_ hnext
        rw [hmiddleNative]
        exact hservicedInvariant.tick

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_eventInvariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_eventInvariant

/-- info: 'Interaction.SealedResolution.runRounds_eventInvariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runRounds_eventInvariant
