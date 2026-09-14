/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionRounds
import Interaction.SealedResolutionPolicy
import Interaction.SealedProgramLaws

/-! # Accepted commitments through deadline resolution

Acceptance events always name the canonical owner-scoped commitment slot, and
that slot remains occupied. This invariant is independent of timeout status:
resolution may append opening events, but it neither creates acceptance events
nor overwrites private registrations.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- Every public acceptance is backed by its canonical occupied private slot.
The rule witness deliberately records only a separate kind equality, so
discharging timeout-completed prerequisites does not change the invariant. -/
structure AcceptedBinding (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value) : Prop where
  accepted : ∀ node handle, .accepted node handle ∈ state.visible.events →
    ∃ owner value rule,
      runtime.program.rules[node]? = some rule ∧ rule.kind = .commit owner ∧
        handle = (owner, node) ∧ state.service.lookup handle = some value

@[simp] theorem PublicState.accepted_stamp_iff
    (state : PublicState Principal Value) (stamped node : Nat)
    (handle : CommitmentHandle Principal Nat) :
    SealedProgram.Event.accepted node handle ∈ (state.stamp stamped).events ↔
      SealedProgram.Event.accepted node handle ∈ state.events := by
  unfold PublicState.stamp
  split <;> rfl

theorem expire_accepted_iff (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (visited node : Nat)
    (kind : SealedRuleKind Principal) (handle : CommitmentHandle Principal Nat) :
    SealedProgram.Event.accepted node handle ∈ (runtime.expire state visited kind).events ↔
      SealedProgram.Event.accepted node handle ∈ state.events := by
  unfold expire
  split <;> simp

theorem visit_accepted_iff (runtime : SealedResolution Principal Value)
    (resolveExpired : Bool) (state : PublicState Principal Value)
    (visited node : Nat) (handle : CommitmentHandle Principal Nat) :
    SealedProgram.Event.accepted node handle ∈
        (runtime.visit resolveExpired state visited).events ↔
      SealedProgram.Event.accepted node handle ∈ state.events := by
  unfold SealedResolution.visit
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · dsimp only
        split
        · simp
        · split
          · exact (runtime.expire_accepted_iff (state.stamp visited) visited node _ handle).trans
              (state.accepted_stamp_iff visited node handle)
          · exact state.accepted_stamp_iff visited node handle
      · dsimp only
        split
        · exact (runtime.expire_accepted_iff (state.stamp visited) visited node _ handle).trans
            (state.accepted_stamp_iff visited node handle)
        · exact state.accepted_stamp_iff visited node handle

theorem refresh_accepted_iff (runtime : SealedResolution Principal Value)
    (resolveExpired : Bool) (state : PublicState Principal Value)
    (node : Nat) (handle : CommitmentHandle Principal Nat) :
    SealedProgram.Event.accepted node handle ∈
        (runtime.refresh resolveExpired state).events ↔
      SealedProgram.Event.accepted node handle ∈ state.events := by
  unfold refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => rfl
  | cons visited rest ih =>
      simp only [List.foldl_cons]
      exact (ih (runtime.visit resolveExpired state visited)).trans
        (runtime.visit_accepted_iff resolveExpired state visited node handle)

variable [DecidableEq Principal] [DecidableEq Value]

/-- Resolution validation preserves the original rule kind even though its
prerequisite list is discharged. -/
theorem validateMessage?_accepted_sound
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (hvalid : runtime.validateMessage? state message = some (.accepted node handle)) :
    ∃ owner value rule,
      runtime.program.rules[node]? = some rule ∧ rule.kind = .commit owner ∧
        handle = (owner, node) ∧ state.service.lookup handle = some value := by
  unfold SealedResolution.validateMessage? at hvalid
  split at hvalid
  · contradiction
  · obtain ⟨owner, requires, value, hrule, hhandle, hlookup⟩ :=
      SealedProgram.validateMessage?_accepted_sound
        (runtime.program.discharge state.visible.timeouts) state.service state.visible.events
        message node handle hvalid
    simp only [SealedProgram.discharge, List.getElem?_map] at hrule
    cases horiginal : runtime.program.rules[node]? with
    | none => simp [horiginal] at hrule
    | some rule =>
        simp only [horiginal, Option.map_some, Option.some.injEq] at hrule
        refine ⟨owner, value, rule, rfl, ?_, hhandle, hlookup⟩
        have hkind := congrArg SealedRule.kind hrule
        simpa [SealedRule.discharge] using hkind

namespace AcceptedBinding

variable {runtime : SealedResolution Principal Value}
variable {state next : ApplicationState Principal Value}

omit [DecidableEq Principal] [DecidableEq Value] in
theorem initial : AcceptedBinding runtime runtime.initial := by
  constructor
  intro node handle haccepted
  have hnone : SealedProgram.Event.accepted node handle ∈
      ({} : PublicState Principal Value).events := by
    rw [← runtime.refresh_accepted_iff false {} node handle]
    exact haccepted
  simp at hnone

omit [DecidableEq Value] in
theorem register (invariant : AcceptedBinding runtime state)
    (owner : Principal) (slot : Nat) (value : Value) :
    AcceptedBinding runtime
      { state with service := (state.service.sealValue owner slot value).state } := by
  constructor
  intro node handle haccepted
  obtain ⟨eventOwner, stored, rule, hrule, hkind, hhandle, hlookup⟩ :=
    invariant.accepted node handle haccepted
  exact ⟨eventOwner, stored, rule, hrule, hkind, hhandle,
    IdealCommitments.lookup_sealValue_of_eq_some state.service owner slot value
      handle stored hlookup⟩

omit [DecidableEq Principal] [DecidableEq Value] in
theorem clock (invariant : AcceptedBinding runtime state) :
    AcceptedBinding runtime
      { state with visible := { state.visible with clock := state.visible.clock + 1 } } := by
  constructor
  intro node handle haccepted
  exact invariant.accepted node handle haccepted

omit [DecidableEq Principal] [DecidableEq Value] in
theorem refresh (invariant : AcceptedBinding runtime state) (resolveExpired : Bool) :
    AcceptedBinding runtime
      { state with visible := runtime.refresh resolveExpired state.visible } := by
  constructor
  intro node handle haccepted
  exact invariant.accepted node handle
    ((runtime.refresh_accepted_iff resolveExpired state.visible node handle).mp haccepted)

theorem handle (invariant : AcceptedBinding runtime state)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.handle state message = some next) : AcceptedBinding runtime next := by
  unfold SealedResolution.handle at hnext
  cases hvalid : runtime.validateMessage? state message with
  | none => simp [hvalid] at hnext
  | some event =>
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
      subst next
      let recorded : ApplicationState Principal Value :=
        { state with visible := { state.visible with events := state.visible.events ++ [event] } }
      have hrecorded : AcceptedBinding runtime recorded := by
        constructor
        intro node handle haccepted
        simp only [recorded, List.mem_append, List.mem_singleton] at haccepted
        rcases haccepted with hprior | rfl
        · exact invariant.accepted node handle hprior
        · exact runtime.validateMessage?_accepted_sound state message node handle hvalid
      exact hrecorded.refresh false

omit [DecidableEq Principal] [DecidableEq Value] in
theorem tick (invariant : AcceptedBinding runtime state) :
    AcceptedBinding runtime (runtime.tick state) := by
  unfold SealedResolution.tick
  exact invariant.clock.refresh true

end AcceptedBinding

/-- Canonical accepted-handle occupancy survives arbitrary randomized player
and environment policies, including any number of resolving clock commands. -/
theorem runPolicies_acceptedBinding
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : AcceptedBinding runtime execution.native.application)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) : AcceptedBinding runtime next.native.application := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (AcceptedBinding runtime) ?_ ?_ ?_ players environment schedule execution next hinitial hnext
  · intro state owner command hstate
    exact hstate.register owner command.down.1 command.down.2
  · intro state message after hstate hafter
    exact hstate.handle message hafter
  · intro state command after hstate hafter
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    exact hstate.tick

/-- An accepted handle is also present in its owner's command-history cache.
This is the player-visible form used by the resolving policy. -/
theorem AcceptedBinding.cachedValue_of_accepted
    (runtime : SealedResolution Principal Value)
    (execution : runtime.messageApplication.PolicyExecution)
    (invariant : AcceptedBinding runtime execution.native.application)
    (memory : RegistrationMemory runtime execution)
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (haccepted : .accepted node handle ∈ execution.native.application.visible.events) :
    ∃ owner value rule,
      runtime.program.rules[node]? = some rule ∧ rule.kind = .commit owner ∧
        handle = (owner, node) ∧
        (runtime.program.registrationEncoding node).cachedValue runtime.messageApplication
          (execution.principalHistory owner) = some value := by
  obtain ⟨owner, value, rule, hrule, hkind, hhandle, hlookup⟩ :=
    invariant.accepted node handle haccepted
  subst handle
  exact ⟨owner, value, rule, hrule, hkind, rfl,
    (memory owner node).symm.trans hlookup⟩

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_acceptedBinding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_acceptedBinding
