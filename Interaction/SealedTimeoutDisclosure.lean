/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedTimeoutPolicyLaws
import Interaction.SealedProgramLaws
import GameTheoryExtensions.Math.SelectiveStopping

/-! # Bound values at timed disclosure checkpoints

After the monitored value is locked, every accepted opening has that value,
even under arbitrary player traffic and adaptive delivery, inclusion, and
clock policies. A resolved checkpoint therefore either discloses the bound
value or expires. Expiration remains an explicit runtime outcome; the source
compiler must supply its meaning and the service must establish resolution.
-/

namespace Interaction.SealedProgram

variable {Principal Value : Type*} [DecidableEq Principal] [DecidableEq Value]

/-- The first accepted value for an opening node, read from public events. -/
def openedValue? (node : Nat) : List (Event Principal Value) → Option Value
  | [] => none
  | .opened other value :: rest => if other = node then some value else openedValue? node rest
  | .accepted _ _ :: rest => openedValue? node rest

omit [DecidableEq Principal] [DecidableEq Value] in
theorem openedValue?_eq_of_unique (node : Nat) (events : List (Event Principal Value))
    (value : Value) (hmem : .opened node value ∈ events)
    (hunique : ∀ claimed, .opened node claimed ∈ events → claimed = value) :
    openedValue? node events = some value := by
  induction events with
  | nil => simp at hmem
  | cons event rest ih =>
      have hrest : ∀ claimed, .opened node claimed ∈ rest → claimed = value :=
        fun claimed h => hunique claimed (List.mem_cons_of_mem event h)
      cases event with
      | accepted other handle =>
          exact ih (by simpa using hmem) hrest
      | opened other claimed =>
          by_cases hnode : other = node
          · subst other
            have heq := hunique claimed (List.mem_cons_self ..)
            simp [openedValue?, heq]
          · apply (if_neg hnode).trans
            apply ih _ hrest
            simp only [List.mem_cons, Event.opened.injEq] at hmem
            rcases hmem with ⟨heq, _⟩ | hmem
            · exact (hnode heq.symm).elim
            · exact hmem

end Interaction.SealedProgram

namespace Interaction

/-- The public result of a monitored disclosure. Expiration carries no
invented application value, and an unresolved run remains distinguishable. -/
inductive DisclosureResult (Value : Type*) where
  | unresolved
  | opened (value : Value)
  | expired
  deriving DecidableEq

end Interaction

namespace Interaction.SealedTimeout

open GameTheory.Math.Probability

variable {Principal Value : Type*} [DecidableEq Principal] [DecidableEq Value]

/-- Read the disposition and accepted opening from the actual application.
This projection never reads the private commitment service. -/
def disclosureResult (timed : SealedTimeout Principal)
    (application : Application Principal Value) : DisclosureResult Value :=
  match application.resolution with
  | .pending => .unresolved
  | .expired => .expired
  | .completed =>
      match SealedProgram.openedValue? timed.openingNode application.events with
      | none => .unresolved
      | some value => .opened value

/-- A monitored opening has a fixed stored value, and its public events and
completion marker agree with that value. This invariant makes no progress claim. -/
structure LockedOpening (timed : SealedTimeout Principal) (owner : Principal)
    (source : Nat) (value : Value) (application : Application Principal Value) : Prop where
  lookup : application.service.lookup (owner, source) = some value
  opened : ∀ claimed, .opened timed.openingNode claimed ∈ application.events → claimed = value
  completed : application.resolution = .completed →
    .opened timed.openingNode value ∈ application.events

namespace LockedOpening

variable {timed : SealedTimeout Principal} {owner : Principal} {source : Nat} {value : Value}

omit [DecidableEq Principal] [DecidableEq Value] in
theorem disclosureResult_eq {application : Application Principal Value}
    (invariant : LockedOpening timed owner source value application)
    (hresolved : application.resolution ≠ .pending) :
    timed.disclosureResult application =
      if application.resolution = .expired then .expired else .opened value := by
  cases h : application.resolution with
  | pending => exact (hresolved h).elim
  | expired => simp [disclosureResult, h]
  | completed =>
      simp [disclosureResult, h, SealedProgram.openedValue?_eq_of_unique
        timed.openingNode application.events value (invariant.completed h) invariant.opened]

omit [DecidableEq Principal] [DecidableEq Value] in
/-- A pending checkpoint with no prior opening is locked as soon as its
ideal-service slot has been populated. -/
theorem of_pending {application : Application Principal Value}
    (hlookup : application.service.lookup (owner, source) = some value)
    (hpending : application.resolution = .pending)
    (hnotOpened : ∀ claimed, .opened timed.openingNode claimed ∉ application.events) :
    LockedOpening timed owner source value application :=
  ⟨hlookup, fun claimed h => (hnotOpened claimed h).elim,
    fun h => (by cases hpending.symm.trans h)⟩

private theorem handle {application next : Application Principal Value}
    (invariant : LockedOpening timed owner source value application)
    (requires : List Nat)
    (hrule : timed.program.rules[timed.openingNode]? = some ⟨.reveal owner source, requires⟩)
    (now : Nat) (message : Message Principal (Payload Principal Value))
    (hhandle : timed.handle now application message = some next) :
    LockedOpening timed owner source value next := by
  cases hpayload : message.payload with
  | expire =>
      obtain ⟨hservice, hevents, hresolution⟩ :=
        handle_expire_updates_only_resolution timed now application next message hpayload hhandle
      refine ⟨by simpa [hservice] using invariant.lookup,
        fun claimed h => invariant.opened claimed (hevents ▸ h), ?_⟩
      intro h
      cases hresolution.symm.trans h
  | protocol payload =>
      simp only [SealedTimeout.handle, hpayload] at hhandle
      split at hhandle <;> try contradiction
      cases hvalid : timed.program.validateMessage? application.service application.events
          ⟨message.id, payload⟩ with
      | none => simp [hvalid] at hhandle
      | some event =>
          rw [hvalid] at hhandle
          cases hhandle
          have hnew : ∀ claimed, event = .opened timed.openingNode claimed → claimed = value := by
            intro claimed hevent
            rw [hevent] at hvalid
            obtain ⟨eventOwner, eventSource, eventRequires, heventRule, hlookup⟩ :=
              SealedProgram.validateMessage?_opened_sound timed.program application.service
                application.events ⟨message.id, payload⟩ timed.openingNode claimed hvalid
            rw [hrule] at heventRule
            have heq := SealedRuleKind.reveal.inj (congrArg SealedRule.kind
              (Option.some.inj heventRule))
            obtain ⟨rfl, rfl⟩ := heq
            exact Option.some.inj (hlookup.symm.trans invariant.lookup)
          refine ⟨invariant.lookup, ?_, ?_⟩
          · intro claimed h
            simp only [List.mem_append, List.mem_singleton] at h
            rcases h with h | h
            · exact invariant.opened claimed h
            · exact hnew claimed h.symm
          · intro h
            cases event with
            | accepted node handle =>
                exact List.mem_append_left _ (invariant.completed h)
            | opened node claimed =>
                by_cases hnode : node = timed.openingNode
                · subst node
                  have heq := hnew claimed rfl
                  subst claimed
                  exact List.mem_append_right _ (List.mem_singleton_self _)
                · exact List.mem_append_left _ (invariant.completed (by simpa [hnode] using h))

theorem step {state : State Principal Value}
    (invariant : LockedOpening timed owner source value state.application)
    (requires : List Nat)
    (hrule : timed.program.rules[timed.openingNode]? = some ⟨.reveal owner source, requires⟩)
    (action : Action Principal Value) :
    LockedOpening timed owner source value (timed.step state action).application := by
  cases action with
  | register registeredOwner slot registeredValue =>
      exact ⟨step_lookup_of_eq_some timed state (.register registeredOwner slot registeredValue)
        (owner, source) value invariant.lookup, invariant.opened, invariant.completed⟩
  | submit | replay | deliver => exact invariant
  | advance clock =>
      simp only [SealedTimeout.step]
      split <;> exact invariant
  | «include» id =>
      cases hlookup : state.pool.lookup id with
      | none => simpa [SealedTimeout.step, includePending, MessagePool.includeApplication,
          MessagePool.includePending, hlookup, MessagePool.Result.invalid] using invariant
      | some message =>
          cases hhandle : timed.handle state.clock state.application message with
          | none => simpa [SealedTimeout.step, includePending, MessagePool.includeApplication,
              MessagePool.includePending, hlookup, hhandle] using invariant
          | some next =>
              simpa [SealedTimeout.step, includePending, MessagePool.includeApplication,
                MessagePool.includePending, hlookup, hhandle] using
                invariant.handle requires hrule state.clock message hhandle

theorem run {state : State Principal Value}
    (invariant : LockedOpening timed owner source value state.application)
    (requires : List Nat)
    (hrule : timed.program.rules[timed.openingNode]? = some ⟨.reveal owner source, requires⟩)
    (actions : List (Action Principal Value)) :
    LockedOpening timed owner source value (timed.run state actions).application := by
  induction actions generalizing state with
  | nil => exact invariant
  | cons action rest ih => exact ih (invariant.step requires hrule action)

/-- Arbitrary randomized policies retain the monitored value despite pending
payload observations, private registrations, malformed traffic, and expiration. -/
theorem runPolicies {initial : State Principal Value}
    (invariant : LockedOpening timed owner source value initial.application)
    (requires : List Nat)
    (hrule : timed.program.rules[timed.openingNode]? = some ⟨.reveal owner source, requires⟩)
    (players : Principal → (timed.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (timed.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution : (timed.messageApplication (Value := Value)).PolicyExecution)
    (hmem : execution ∈ ((timed.messageApplication (Value := Value)).runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial _ (timed.toSharedState initial))).support) :
    LockedOpening timed owner source value execution.native.application.application := by
  rw [runPolicies_native_eq_run_trace timed players environment schedule initial execution hmem]
  exact invariant.run requires hrule (execution.nativeTrace.map (fromSharedAction timed))

end LockedOpening

/-- Any resolved policy continuation of a locked checkpoint is an arbitrary
mixture of opening the fixed value and expiration. The mixture is extracted
from actual execution; player and environment policies are unrestricted. -/
theorem resolved_policy_disclosure_law
    (timed : SealedTimeout Principal) (initial : State Principal Value)
    (owner : Principal) (source : Nat) (value : Value) (requires : List Nat)
    (hrule : timed.program.rules[timed.openingNode]? = some ⟨.reveal owner source, requires⟩)
    (invariant : LockedOpening timed owner source value initial.application)
    (players : Principal → (timed.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (timed.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (hresolved : ∀ execution ∈ ((timed.messageApplication (Value := Value)).runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial _ (timed.toSharedState initial))).support,
      execution.native.application.application.resolution ≠ .pending) :
    let law := (timed.messageApplication (Value := Value)).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial _ (timed.toSharedState initial))
    law.map (fun execution => timed.disclosureResult execution.native.application.application) =
      (law.map (fun execution => decide
        (execution.native.application.application.resolution = .expired))).map
        (fun expires => if expires then DisclosureResult.expired else .opened value) := by
  dsimp only
  rw [FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro execution hmem
  have hlocked := invariant.runPolicies requires hrule players environment schedule execution hmem
  simpa only [Function.comp_def, decide_eq_true_eq] using
    hlocked.disclosureResult_eq (hresolved execution hmem)

/-- Once a bound value has been chosen, observing pending messages cannot
improve this disclosure payoff through selective expiration when opening is
better by the stated margin. Resolution is a separate service premise.

This compares disclosure outcomes only. Full program continuations must first
be related to these two branches before applying the inequality to source utility. -/
theorem resolved_policy_utility_bound
    (timed : SealedTimeout Principal) (initial : State Principal Value)
    (owner : Principal) (source : Nat) (value : Value) (requires : List Nat)
    (hrule : timed.program.rules[timed.openingNode]? = some ⟨.reveal owner source, requires⟩)
    (invariant : LockedOpening timed owner source value initial.application)
    (players : Principal → (timed.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (timed.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (hresolved : ∀ execution ∈ ((timed.messageApplication (Value := Value)).runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial _ (timed.toSharedState initial))).support,
      execution.native.application.application.resolution ≠ .pending)
    (utility : DisclosureResult Value → ℝ) (margin : ℝ)
    (hmargin : utility .expired + margin ≤ utility (.opened value)) :
    let law := (timed.messageApplication (Value := Value)).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial _ (timed.toSharedState initial))
    (law.map (fun execution => timed.disclosureResult
        execution.native.application.application)).expect utility +
        margin * (law.map (fun execution => decide
          (execution.native.application.application.resolution = .expired))).prob true ≤
      utility (.opened value) := by
  dsimp only
  rw [resolved_policy_disclosure_law timed initial owner source value requires hrule
    invariant players environment schedule hresolved]
  let law := (timed.messageApplication (Value := Value)).runPolicies players environment schedule
    (MessageApplication.PolicyExecution.initial _ (timed.toSharedState initial))
  let stops := law.map (fun execution => decide
    (execution.native.application.application.resolution = .expired))
  have hbound := FinDist.selective_stopping_bound (FinDist.pure ()) (fun _ => stops)
    (fun _ => FinDist.pure (DisclosureResult.expired : DisclosureResult Value))
    (fun _ => FinDist.pure (DisclosureResult.opened value)) utility margin
    (fun _ _ _ => by simpa using hmargin)
  simpa only [stops, law, FinDist.pure_bind, FinDist.expect_pure, FinDist.map_eq_bind,
    apply_ite FinDist.pure] using hbound

end Interaction.SealedTimeout

/-- info: 'Interaction.SealedTimeout.LockedOpening.runPolicies' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedTimeout.LockedOpening.runPolicies

/-- info: 'Interaction.SealedTimeout.resolved_policy_utility_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedTimeout.resolved_policy_utility_bound
