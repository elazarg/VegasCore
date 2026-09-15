/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedOpeningValidation
import Interaction.SealedCandidatePublicPersistence

/-! # Historical validity of public openings

An opening admitted by the guarded candidate handler records the exact public
event prefix against which its validator succeeded. Openings created by clock
resolution instead carry the runtime null value and have either their own
reveal node or their source commitment recorded as timed out. The invariant is
preserved by the shared policy runner and round driver under arbitrary player
and wire policies.

The prefix witness is intentionally part of the proposition: a validator may
depend on public events that occur before admission and need not remain true in
a later event log.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability MessageApplication

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- Public event nodes are unique, and every opening is either certified
against its exact pre-admission event prefix or is a null opening explained by
direct or propagated timeout. -/
structure OpeningHistoryInvariant
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (state : PublicState Principal Value) : Prop where
  nodes_unique : (state.events.map SealedProgram.Event.node).Nodup
  opening : ∀ node value, .opened node value ∈ state.events →
    (∃ beforeEvents suffix,
      state.events = beforeEvents ++ .opened node value :: suffix ∧
        validator node beforeEvents value = true) ∨
    (∃ owner source requires,
      runtime.program.rules[node]? =
          some { kind := .reveal owner source, requires } ∧
        value = runtime.nullValue ∧
        (node ∈ state.timeouts ∨ source ∈ state.timeouts))

namespace OpeningHistoryInvariant

variable {runtime : SealedResolution Principal Value}
variable {validator : PublicOpeningValidator Principal Value}
variable {state : PublicState Principal Value}

private theorem prior_after_append
    (invariant : OpeningHistoryInvariant runtime validator state)
    (event : SealedProgram.Event Principal Value)
    (node : Nat) (value : Value) (hopened : .opened node value ∈ state.events) :
    (∃ beforeEvents suffix,
      (state.events ++ [event]) = beforeEvents ++ .opened node value :: suffix ∧
        validator node beforeEvents value = true) ∨
    (∃ owner source requires,
      runtime.program.rules[node]? =
          some { kind := .reveal owner source, requires } ∧
        value = runtime.nullValue ∧
        (node ∈ state.timeouts ∨ source ∈ state.timeouts)) := by
  rcases invariant.opening node value hopened with
    ⟨beforeEvents, suffix, hevents, hvalid⟩ | hdefault
  · left
    refine ⟨beforeEvents, suffix ++ [event], ?_, hvalid⟩
    simp [hevents, List.append_assoc]
  · exact Or.inr hdefault

theorem appendAccepted
    (invariant : OpeningHistoryInvariant runtime validator state)
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (hnotDone : SealedProgram.done state.events node = false) :
    OpeningHistoryInvariant runtime validator
      { state with events := state.events ++ [.accepted node handle] } := by
  constructor
  · exact SealedProgram.eventNodes_nodup_append invariant.nodes_unique hnotDone
  intro target value hopened
  simp only [List.mem_append, List.mem_singleton] at hopened
  rcases hopened with hprior | himpossible
  · exact invariant.prior_after_append (.accepted node handle) target value hprior
  · contradiction

theorem appendValidated
    (invariant : OpeningHistoryInvariant runtime validator state)
    (node : Nat) (value : Value)
    (hvalid : validator node state.events value = true)
    (hnotDone : SealedProgram.done state.events node = false) :
    OpeningHistoryInvariant runtime validator
      { state with events := state.events ++ [.opened node value] } := by
  constructor
  · exact SealedProgram.eventNodes_nodup_append invariant.nodes_unique hnotDone
  intro target opened hopened
  simp only [List.mem_append, List.mem_singleton] at hopened
  rcases hopened with hprior | hnew
  · exact invariant.prior_after_append (.opened node value) target opened hprior
  · cases hnew
    exact Or.inl ⟨state.events, [], by simp, hvalid⟩

theorem addTimeout
    (invariant : OpeningHistoryInvariant runtime validator state) (timed : Nat) :
    OpeningHistoryInvariant runtime validator
      { state with timeouts := state.timeouts ++ [timed] } := by
  constructor
  · exact invariant.nodes_unique
  intro node value hopened
  rcases invariant.opening node value hopened with hnormal | hdefault
  · exact Or.inl hnormal
  · right
    obtain ⟨owner, source, requires, hrule, hvalue, htimeout⟩ := hdefault
    refine ⟨owner, source, requires, hrule, hvalue, ?_⟩
    rcases htimeout with hnode | hsource
    · exact Or.inl (List.mem_append_left [timed] hnode)
    · exact Or.inr (List.mem_append_left [timed] hsource)

theorem appendDefault
    (invariant : OpeningHistoryInvariant runtime validator state)
    (node : Nat) (owner : Principal) (source : Nat) (requires : List Nat)
    (hrule : runtime.program.rules[node]? =
      some { kind := .reveal owner source, requires })
    (htimeout : node ∈ state.timeouts ∨ source ∈ state.timeouts)
    (hnotDone : SealedProgram.done state.events node = false) :
    OpeningHistoryInvariant runtime validator
      { state with events := state.events ++ [.opened node runtime.nullValue] } := by
  constructor
  · exact SealedProgram.eventNodes_nodup_append invariant.nodes_unique hnotDone
  intro target value hopened
  simp only [List.mem_append, List.mem_singleton] at hopened
  rcases hopened with hprior | hnew
  · exact invariant.prior_after_append (.opened node runtime.nullValue) target value hprior
  · cases hnew
    exact Or.inr ⟨owner, source, requires, hrule, rfl, htimeout⟩

theorem stamp (invariant : OpeningHistoryInvariant runtime validator state) (node : Nat) :
    OpeningHistoryInvariant runtime validator (state.stamp node) := by
  unfold PublicState.stamp
  split <;> exact ⟨invariant.nodes_unique, invariant.opening⟩

theorem clock (invariant : OpeningHistoryInvariant runtime validator state) :
    OpeningHistoryInvariant runtime validator
      { state with clock := state.clock + 1 } := ⟨invariant.nodes_unique, invariant.opening⟩

theorem expire
    (invariant : OpeningHistoryInvariant runtime validator state)
    (node : Nat) (rule : SealedRule Principal)
    (hrule : runtime.program.rules[node]? = some rule)
    (hnotDone : SealedProgram.done state.events node = false) :
    OpeningHistoryInvariant runtime validator
      (runtime.expire state node rule.kind) := by
  cases hkind : rule.kind with
  | disabled => simpa [SealedResolution.expire, hkind] using invariant
  | commit owner =>
      simpa [SealedResolution.expire, hkind] using invariant.addTimeout node
  | reveal owner source =>
      have hshape : runtime.program.rules[node]? =
          some { kind := .reveal owner source, requires := rule.requires } := by
        have hruleShape :
            rule = ({ kind := .reveal owner source, requires := rule.requires } :
              SealedRule Principal) := by
          cases rule
          simp_all
        rwa [hruleShape] at hrule
      have htimed := invariant.addTimeout node
      have happended := htimed.appendDefault node owner source rule.requires hshape
        (Or.inl (by simp)) hnotDone
      simpa [SealedResolution.expire, hkind] using happended

theorem visit
    (invariant : OpeningHistoryInvariant runtime validator state)
    (resolveExpired : Bool) (node : Nat) :
    OpeningHistoryInvariant runtime validator
      (runtime.visit resolveExpired state node) := by
  cases hrule : runtime.program.rules[node]? with
  | none => simp [SealedResolution.visit, hrule, invariant]
  | some rule =>
      cases hkind : rule.kind with
      | disabled => simpa [SealedResolution.visit, hrule, hkind] using invariant
      | commit owner =>
          simp only [SealedResolution.visit, hrule]
          split
          · exact invariant
          · rename_i hactive
            have hnotDone : SealedProgram.done state.events node = false := by
              cases hdone : SealedProgram.done state.events node <;>
                simp_all [PublicState.completed]
            simp only [hkind]
            split
            · simpa only [hkind] using (invariant.stamp node).expire node rule hrule
                (by simpa using hnotDone)
            · exact invariant.stamp node
      | reveal owner source =>
          simp only [SealedResolution.visit, hrule]
          split
          · exact invariant
          · rename_i hactive
            have hnotDone : SealedProgram.done state.events node = false := by
              cases hdone : SealedProgram.done state.events node <;>
                simp_all [PublicState.completed]
            simp only [hkind]
            split
            · rename_i hsource
              have hshape : runtime.program.rules[node]? = some
                  { kind := .reveal owner source, requires := rule.requires } := by
                have hruleShape : rule =
                    ({ kind := .reveal owner source, requires := rule.requires } :
                      SealedRule Principal) := by
                  cases rule
                  simp_all
                rwa [hruleShape] at hrule
              apply (invariant.stamp node).appendDefault node owner source rule.requires hshape
              · exact Or.inr (by simpa using hsource)
              · simpa using hnotDone
            · split
              · simpa only [hkind] using (invariant.stamp node).expire node rule hrule
                  (by simpa using hnotDone)
              · exact invariant.stamp node

theorem refresh
    (invariant : OpeningHistoryInvariant runtime validator state)
    (resolveExpired : Bool) :
    OpeningHistoryInvariant runtime validator
      (runtime.refresh resolveExpired state) := by
  unfold SealedResolution.refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => exact invariant
  | cons node rest ih => exact ih (invariant.visit resolveExpired node)

theorem initial (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value) :
    OpeningHistoryInvariant runtime validator runtime.candidateInitial.visible := by
  apply (show OpeningHistoryInvariant runtime validator
    ({} : PublicState Principal Value) from by
      constructor
      · simp
      · intro node value hopened
        simp at hopened).refresh false

theorem tick
    {Service : Type (max uPrincipal uValue)}
    (invariant : OpeningHistoryInvariant runtime validator state)
    (service : Service) :
    OpeningHistoryInvariant runtime validator
      (runtime.tick (ApplicationState.mk service state)).visible := by
  unfold SealedResolution.tick
  exact invariant.clock.refresh true

variable [DecidableEq Principal] [DecidableEq Value]

/-- The guarded candidate handler preserves the historical opening witness. -/
theorem guardedCandidateHandle
    {before next : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value)}
    (invariant : OpeningHistoryInvariant runtime validator before.visible)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.guardedCandidateHandle validator before message = some next) :
    OpeningHistoryInvariant runtime validator next.visible := by
  have horiginal :=
    (runtime.guardedCandidateHandle_success validator before next message hnext).1
  unfold SealedResolution.candidateHandle at horiginal
  split at horiginal
  · contradiction
  · cases hmessage : (runtime.program.discharge before.visible.timeouts).candidateMessage?
        before.service before.visible.events message with
    | none => simp [hmessage] at horiginal
    | some result =>
        simp only [hmessage, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq] at horiginal
        have hnotDone :=
          (runtime.program.discharge before.visible.timeouts).candidateMessage?_event_not_done
            before.service before.visible.events message result hmessage
        rcases (runtime.program.discharge before.visible.timeouts).candidateMessage?_effect
            before.service before.visible.events message result hmessage with
          ⟨node, handle, hpayload, hresult⟩ |
          ⟨node, handle, claimed, hpayload, hresult⟩
        · subst result
          subst next
          exact (invariant.appendAccepted node handle hnotDone).refresh false
        · have hvalid := runtime.guardedCandidateHandle_opening_valid validator before next
            message node handle claimed hpayload hnext
          subst result
          subst next
          exact (invariant.appendValidated node claimed hvalid hnotDone).refresh false

end OpeningHistoryInvariant

variable [DecidableEq Principal] [DecidableEq Value]

/-- Historical opening validity survives arbitrary guarded-candidate player
and environment policies, including application clock commands. -/
theorem runPolicies_guarded_openingHistory
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (players : Principal → (runtime.guardedCandidateApplication validator).PlayerPolicy)
    (environment : (runtime.guardedCandidateApplication validator).EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : (runtime.guardedCandidateApplication validator).PolicyExecution)
    (hinitial : OpeningHistoryInvariant runtime validator
      execution.native.application.visible)
    (hnext : next ∈ ((runtime.guardedCandidateApplication validator).runPolicies
      players environment schedule execution).support) :
    OpeningHistoryInvariant runtime validator next.native.application.visible := by
  apply (runtime.guardedCandidateApplication validator).runPolicies_application_invariant
    (fun state => OpeningHistoryInvariant runtime validator state.visible) ?_ ?_ ?_
    players environment schedule execution next hinitial hnext
  · intro state owner command hstate
    exact hstate
  · intro state message result hstate hresult
    exact hstate.guardedCandidateHandle message hresult
  · intro state command result hstate hresult
    simp only [guardedCandidateApplication, SealedResolution.host,
      FinDist.mem_support_pure] at hresult
    subst result
    exact hstate.tick state.service

/-- The same invariant survives arbitrary guarded-candidate round execution,
including wire traffic and every mandatory timeout boundary. -/
theorem runRounds_guarded_openingHistory
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.guardedCandidateApplication validator).PlayerPolicy)
    (environment : (runtime.guardedCandidateApplication validator).WirePolicy)
    (count : Nat)
    (execution next : (runtime.guardedCandidateApplication validator).PolicyExecution)
    (hinitial : OpeningHistoryInvariant runtime validator
      execution.native.application.visible)
    (hnext : next ∈ ((runtime.hostRoundDriver
      (fun state owner slot value => state.prepare owner slot value)
      (runtime.guardedCandidateHandle validator)).runRounds principals serviceSlots
        players environment count execution).support) :
    OpeningHistoryInvariant runtime validator next.native.application.visible := by
  apply (runtime.hostRoundDriver
    (fun state owner slot value => state.prepare owner slot value)
    (runtime.guardedCandidateHandle validator)).runRounds_application_invariant
      (fun state => OpeningHistoryInvariant runtime validator state.visible) ?_ ?_ ?_
      principals serviceSlots players environment count execution next hinitial hnext
  · intro state owner command hstate
    exact hstate
  · intro state message result hstate hresult
    exact hstate.guardedCandidateHandle message hresult
  · intro state command result hstate hresult
    simp only [SealedResolution.host, FinDist.mem_support_pure] at hresult
    subst result
    exact hstate.tick state.service

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runRounds_guarded_openingHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runRounds_guarded_openingHistory
