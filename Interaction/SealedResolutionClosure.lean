/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionEvents
import Interaction.SealedResolutionProgress

/-! # Closure of propagated reveal defaults

A source-ordered refresh propagates every earlier commitment timeout to each
ready reveal that consumes it.  Thus a canonical runtime snapshot cannot leave
such a reveal incomplete merely because no opening message will arrive.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- Every ready reveal whose producer timed out has itself completed. -/
def PublicState.ResolutionClosed (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) : Prop :=
  ∀ (node : Nat) (owner : Principal) (source : Nat) (requires : List Nat),
    runtime.program.rules[node]? = some { kind := .reveal owner source, requires } →
    requires.all state.completed = true →
    source ∈ state.timeouts →
    state.completed node = true

private theorem visit_completed_eq_of_ne (runtime : SealedResolution Principal Value)
    (resolveExpired : Bool) (state : PublicState Principal Value)
    (visited target : Nat) (hne : visited ≠ target) :
    (runtime.visit resolveExpired state visited).completed target = state.completed target := by
  have hbeq : (visited == target) = false := beq_eq_false_iff_ne.mpr hne
  have hdecide : decide (target = visited) = false := decide_eq_false (Ne.symm hne)
  unfold SealedResolution.visit
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · dsimp only
        split
        · simp [PublicState.completed, SealedProgram.done, SealedProgram.Event.node, hbeq]
        · split
          · unfold expire
            split <;> simp [PublicState.completed, SealedProgram.done,
              SealedProgram.Event.node, hbeq, hdecide]
          · exact state.completed_stamp visited target
      · dsimp only
        split
        · unfold expire
          split <;> simp [PublicState.completed, SealedProgram.done,
            SealedProgram.Event.node, hbeq, hdecide]
        · exact state.completed_stamp visited target

private theorem visit_timeout_mem_iff_of_ne (runtime : SealedResolution Principal Value)
    (resolveExpired : Bool) (state : PublicState Principal Value)
    (visited target : Nat) (hne : visited ≠ target) :
    target ∈ (runtime.visit resolveExpired state visited).timeouts ↔
      target ∈ state.timeouts := by
  have htargetNe : target ≠ visited := Ne.symm hne
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
          · unfold expire
            split <;> simp [htargetNe]
          · simp
      · dsimp only
        split
        · unfold expire
          split <;> simp [htargetNe]
        · simp

private theorem visit_completes_timedOut_reveal
    (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node : Nat) (owner : Principal)
    (source : Nat) (requires : List Nat)
    (hrule : runtime.program.rules[node]? =
      some { kind := .reveal owner source, requires })
    (hrequires : requires.all state.completed = true)
    (hsource : source ∈ state.timeouts) :
    (runtime.visit resolveExpired state node).completed node = true := by
  rw [show runtime.visit resolveExpired state node =
      if state.completed node || !requires.all state.completed then state
      else
        { state.stamp node with
          events := (state.stamp node).events ++ [.opened node runtime.nullValue] } by
    simp [SealedResolution.visit, hrule, hsource]]
  by_cases hcompleted : state.completed node = true
  · simp [hcompleted]
  · have hcompletedFalse := Bool.eq_false_of_not_eq_true hcompleted
    simp only [hcompletedFalse, Bool.false_or, hrequires, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    simp [PublicState.completed, SealedProgram.done, SealedProgram.Event.node]

private def PublicState.ResolutionClosedThrough
    (runtime : SealedResolution Principal Value) (bound : Nat)
    (state : PublicState Principal Value) : Prop :=
  ∀ node < bound, ∀ (owner : Principal) (source : Nat) (requires : List Nat),
    runtime.program.rules[node]? = some { kind := .reveal owner source, requires } →
    requires.all state.completed = true →
    source ∈ state.timeouts →
    state.completed node = true

private theorem resolutionClosedThrough_range
    (runtime : SealedResolution Principal Value)
    (hbackward : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node)
    (hsource : ∀ (node : Nat) (owner : Principal) (source : Nat) (requires : List Nat),
      runtime.program.rules[node]? = some { kind := .reveal owner source, requires } →
      source < node)
    (resolveExpired : Bool) (initial : PublicState Principal Value) (bound : Nat) :
    PublicState.ResolutionClosedThrough runtime bound
      ((List.range bound).foldl (runtime.visit resolveExpired) initial) := by
  induction bound with
  | zero => intro node hnode; omega
  | succ bound ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      let before := (List.range bound).foldl (runtime.visit resolveExpired) initial
      have hprior : PublicState.ResolutionClosedThrough runtime bound before := ih
      intro node hnode owner source requires hrule hrequires hsourceTimeout
      by_cases hnodePrior : node < bound
      · have hne : bound ≠ node := by omega
        apply runtime.visit_completed resolveExpired before bound node
        apply hprior node hnodePrior owner source requires hrule
        · apply List.all_eq_true.mpr
          intro prerequisite hprerequisite
          have hprerequisiteLt : prerequisite < node :=
            hbackward node
              ({ kind := .reveal owner source, requires } : SealedRule Principal) hrule
              prerequisite hprerequisite
          have hfinal := List.all_eq_true.mp hrequires prerequisite hprerequisite
          rwa [runtime.visit_completed_eq_of_ne resolveExpired before bound prerequisite
            (by omega)] at hfinal
        · exact (runtime.visit_timeout_mem_iff_of_ne resolveExpired before bound source
            (by have := hsource node owner source requires hrule; omega)).mp hsourceTimeout
      · have hnodeEq : node = bound := by omega
        subst node
        apply runtime.visit_completes_timedOut_reveal resolveExpired before bound owner source
          requires hrule
        · apply List.all_eq_true.mpr
          intro prerequisite hprerequisite
          have hlt := hbackward bound
            ({ kind := .reveal owner source, requires } : SealedRule Principal) hrule
              prerequisite hprerequisite
          have hfinal := List.all_eq_true.mp hrequires prerequisite hprerequisite
          rwa [runtime.visit_completed_eq_of_ne resolveExpired before bound prerequisite
            (by omega)] at hfinal
        · exact (runtime.visit_timeout_mem_iff_of_ne resolveExpired before bound source
            (by have := hsource bound owner source requires hrule; omega)).mp hsourceTimeout

/-- One full source-ordered scan closes propagation from every earlier timed-out
producer to its ready reveal. -/
theorem refresh_resolutionClosed
    (runtime : SealedResolution Principal Value)
    (hbackward : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node)
    (hsource : ∀ (node : Nat) (owner : Principal) (source : Nat) (requires : List Nat),
      runtime.program.rules[node]? = some { kind := .reveal owner source, requires } →
      source < node)
    (resolveExpired : Bool) (state : PublicState Principal Value) :
    (runtime.refresh resolveExpired state).ResolutionClosed runtime := by
  unfold SealedResolution.refresh
  have hthrough := runtime.resolutionClosedThrough_range hbackward hsource resolveExpired state
    runtime.program.rules.length
  intro node owner source requires hrule
  apply hthrough node ?_ owner source requires hrule
  exact (List.getElem?_eq_some_iff.mp hrule).1

variable {Service : Type (max uPrincipal uValue)}
variable [DecidableEq Principal]

namespace PublicState.ResolutionClosed

variable {runtime : SealedResolution Principal Value}
variable {state : ApplicationState Principal Value Service}

omit [DecidableEq Principal] in
theorem initial
    (hbackward : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node)
    (hsource : ∀ (node : Nat) (owner : Principal) (source : Nat) (requires : List Nat),
      runtime.program.rules[node]? = some { kind := .reveal owner source, requires } →
      source < node) :
    runtime.initial.visible.ResolutionClosed runtime :=
  runtime.refresh_resolutionClosed hbackward hsource false {}

omit [DecidableEq Principal] in
theorem tick
    (hbackward : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node)
    (hsource : ∀ (node : Nat) (owner : Principal) (source : Nat) (requires : List Nat),
      runtime.program.rules[node]? = some { kind := .reveal owner source, requires } →
      source < node) :
    (runtime.tick state).visible.ResolutionClosed runtime := by
  unfold SealedResolution.tick
  exact runtime.refresh_resolutionClosed hbackward hsource true _

end PublicState.ResolutionClosed

/-- Closure is invariant under arbitrary randomized native policies once it
holds initially; every handler and clock transition re-establishes it by a full
source-ordered refresh. -/
theorem runPolicies_resolutionClosed
    (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
        Option (ApplicationState Principal Value Service))
    (hrecords : runtime.HandlerRecords applyMessage)
    (hbackward : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node)
    (hsource : ∀ (node : Nat) (owner : Principal) (source : Nat) (requires : List Nat),
      runtime.program.rules[node]? = some { kind := .reveal owner source, requires } →
      source < node)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hinitial : execution.native.application.visible.ResolutionClosed runtime)
    (hnext : next ∈ ((runtime.host prepare applyMessage).runPolicies players environment
      schedule execution).support) :
    next.native.application.visible.ResolutionClosed runtime := by
  apply (runtime.host prepare applyMessage).runPolicies_application_invariant
    (fun state => state.visible.ResolutionClosed runtime) ?_ ?_ ?_
      players environment schedule execution next hinitial hnext
  · intro state owner command hclosed
    exact hclosed
  · intro state message after _hclosed hafter
    obtain ⟨event, hvisible⟩ := hrecords state message after hafter
    rw [hvisible]
    exact runtime.refresh_resolutionClosed hbackward hsource false _
  · intro state command after _hclosed hafter
    simp only [host, FinDist.mem_support_pure] at hafter
    subst after
    exact PublicState.ResolutionClosed.tick hbackward hsource

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_resolutionClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_resolutionClosed
