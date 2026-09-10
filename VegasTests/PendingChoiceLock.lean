/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.PendingRelease
import Interaction.SealedPolicyBinding

/-! # The opponent's value at the compiled release boundary

The extracted value is analysis data, not an added runtime observation.
Its outer `none` records that release was not reached; `some none` records
the source's nullable decline value at a reached release boundary.
The complete native executions still include their post-release suffixes.
-/

noncomputable section

namespace VegasTests.PendingChoiceLock

open Interaction Interaction.SealedProgram GameTheory GameTheory.Math.Probability
open VegasTests.PendingSource VegasTests.PendingExecution VegasTests.PendingPolicies
open Interaction.MessageApplication
open VegasTests.PendingRelease

def choiceAtRelease (execution : Application.PolicyExecution) : Option Value :=
  if release execution.native.application.events then
    execution.native.application.service.lookup (1, 1) else none

private theorem choiceAtRelease_congr {left right : Application.PolicyExecution}
    (related : ApplicationPolicyRelated program (0 : Player) left right) :
    choiceAtRelease left = choiceAtRelease right := by
  have hevents : left.native.application.events = right.native.application.events :=
    related.native.native.events
  have hvalue : left.native.application.service.lookup (1, 1) =
      right.native.application.service.lookup (1, 1) :=
    related.native.native.service.1 (1, 1) (by decide)
  simp only [choiceAtRelease, hevents, hvalue]

theorem choiceAtRelease_lookup {execution : Application.PolicyExecution} {chosen : Value}
    (hchoice : choiceAtRelease execution = some chosen) :
    execution.native.application.service.lookup (1, 1) = some chosen := by
  unfold choiceAtRelease at hchoice
  split at hchoice
  · exact hchoice
  · contradiction

theorem choiceAtRelease_ready {execution : Application.PolicyExecution} {chosen : Value}
    (hchoice : choiceAtRelease execution = some chosen) :
    release execution.native.application.events = true := by
  unfold choiceAtRelease at hchoice
  split at hchoice
  · assumption
  · contradiction

def choiceLaw (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) :
    FinDist (Option Value) :=
  ((controllerTraceLaw value players environment schedule).map
    (PolicyTrace.firstRelease releaseSnapshot)).map choiceAtRelease

/-- The opponent's extracted value (including the unreached-release marker)
has one law independent of the protected owner's chosen source value. All
opponent and environment policies are unchanged and may adapt to native views. -/
theorem choiceLaw_independent (left right : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) :
    choiceLaw left players environment schedule =
      choiceLaw right players environment schedule := by
  unfold choiceLaw
  rw [controllerTraceLaw_firstRelease, controllerTraceLaw_firstRelease]
  apply tracePolicies_release_readout_congr (hiddenOwner := 0)
  · intro who hne
    simp only [openingProfile, Profile.update_of_ne _ _ hne]
  · simpa only [openingProfile, Profile.update_same, WaitsBeforeRelease,
      release, openingReady] using openingPolicy_waitsBefore program 0 2 left
  · simpa only [openingProfile, Profile.update_same, WaitsBeforeRelease,
      release, openingReady] using openingPolicy_waitsBefore program 0 2 right
  · exact fun related => choiceAtRelease_congr related
  · exact prepared_related left right

/-- Randomizing the protected source input yields a product law with the
opponent's extracted choice. This includes failure to reach release and does
not condition on later completion. -/
theorem mixed_choiceLaw_product (input : FinDist Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) :
    (input.bind fun value =>
      (controllerTraceLaw value players environment schedule).map
        (fun trace => (value, choiceAtRelease (trace.firstRelease releaseSnapshot)))) =
      input.product (choiceLaw none players environment schedule) := by
  change _ = input.bind (fun value =>
    (choiceLaw none players environment schedule).map (Prod.mk value))
  apply FinDist.bind_congr
  intro value _
  rw [← choiceLaw_independent value none players environment schedule]
  simp only [choiceLaw, FinDist.map_comp, Function.comp_def]

/-- Once extracted at release, the opponent's value is fixed through the
post-release suffix of this same complete trace, including arbitrary retries,
malformed messages, registrations, and withheld openings. -/
theorem choiceAtRelease_persists (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (trace : Application.PolicyTrace)
    (htrace : trace ∈ (controllerTraceLaw value players environment schedule).support)
    (chosen : Value)
    (hchoice : choiceAtRelease (trace.firstRelease releaseSnapshot) = some chosen) :
    trace.last.native.application.service.lookup (1, 1) = some chosen :=
  tracePolicies_firstRelease_lookup_persists program
    (controllerProfile value players) environment releaseSnapshot
    (.player 0 :: .player 0 :: schedule) (initialExecution) trace (1, 1) chosen
    htrace (choiceAtRelease_lookup hchoice)

/-- Reaching this compiled release barrier guarantees an actual occupied
opponent slot. Only an unreached release can produce the outer `none`. -/
theorem choiceAtRelease_some (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (trace : Application.PolicyTrace)
    (htrace : trace ∈ (controllerTraceLaw value players environment schedule).support)
    (hrelease : release (trace.firstRelease releaseSnapshot).native.application.events = true) :
    ∃ chosen, choiceAtRelease (trace.firstRelease releaseSnapshot) = some chosen := by
  have invariant := tracePolicies_firstRelease_bindingInvariant program
    (controllerProfile value players) environment releaseSnapshot
    (.player 0 :: .player 0 :: schedule) applicationInitial trace
    (BindingInvariant.empty program) htrace
  obtain ⟨chosen, hlookup⟩ := invariant.done_commit_lookup 1 1 [] rfl
    (release_requires_both _ hrelease).2
  simp only [eraseReceipts] at hlookup
  refine ⟨chosen, ?_⟩
  simpa only [choiceAtRelease, hrelease, ↓reduceIte] using hlookup

/-- On supported traces, outer absence records precisely an unreached release;
it never conflates that case with the legal nullable source value. -/
theorem choiceAtRelease_none_iff (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (trace : Application.PolicyTrace)
    (htrace : trace ∈ (controllerTraceLaw value players environment schedule).support) :
    choiceAtRelease (trace.firstRelease releaseSnapshot) = none ↔
      release (trace.firstRelease releaseSnapshot).native.application.events = false := by
  constructor
  · intro hnone
    cases hrelease : release (trace.firstRelease releaseSnapshot).native.application.events with
    | false => rfl
    | true =>
        obtain ⟨chosen, hchoice⟩ := choiceAtRelease_some value players environment
          schedule trace htrace hrelease
        rw [hnone] at hchoice
        contradiction
  · intro hrelease
    simp [choiceAtRelease, hrelease]

/-- The extracted value is the actual compiled source binding, not merely a
value stored in an unrelated private runtime slot. -/
theorem choiceAtRelease_source_field (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (trace : Application.PolicyTrace)
    (htrace : trace ∈ (controllerTraceLaw value players environment schedule).support)
    (chosen : Value)
    (hchoice : choiceAtRelease (trace.firstRelease releaseSnapshot) = some chosen) :
    ∃ cfg : Vegas.EventGraph.Config graph,
      graph.decodeSealed (.option .bool)
        (program.eraseReceipts (trace.firstRelease releaseSnapshot).native) = some cfg ∧
      Vegas.EventGraph.Reachable graph cfg ∧
      Vegas.EventGraph.Store.getAs cfg.store (graph.nodeTarget (node 1)) (.option .bool) =
        some chosen := by
  have invariant := tracePolicies_firstRelease_bindingInvariant program
    (controllerProfile value players) environment releaseSnapshot
    (.player 0 :: .player 0 :: schedule) applicationInitial trace
    (BindingInvariant.empty program) htrace
  have haccepted := invariant.accepted_mem_of_done_commit 1 1 [] rfl
    (release_requires_both _ (choiceAtRelease_ready hchoice)).2
  obtain ⟨front, _, _, hcut, _⟩ := Application.tracePolicies_firstRelease_split
    (controllerProfile value players) environment releaseSnapshot
    (.player 0 :: .player 0 :: schedule) initialExecution trace htrace
  have hnative := runPolicies_eraseReceipts_eq_run_trace program
    (controllerProfile value players) environment front applicationInitial _ hcut
  have hnodup := run_eventNodes_nodup program (program.eraseReceipts applicationInitial)
    ((trace.firstRelease releaseSnapshot).nativeTrace.map program.nativeAction) (by
      simp [applicationInitial, MessageApplication.State.initial, eraseReceipts])
  rw [← hnative] at hnodup
  obtain ⟨cfg, hdecode, hreachable⟩ :=
    controllerTraceLaw_cut_reachable value players environment schedule trace htrace
  have hfield := Vegas.EventGraph.Graph.decodeSealed_accepted_getAs (G := graph) (.option .bool)
    (program.eraseReceipts (trace.firstRelease releaseSnapshot).native) cfg (node 1) (1, 1)
      hnodup haccepted hdecode
  exact ⟨cfg, hdecode, hreachable, hfield.2.trans (choiceAtRelease_lookup hchoice)⟩

/-- Any accepted later opening of the opponent's node discloses exactly the
value extracted before the honest owner's release. This does not force an
opening to occur. -/
theorem opened_eq_choiceAtRelease (value : Value)
    (players : Profile (MessageApplication.policySignature Player Application))
    (environment : Application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (trace : Application.PolicyTrace)
    (htrace : trace ∈ (controllerTraceLaw value players environment schedule).support)
    (chosen disclosed : Value)
    (hchoice : choiceAtRelease (trace.firstRelease releaseSnapshot) = some chosen)
    (hopened : Event.opened 3 disclosed ∈ trace.last.native.application.events) :
    disclosed = chosen := by
  have invariant := tracePolicies_last_bindingInvariant program
    (controllerProfile value players) environment
    (.player 0 :: .player 0 :: schedule) applicationInitial trace
    (BindingInvariant.empty program) htrace
  obtain ⟨owner, sourceNode, requires, hrule, hlookup⟩ := invariant.opened 3 disclosed hopened
  have hkind := congrArg SealedRule.kind (Option.some.inj hrule)
  change SealedRuleKind.reveal (1 : Player) 1 = .reveal owner sourceNode at hkind
  obtain ⟨rfl, rfl⟩ := SealedRuleKind.reveal.inj hkind
  exact Option.some.inj (hlookup.symm.trans
    (choiceAtRelease_persists value players environment schedule trace htrace
      chosen hchoice))

end VegasTests.PendingChoiceLock

/-- info: 'VegasTests.PendingChoiceLock.mixed_choiceLaw_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingChoiceLock.mixed_choiceLaw_product

/-- info: 'VegasTests.PendingChoiceLock.choiceAtRelease_source_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingChoiceLock.choiceAtRelease_source_field

/-- info: 'VegasTests.PendingChoiceLock.opened_eq_choiceAtRelease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingChoiceLock.opened_eq_choiceAtRelease
