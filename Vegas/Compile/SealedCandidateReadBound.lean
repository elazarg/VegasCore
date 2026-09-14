/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionReplay
import Interaction.SealedCandidateCoupling

/-! # Source-earlier information at candidate acceptance

Assigned honest values vary freely at source-future coordinates. The focal
native policy and the full-pool environment remain arbitrary and randomized.
The actual first-acceptance/timeout readout retains the focal player's entire
local input and its candidate catalog for extraction. No private preparation
is treated as the source-site decision, and no fairness premise is needed.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Assigned honest choices in the actual candidate host, with one arbitrary
native replacement. Only the proof substitutes the honest value assignment. -/
def candidateValuePlayers (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (values : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy) :=
  let runtime := supported.resolvingRuntime nullValue window
  Profile.update (sig := MessageApplication.policySignature Player runtime.candidateApplication)
    (fun who => runtime.candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who (supported.valuePolicy values who)))
    focal deviator

private theorem candidatePolicy_before_focal (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (focal who : Player)
    (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (leftValues rightValues : Fin G.nodeCount → L.Val ty)
    (left right :
      (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (related : SealedResolution.CandidateExecutionRelated
      (supported.resolvingRuntime nullValue window)
      (supported.knownBefore focal decision) left right)
    (hclear : left.native.application.visible.timeouts = [])
    (hnotDone : SealedProgram.done left.native.application.visible.events decision.val = false)
    (hvalues : ∀ node, supported.knownBefore focal decision (who, node.val) →
      leftValues node = rightValues node) :
    let runtime := supported.resolvingRuntime nullValue window
    ∃ leftCommand rightCommand,
      runtime.candidatePlayerPolicy
          (supported.resolvingPolicy nullValue window who (supported.valuePolicy leftValues who))
          (left.principalHistory who) (State.observe _ left.native who) = FinDist.pure leftCommand ∧
      runtime.candidatePlayerPolicy
          (supported.resolvingPolicy nullValue window who (supported.valuePolicy rightValues who))
          (right.principalHistory who) (State.observe _ right.native who) =
        FinDist.pure rightCommand ∧
      SealedProgram.CommandAgreement supported.compile (supported.knownBefore focal decision)
        who leftCommand rightCommand ∧
      (∀ payload, leftCommand = .submit payload →
        SealedProgram.OpeningKnown (supported.knownBefore focal decision)
          ⟨(who, left.native.pool.nextSerial who), payload⟩) := by
  intro runtime
  have hrightClear : right.native.application.visible.timeouts = [] := by
    rw [← related.native.publicState]
    exact hclear
  have hopenings : ∀ (node : Fin G.nodeCount) handle,
      supported.compile.openingHandle? left.native.application.visible.events who node.val =
        some handle → supported.knownBefore focal decision handle := by
    intro node handle hhandle
    exact supported.openingHandle?_knownBefore focal decision guard hdecision _
      hnotDone who node.val handle hhandle
  obtain ⟨lc, rc, hl, hr, hc⟩ := supported.playerPolicy_knowledge
    (supported.knownBefore focal decision) who leftValues rightValues
    (runtime.eventHistory (runtime.registeredPlayerHistory (left.principalHistory who)))
    (runtime.eventHistory (runtime.registeredPlayerHistory (right.principalHistory who)))
    (runtime.eventView (runtime.registeredPlayerView (State.observe _ left.native who)))
    (fun slot => by
      erw [runtime.eventHistory_cache, runtime.eventHistory_cache]
      exact ((related.histories who).cache slot).1)
    (fun slot hknown => by
      erw [runtime.eventHistory_cache, runtime.eventHistory_cache]
      exact ((related.histories who).cache slot).2 hknown) hvalues hopenings
  have hleft : runtime.candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who (supported.valuePolicy leftValues who))
      (left.principalHistory who) (State.observe _ left.native who) = FinDist.pure lc := by
    rw [SealedResolution.candidatePlayerPolicy,
      supported.resolvingPolicy_no_timeout nullValue window who _ _ _ hclear]
    exact hl
  have hright : runtime.candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who (supported.valuePolicy rightValues who))
      (right.principalHistory who) (State.observe _ right.native who) = FinDist.pure rc := by
    rw [SealedResolution.candidatePlayerPolicy,
      supported.resolvingPolicy_no_timeout nullValue window who _ _ _ hrightClear,
      ← related.native.observe_eq who]
    exact hr
  refine ⟨lc, rc, hleft, hright, hc, ?_⟩
  intro payload hp
  have hsubmit : .submit payload ∈
      (runtime.candidatePlayerPolicy
        (supported.resolvingPolicy nullValue window who (supported.valuePolicy leftValues who))
        (left.principalHistory who) (State.observe _ left.native who)).support := by
    rw [hleft, hp, FinDist.mem_support_pure]
  rcases supported.resolvingPolicy_submission nullValue window who _ _ _ payload hsubmit with
    ⟨node, rfl, _⟩ | ⟨node, handle, value, rfl, hhandle⟩
  · trivial
  · simp only [SealedResolution.registeredPlayerView, State.observe,
      SealedResolution.candidateApplication, SealedResolution.host,
      hclear, SealedProgram.discharge_nil] at hhandle
    intro _
    exact supported.openingHandle?_knownBefore focal decision guard hdecision _
      hnotDone who node handle hhandle

/-- Whole-prefix candidate-host hiding for any related readout that stops by
the focal source site's acceptance or the first timeout. This uses the actual
shared runner and its complete adaptive environment input. -/
theorem candidateValuePlayers_cut_law {Observation : Type*} (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (focal : Player) (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (leftValues rightValues : Fin G.nodeCount → L.Val ty)
    (hvalues : ∀ who, who ≠ focal → ∀ node,
      supported.knownBefore focal decision (who, node.val) → leftValues node = rightValues node)
    (deviator : (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (cut : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution →
      Bool)
    (observe : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution →
      Observation)
    (hcut : ∀ left right, SealedResolution.CandidateExecutionRelated
      (supported.resolvingRuntime nullValue window) (supported.knownBefore focal decision)
      left right → cut left = cut right)
    (hobserve : ∀ left right, SealedResolution.CandidateExecutionRelated
      (supported.resolvingRuntime nullValue window) (supported.knownBefore focal decision)
      left right → observe left = observe right)
    (hbefore : ∀ left right, SealedResolution.CandidateExecutionRelated
      (supported.resolvingRuntime nullValue window) (supported.knownBefore focal decision)
      left right → cut left = false →
      left.native.application.visible.timeouts = [] ∧
      SealedProgram.done left.native.application.visible.events decision.val = false) :
    let runtime := supported.resolvingRuntime nullValue window
    let app := runtime.candidateApplication
    ((app.tracePolicies (supported.candidateValuePlayers nullValue window leftValues focal deviator)
      environment schedule
      (PolicyExecution.initial app (State.initial app runtime.candidateInitial))).map
        (PolicyTrace.firstRelease cut)).map observe =
      ((app.tracePolicies
        (supported.candidateValuePlayers nullValue window rightValues focal deviator)
        environment schedule
        (PolicyExecution.initial app (State.initial app runtime.candidateInitial))).map
          (PolicyTrace.firstRelease cut)).map observe := by
  apply SealedResolution.candidate_firstRelease_observation_law
    (known := supported.knownBefore focal decision)
    _ _ environment cut observe hcut hobserve ?_ schedule _ _
    SealedResolution.CandidateExecutionRelated.initial
  intro left right related hstop who
  obtain ⟨hclear, hnotDone⟩ := hbefore left right related hstop
  by_cases hwho : who = focal
  · subst who
    have hh := related.history_eq focal (fun _ => Or.inl rfl)
    have hv := related.native.observe_eq focal
    refine ⟨(deviator (left.principalHistory focal) (State.observe _ left.native focal)).map
      (fun command => (command, command)), ?_, ?_, ?_⟩
    · simp only [candidateValuePlayers, Profile.update_same, FinDist.map_comp, Function.comp_def]
      exact (FinDist.map_id _).symm
    · simp only [candidateValuePlayers, Profile.update_same, FinDist.map_comp,
        Function.comp_def, hh, hv]
      exact (FinDist.map_id _).symm
    · intro pair hpair
      rw [FinDist.support_map] at hpair
      obtain ⟨command, _, rfl⟩ := hpair
      refine ⟨SealedProgram.CommandAgreement.refl _ focal, ?_⟩
      intro payload _
      cases payload with
      | commitment | cleartext | malformed => trivial
      | opening node handle value => exact fun h => Or.inl h.symm
  · obtain ⟨lc, rc, hl, hr, hc, hopen⟩ := supported.candidatePolicy_before_focal nullValue window
      focal who decision guard hdecision leftValues rightValues left right related hclear hnotDone
      (hvalues who hwho)
    refine ⟨FinDist.pure (lc, rc), ?_, ?_, ?_⟩
    · simpa only [candidateValuePlayers, Profile.update_of_ne _ _ hwho, FinDist.map_pure] using hl
    · simpa only [candidateValuePlayers, Profile.update_of_ne _ _ hwho, FinDist.map_pure] using hr
    · intro pair hpair
      simp only [FinDist.mem_support_pure] at hpair
      subst pair
      exact ⟨hc, hopen⟩

/-- First public completion of the source commitment or first timeout. Private
preparation alone never triggers this readout. -/
def candidateAcceptanceCut (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (decision : Fin G.nodeCount)
    (execution :
      (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution) :
    Bool :=
  SealedProgram.done execution.native.application.visible.events decision.val ||
    !execution.native.application.visible.timeouts.isEmpty

/-- The focal player's actual local input and owner-scoped candidate catalog
at first acceptance, timeout, or the finite horizon. The catalog component is
proof-facing extraction data; the runtime does not expose it to policies. -/
def candidateAcceptanceLaw (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (values : Fin G.nodeCount → L.Val ty) (focal : Player) (decision : Fin G.nodeCount)
    (deviator : (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player)) :
    FinDist (List (supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry ×
      (supported.resolvingRuntime nullValue window).candidateApplication.View ×
      (Nat → CommitmentCandidate (L.Val ty))) :=
  let runtime := supported.resolvingRuntime nullValue window
  let app := runtime.candidateApplication
  ((app.tracePolicies (supported.candidateValuePlayers nullValue window values focal deviator)
    environment schedule
    (PolicyExecution.initial app (State.initial app runtime.candidateInitial))).map
      (PolicyTrace.firstRelease (supported.candidateAcceptanceCut nullValue window decision))).map
    fun execution => (execution.principalHistory focal, State.observe app execution.native focal,
      fun slot => execution.native.application.service.lookup (focal, slot))

/-- Source-future hidden honest choices change neither the focal player's
complete input nor any of its candidate meanings through public acceptance.
The focal policy and full-pool environment are arbitrary and randomized;
several preparations, competing submissions, and unopenable candidates are
permitted. No service, completion, or incentive assumption is used. -/
theorem candidateAcceptanceLaw_read_bound (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (focal : Player) (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (leftValues rightValues : Fin G.nodeCount → L.Val ty)
    (hvalues : ∀ who, who ≠ focal → ∀ node,
      supported.knownBefore focal decision (who, node.val) → leftValues node = rightValues node)
    (deviator : (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player)) :
    supported.candidateAcceptanceLaw nullValue window leftValues focal decision
        deviator environment schedule =
      supported.candidateAcceptanceLaw nullValue window rightValues focal decision
        deviator environment schedule := by
  apply supported.candidateValuePlayers_cut_law nullValue window focal decision guard hdecision
    leftValues rightValues hvalues deviator environment schedule
    (supported.candidateAcceptanceCut nullValue window decision)
    (fun execution => (execution.principalHistory focal, State.observe _ execution.native focal,
      fun slot => execution.native.application.service.lookup (focal, slot)))
  · intro left right related
    simp only [candidateAcceptanceCut, related.native.publicState]
  · intro left right related
    refine Prod.ext (related.history_eq focal (fun _ => Or.inl rfl))
      (Prod.ext (related.native.observe_eq focal) ?_)
    funext slot
    exact related.native.values (focal, slot) (Or.inl rfl)
  · intro left _right _related hcut
    have hdone := (Bool.or_eq_false_iff.mp hcut).1
    have hh := (Bool.or_eq_false_iff.mp hcut).2
    refine ⟨?_, hdone⟩
    cases ht : left.native.application.visible.timeouts with
    | nil => rfl
    | cons node rest =>
        simp only [ht, List.isEmpty_cons, Bool.not_false, Bool.true_eq_false] at hh

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidateAcceptanceLaw_read_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidateAcceptanceLaw_read_bound
