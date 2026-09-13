/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPrivacy

/-! # Whole-prefix read bound for a native focal registration

Execute the compiled resolving policies with assigned honest values, retaining
an arbitrary native focal policy and adaptive full-pool environment. The law of
the focal registration, cut off at the first timeout, depends only on honest
values whose disclosures precede that source decision. The finite invocation
list is unrestricted; no service or fairness assumption is used for hiding.

The cut is a proof readout of the actual trace, not a restriction on native
commands. The first timeout snapshot follows its clock step, which cannot
change private registrations. Missing registration reads as `none`, distinct
from a registered nullable source choice. This theorem supplies the causal
read bound for extraction; it does not identify the source probability law.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Assigned source choices for compiled opponents, with the focal native
policy unchanged. Assignment substitution is used only in the proof. -/
def resolvingValuePlayers (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (values : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator : (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy) :=
  Profile.update
    (sig := MessageApplication.policySignature Player
      (supported.resolvingRuntime nullValue window).messageApplication)
    (fun who => supported.resolvingPolicy nullValue window who (supported.valuePolicy values who))
    focal deviator

def bindingCut (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (focal : Player) (decision : Fin G.nodeCount)
    (execution : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution) :
    Bool :=
  (execution.native.application.service.lookup (focal, decision.val)).isSome ||
    !execution.native.application.visible.timeouts.isEmpty

/-- First native registration at the focal source handle, or absence if a
timeout or the finite horizon is reached first. -/
def resolvingBindingLaw (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (values : Fin G.nodeCount → L.Val ty) (focal : Player) (decision : Fin G.nodeCount)
    (deviator : (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player)) : FinDist (Option (L.Val ty)) :=
  let runtime := supported.resolvingRuntime nullValue window
  let app := runtime.messageApplication
  ((app.tracePolicies (supported.resolvingValuePlayers nullValue window values focal deviator)
      environment schedule (PolicyExecution.initial app (State.initial app runtime.initial))).map
      (PolicyTrace.firstRelease (supported.bindingCut nullValue window focal decision))).map
    fun execution => execution.native.application.service.lookup (focal, decision.val)

/-- A native deviator cannot choose its registered value as a function
of honest commitments disclosed only after the focal source choice. The
environment may use arbitrary randomized policies over the entire pool. -/
theorem resolvingBindingLaw_read_bound (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (focal : Player) (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (leftValues rightValues : Fin G.nodeCount → L.Val ty)
    (hvalues : ∀ who, who ≠ focal → ∀ node,
      supported.knownBefore focal decision (who, node.val) → leftValues node = rightValues node)
    (deviator : (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player)) :
    supported.resolvingBindingLaw nullValue window leftValues focal decision
        deviator environment schedule =
      supported.resolvingBindingLaw nullValue window rightValues focal decision
        deviator environment schedule := by
  apply SealedResolution.firstRelease_observation_law
    (known := supported.knownBefore focal decision)
    _ _ environment (supported.bindingCut nullValue window focal decision)
    (fun execution => execution.native.application.service.lookup (focal, decision.val))
    ?_ ?_ ?_ schedule _ _ SealedResolution.ExecutionRelated.initial
  · intro left right related
    have hoccupied := related.native.sealed.occupied (focal, decision.val)
    simpa only [bindingCut, SealedResolution.eventState,
      related.native.publicState] using congrArg
        (fun occupied => occupied || !right.native.application.visible.timeouts.isEmpty) hoccupied
  · intro left right related
    exact related.native.sealed.values (focal, decision.val) (Or.inl rfl)
  · intro left right related hcut who
    have hempty : left.native.application.service.lookup (focal, decision.val) = none := by
      have hh : (left.native.application.service.lookup (focal, decision.val)).isSome = false :=
        (Bool.or_eq_false_iff.mp hcut).1
      cases hs : left.native.application.service.lookup (focal, decision.val) with
      | none => rfl
      | some value => simp only [hs, Option.isSome_some, Bool.true_eq_false] at hh
    have hclear : left.native.application.visible.timeouts = [] := by
      have hh := (Bool.or_eq_false_iff.mp hcut).2
      cases ht : left.native.application.visible.timeouts with
      | nil => rfl
      | cons node rest =>
          simp only [ht, List.isEmpty_cons, Bool.not_false, Bool.true_eq_false] at hh
    by_cases hwho : who = focal
    · subst who
      have hh := (related.histories focal).eq (fun _ => Or.inl rfl)
      have hv := related.native.observe_eq focal
      refine ⟨(deviator (left.principalHistory focal) (State.observe _ left.native focal)).map
        (fun command => (command, command)), ?_, ?_, ?_⟩
      · simp only [resolvingValuePlayers, Profile.update_same, FinDist.map_comp,
          Function.comp_def]
        exact (FinDist.map_id _).symm
      · simp only [resolvingValuePlayers, Profile.update_same, FinDist.map_comp,
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
    · obtain ⟨lc, rc, hl, hr, hc, hopen⟩ :=
        supported.resolvingPolicy_before_focal nullValue window focal who decision guard
          hdecision leftValues rightValues left right related hclear hempty (hvalues who hwho)
      refine ⟨FinDist.pure (lc, rc), ?_, ?_, ?_⟩
      · simpa only [resolvingValuePlayers, Profile.update_of_ne _ _ hwho,
          FinDist.map_pure] using hl
      · simpa only [resolvingValuePlayers, Profile.update_of_ne _ _ hwho,
          FinDist.map_pure] using hr
      · intro pair hpair
        simp only [FinDist.mem_support_pure] at hpair
        subst pair
        exact ⟨hc, hopen⟩

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.resolvingBindingLaw_read_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.resolvingBindingLaw_read_bound
