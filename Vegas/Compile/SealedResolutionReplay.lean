/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionReadBound
import Interaction.SealedResolutionRounds

/-! # Fixed-seed replay and causal registration extraction

The replay selects the unique trace of the shared resolving runner when honest
choices and native deviator/environment responses are fixed. It includes
post-timeout execution; a source choice is extracted from the first registration
or first-timeout snapshot. No separate operational transition is introduced.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

theorem resolvingPolicy_valuePolicy_pure (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (values : Fin G.nodeCount → L.Val ty)
    (who : Player)
    (history : List (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (view : (supported.resolvingRuntime nullValue window).messageApplication.View) :
    ∃ command, supported.resolvingPolicy nullValue window who (supported.valuePolicy values who)
      history view = FinDist.pure command := by
  obtain ⟨command, hcommand⟩ :=
    (supported.resolvingPolicy nullValue window who (supported.valuePolicy values who)
      history view).support_nonempty
  refine ⟨command, ?_⟩
  exact supported.selected_valuePolicy_congr values values who view.application.timeouts
    ((supported.resolvingRuntime nullValue window).eventHistory history)
    ((supported.resolvingRuntime nullValue window).eventView view)
    _ command hcommand (fun _ _ => rfl)

variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)

private theorem resolvingReplay_exists (values : Fin G.nodeCount → L.Val ty) (focal : Player)
    (deviator :
      List (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
      (supported.resolvingRuntime nullValue window).messageApplication.View →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand)
    (environment :
      List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
    (schedule : List (@Invocation Player)) :
    ∃ trace, (supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
      (supported.resolvingValuePlayers nullValue window values focal
        (fun history view => FinDist.pure (deviator history view)))
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _
        (supported.resolvingRuntime nullValue window).initial)) = FinDist.pure trace := by
  apply MessageApplication.tracePolicies_pure _ _ _ ?_
    (fun _ _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩)
  intro who history view
  by_cases hwho : who = focal
  · subst who
    exact ⟨deviator history view, by
      simp only [resolvingValuePlayers, GameTheory.Profile.update_same]⟩
  · rw [resolvingValuePlayers, GameTheory.Profile.update_of_ne _ _ hwho]
    exact supported.resolvingPolicy_valuePolicy_pure nullValue window values who history view

variable (values : Fin G.nodeCount → L.Val ty) (focal : Player)
variable (deviator :
  List (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
  (supported.resolvingRuntime nullValue window).messageApplication.View →
  (supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand)
variable (environment :
  List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))

def resolvingReplay :
    (supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace :=
  Classical.choose (supported.resolvingReplay_exists nullValue window values focal
    deviator environment schedule)

theorem resolvingReplay_law :
    (supported.resolvingRuntime nullValue window).messageApplication.tracePolicies
      (supported.resolvingValuePlayers nullValue window values focal
        (fun history view => FinDist.pure (deviator history view)))
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _
        (supported.resolvingRuntime nullValue window).initial)) =
      FinDist.pure (supported.resolvingReplay nullValue window values focal
        deviator environment schedule) :=
  Classical.choose_spec (supported.resolvingReplay_exists nullValue window values focal
    deviator environment schedule)

/-- The first timeout snapshot, or the last snapshot at the finite horizon.
This is a proof readout of the complete native replay, not a runtime stop. -/
def resolvingStop :
    (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution :=
  (supported.resolvingReplay nullValue window values focal
    deviator environment schedule).firstRelease (fun execution :
      (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution =>
        !execution.native.application.visible.timeouts.isEmpty)

def resolvingBinding (decision : Fin G.nodeCount) : Option (L.Val ty) :=
  ((supported.resolvingReplay nullValue window values focal
      deviator environment schedule).firstRelease
    (supported.bindingCut nullValue window focal decision)).native.application.service.lookup
      (focal, decision.val)

theorem resolvingBinding_law (decision : Fin G.nodeCount) :
    supported.resolvingBindingLaw nullValue window values focal decision
      (fun history view => FinDist.pure (deviator history view))
      (fun history view => FinDist.pure (environment history view)) schedule =
      FinDist.pure (supported.resolvingBinding nullValue window values focal
        deviator environment schedule decision) := by
  simp only [resolvingBindingLaw, resolvingReplay_law, FinDist.map_pure]
  rfl

/-- All extracted first registrations can be read at one common first-timeout
snapshot. The resolving runtime retains its private service across the tick,
so this also covers the snapshot immediately after resolution. -/
theorem resolvingBinding_eq_stop_lookup (decision : Fin G.nodeCount) :
    supported.resolvingBinding nullValue window values focal
      deviator environment schedule decision =
      (supported.resolvingStop nullValue window values focal
        deviator environment schedule).native.application.service.lookup (focal, decision.val) := by
  refine MessageApplication.tracePolicies_firstRelease_option
    (supported.resolvingRuntime nullValue window).messageApplication
    (supported.resolvingValuePlayers nullValue window values focal
      (fun history view => FinDist.pure (deviator history view)))
    (fun history view => FinDist.pure (environment history view))
    (fun execution => execution.native.application.service.lookup (focal, decision.val))
    (fun execution => !execution.native.application.visible.timeouts.isEmpty)
    ?_ schedule
    (PolicyExecution.initial _ (State.initial _
      (supported.resolvingRuntime nullValue window).initial)) _ ?_
  · intro invocations initial next hnext value hvalue
    exact (supported.resolvingRuntime nullValue window).runPolicies_lookup_of_eq_some
      _ _ invocations initial next (focal, decision.val) value hvalue hnext
  · rw [resolvingReplay_law, FinDist.mem_support_pure]

/-- Pointwise causal extraction using the same native seed at all decisions.
Both registration and absence are independent of source-future honest values. -/
theorem resolvingBinding_read_bound (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (rightValues : Fin G.nodeCount → L.Val ty)
    (hvalues : ∀ who, who ≠ focal → ∀ node,
      supported.knownBefore focal decision (who, node.val) → values node = rightValues node) :
    supported.resolvingBinding nullValue window values focal
        deviator environment schedule decision =
      supported.resolvingBinding nullValue window rightValues focal
        deviator environment schedule decision := by
  have hlaw := supported.resolvingBindingLaw_read_bound nullValue window focal decision guard
    hdecision values rightValues hvalues (fun history view => FinDist.pure (deviator history view))
    (fun history view => FinDist.pure (environment history view)) schedule
  rw [resolvingBinding_law, resolvingBinding_law] at hlaw
  apply FinDist.mem_support_pure.mp
  rw [← hlaw]
  exact FinDist.mem_support_pure.mpr rfl

/-- The honest coordinates disclosed before the focal source choice.
Membership is static program data, independent of native delivery order. -/
def priorHonestCoordinates (decision : Fin G.nodeCount) : Set (Fin G.nodeCount) :=
  {node | ∃ who, who ≠ focal ∧ supported.knownBefore focal decision (who, node.val)}

omit [DecidableEq (L.Val ty)] in
theorem priorHonestCoordinates_opening (decision node : Fin G.nodeCount)
    (hnode : node ∈ supported.priorHonestCoordinates focal decision) :
    ∃ opening : Fin G.nodeCount, opening.val < decision.val ∧
      (G.nodeRow opening).sem = .reveal (G.nodeTarget node) := by
  obtain ⟨who, hwho, hknown⟩ := hnode
  rcases hknown with howner | ⟨opening, requires, hbefore, hrule⟩
  · exact False.elim (hwho howner)
  · obtain ⟨actual, producer, guard, hactual, hproducer, hsem, _⟩ :=
      supported.ruleAt_reveal hrule rfl
    have heq : producer = node := Fin.ext hproducer
    exact ⟨actual, hactual ▸ hbefore, heq ▸ hsem⟩

omit [DecidableEq (L.Val ty)] in
theorem priorHonestCoordinates_lt (decision node : Fin G.nodeCount)
    (hnode : node ∈ supported.priorHonestCoordinates focal decision) :
    node.val < decision.val := by
  classical
  obtain ⟨opening, hbefore, hsem⟩ :=
    supported.priorHonestCoordinates_opening focal decision node hnode
  have hread := (supported.graphWF opening (G.nodeRow opening)
    (G.nodes_get?_nodeRow opening)).1 (G.nodeTarget node)
    (by simp only [hsem, NodeSem.reads, Finset.mem_singleton])
  have hlt : node.val < opening.val := by
    simpa only [Graph.fieldAvailableBefore, G.field?_nodeTarget (G.nodes_get?_nodeRow node),
      decide_eq_true_eq] using hread
  omega

/-- Supply only source-earlier disclosed values to fixed-seed replay. Every
other assignment coordinate is filled with the fixed fallback. The native seed
is shared across all calls; replay never receives future source secrets. -/
def extractedChoice (decision : Fin G.nodeCount)
    (visible : supported.priorHonestCoordinates focal decision → L.Val ty)
    (fallback : L.Val ty) : L.Val ty := by
  classical
  exact (supported.resolvingBinding nullValue window
    (fun node => if h : node ∈ supported.priorHonestCoordinates focal decision then
      visible ⟨node, h⟩ else fallback) focal deviator environment schedule decision).getD fallback

/-- Fixed-seed extraction exactly recovers the native first registration,
using a fallback only for absence. The proof removes every future coordinate
from replay, not just from its returned value's type. -/
theorem extractedChoice_eq_binding (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard) (fallback : L.Val ty) :
    supported.extractedChoice nullValue window focal deviator environment schedule decision
        (fun node => values node.val) fallback =
      (supported.resolvingBinding nullValue window values focal
        deviator environment schedule decision).getD fallback := by
  classical
  unfold extractedChoice
  apply congrArg (fun value : Option (L.Val ty) => value.getD fallback)
  apply supported.resolvingBinding_read_bound nullValue window _ focal
    deviator environment schedule decision guard hdecision values
  intro who hwho node hknown
  exact dif_pos ⟨who, hwho, hknown⟩

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.resolvingBinding_read_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.resolvingBinding_read_bound

/-- info: 'Vegas.EventGraph.SealedFragment.extractedChoice_eq_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.extractedChoice_eq_binding
