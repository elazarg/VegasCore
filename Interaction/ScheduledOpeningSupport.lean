/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ScheduledOpening
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # Full support before a scheduled opening

The support proof ranges over every lawful waiting history of the phase.
Earlier responses need not have been supported by the artificial waiting
policy: the scheduled family is dormant before its offset, so its posterior
there is its original mixing law even at an impossible earlier transcript.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

theorem policyMixture_posterior_support_snoc {Index : Type} (initial : PMF Index)
    (policies : Index → app.Policy) (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (index : Index) (retained : index ∈
      ((app.policyMixture initial policies).posterior past).support)
    (possible : entry.action ∈ (policies index past entry.beforeView).support) :
    index ∈ ((app.policyMixture initial policies).posterior (past ++ [entry])).support := by
  classical
  let joint := ((app.policyMixture initial policies).posterior past).bind fun selected =>
    (policies selected past entry.beforeView).map fun action => (action, selected)
  have produced : (entry.action, index) ∈ joint.support := by
    simp only [joint, PMF.support_bind, Set.mem_iUnion]
    refine ⟨index, retained, ?_⟩
    rw [PMF.support_map]
    exact ⟨entry.action, possible, rfl⟩
  have meets : ∃ pair ∈ Prod.fst ⁻¹' {entry.action}, pair ∈ joint.support :=
    ⟨(entry.action, index), rfl, produced⟩
  rw [Implementation.posterior_snoc]
  change index ∈ ((fiberConditional joint Prod.fst entry.action).map Prod.snd).support
  rw [fiberConditional, dite_eq_left meets, PMF.support_map]
  refine ⟨(entry.action, index), ?_, rfl⟩
  apply pmf_toReal_pos_iff.mp
  rw [toReal_filter_apply, ite_eq_left
    (show (entry.action, index) ∈ Prod.fst ⁻¹' {entry.action} from rfl)]
  exact div_pos (pmf_toReal_pos_iff.mpr produced) (toOuterMeasure_toReal_pos _ meets)

theorem policyMixture_posterior_support_append {Index : Type} (initial : PMF Index)
    (policies : Index → app.Policy) (past suffix : List app.PlayerEntry) (index : Index)
    (retained : index ∈ ((app.policyMixture initial policies).posterior past).support)
    (possible : ∀ before entry after, suffix = before ++ entry :: after →
      entry.action ∈ (policies index (past ++ before) entry.beforeView).support) :
    index ∈ ((app.policyMixture initial policies).posterior (past ++ suffix)).support := by
  induction suffix generalizing past with
  | nil => simpa only [List.append_nil] using retained
  | cons entry suffix ih =>
      have first := app.policyMixture_posterior_support_snoc initial policies past entry index
        retained (by simpa only [List.append_nil] using possible [] entry suffix rfl)
      have tail := ih (past ++ [entry]) first (by
        intro before next after split
        have earlier := possible (entry :: before) next after (by simp [split])
        simpa only [List.cons_append, List.nil_append, List.append_assoc] using earlier)
      simpa only [List.append_assoc, List.singleton_append] using tail

theorem policyMixture_action_support {Index : Type} (initial : PMF Index)
    (policies : Index → app.Policy) (past : List app.PlayerEntry) (view : app.PlayerView)
    (index : Index) (action : app.Action)
    (retained : index ∈ ((app.policyMixture initial policies).posterior past).support)
    (possible : action ∈ (policies index past view).support) :
    action ∈ ((app.policyMixture initial policies).policy past view).support := by
  rw [app.policyMixture_policy]
  simp only [PMF.support_bind, Set.mem_iUnion]
  exact ⟨index, retained, possible⟩

/-- A future selected slot, or never opening, stays possible after every
lawful prefix of waiting responses. -/
theorem scheduledMixture_retains_future {slots : Nat}
    (initial : PMF (Option (Fin slots))) (offset : Nat)
    (opening : app.Action) (waiting : app.Policy)
    (past suffix : List app.PlayerEntry) (atStart : past.length = offset)
    (selected : Option (Fin slots)) (initially : selected ∈ initial.support)
    (future : ∀ slot, selected = some slot → suffix.length ≤ slot.val)
    (lawful : ∀ before entry after, suffix = before ++ entry :: after →
      entry.action ∈ (waiting (past ++ before) entry.beforeView).support) :
    selected ∈ ((app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure opening) waiting)).posterior (past ++ suffix)).support := by
  let policies := fun selected : Option (Fin slots) =>
    app.scheduledPolicy offset selected (fun _ _ => PMF.pure opening) waiting
  have dormant := app.policyMixture_posterior_dormant initial policies waiting offset
    (fun selected before view earlier =>
      app.scheduledPolicy_before offset selected _ waiting before view earlier)
    past atStart.le
  apply app.policyMixture_posterior_support_append initial policies past suffix selected
  · rw [dormant]
    exact initially
  · intro before entry after split
    have earlier : before.length < suffix.length := by
      have := congrArg List.length split
      simp only [List.length_append, List.length_cons] at this
      omega
    have unused : selected.map (fun slot => offset + slot.val) ≠
        some (past ++ before).length := by
      cases selected with
      | none => simp
      | some slot =>
          have later := future slot rfl
          intro equal
          have count := Option.some.inj equal
          simp only [List.length_append, atStart] at count
          omega
    simpa only [policies, scheduledPolicy, ite_eq_right unused] using
      lawful before entry after split

/-- Before the first opening, every current opening and every lawful waiting
response has positive probability under a fully supported timing mixture. -/
theorem scheduledMixture_before_open_full {slots : Nat}
    (initial : PMF (Option (Fin slots))) (full : FullSupport initial) (offset : Nat)
    (opening : app.Action) (waiting : app.Policy)
    (past suffix : List app.PlayerEntry) (atStart : past.length = offset)
    (inside : suffix.length < slots)
    (lawful : ∀ before entry after, suffix = before ++ entry :: after →
      entry.action ∈ (waiting (past ++ before) entry.beforeView).support)
    (view : app.PlayerView) :
    let law := (app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure opening) waiting)).policy (past ++ suffix) view
    opening ∈ law.support ∧
      ∀ action ∈ (waiting (past ++ suffix) view).support, action ∈ law.support := by
  dsimp only
  let slot : Fin slots := ⟨suffix.length, inside⟩
  have selected := app.scheduledMixture_retains_future initial offset opening waiting
    past suffix atStart (some slot) (full _) (by intro chosen same; cases same; exact le_rfl)
      lawful
  have never := app.scheduledMixture_retains_future initial offset opening waiting
    past suffix atStart none (full _) (by simp) lawful
  constructor
  · apply app.policyMixture_action_support initial _ _ view (some slot) opening selected
    simp only [scheduledPolicy, Option.map_some, List.length_append, atStart, slot,
      ↓reduceIte, PMF.mem_support_pure_iff _ _]
  · intro action supported
    apply app.policyMixture_action_support initial _ _ view none action never
    simpa only [scheduledPolicy, Option.map_none, reduceCtorEq, ↓reduceIte] using supported

end Interaction.ReactiveApplication
