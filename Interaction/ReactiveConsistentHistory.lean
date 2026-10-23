/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveRecovery
import Interaction.ReactiveHistory

/-! # Full behavioral history support from consistent reactive recall -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

omit [DecidableEq Principal] in
private theorem encoded_action_law (policy : app.Policy) (info : app.Info) :
    (app.encodePolicy policy info).map Subtype.val =
      match info with
      | none => PMF.pure none
      | some (past, view) => (policy past view).map some := by
  cases info with
  | none => exact PMF.pure_map _ _
  | some input => exact PMF.map_comp _ _ _

private theorem response_supported_of_consistent (policy : app.Policy)
    (execution : app.Execution) (who : Principal) (action : app.Action)
    (consistent : policy.Consistent ((execution.respond app who action).recall who)) :
    action ∈ (policy (execution.recall who) (execution.observe app who)).support := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      have valid : policy.Consistent (execution.recall who ++
          [⟨execution.observe app who, ⟨none⟩, none⟩]) := by
        simpa only [Execution.respond, ↓reduceIte] using consistent
      exact ((Policy.consistent_snoc_iff policy _ _).mp valid).2
  | some material =>
      simp only [Execution.respond, ↓reduceIte] at consistent
      exact ((Policy.consistent_snoc_iff policy _ _).mp consistent).2

private theorem encoded_choice_supported_of_consistent_transition
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) {before after : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace before)
    (joint : Principal → Option app.Action)
    (legal : (app.protocol initial horizon scheduler).Legal before joint)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support)
    (consistent : ∀ control, after = some control →
      ∀ who, (players who).Consistent (control.execution.recall who)) (who : Principal) :
    (⟨joint who, ((app.information initial horizon scheduler).menu_adequate who trace
      (joint who)).mpr ((app.protocol initial horizon scheduler).legalOption_of_legal legal who)⟩ :
        (app.information initial horizon scheduler).Choice who
          ((app.information initial horizon scheduler).infoOf who trace)) ∈
      (app.encodePolicy (players who)
        ((app.information initial horizon scheduler).infoOf who trace)).support := by
  classical
  suffices supported : joint who ∈ ((app.encodePolicy (players who)
      ((app.information initial horizon scheduler).infoOf who trace)).map Subtype.val).support by
    obtain ⟨choice, positive, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact (Subtype.ext same : choice = ⟨joint who, _⟩) ▸ positive
  have observed : (app.information initial horizon scheduler).infoOf who trace =
      app.observe who before := app.info initial horizon scheduler who trace
  rw [encoded_action_law, observed]
  by_cases active : app.actor before = some who
  · cases before with
    | none => simp only [actor, Option.bind_none, reduceCtorEq] at active
    | some control =>
        have acting : control.actor = some who := active
        have legalChoice := (app.protocol initial horizon scheduler).legalOption_of_legal legal who
        obtain ⟨action, selected⟩ := LegalOption.exists_eq_some_of_active
          (E := app.protocol initial horizon scheduler) (joint who) legalChoice
          active
        simp only [transition, acting, selected, Option.getD_some] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        have supported := response_supported_of_consistent app (players who) control.execution who
          action (consistent _ rfl who)
        simp only [observe, acting, ↓reduceIte, PMF.mem_support_map_iff]
        exact ⟨action, supported, selected.symm⟩
  · have absent : app.observe who before = none := by
      cases before with
      | none => rfl
      | some control =>
          have inactive : control.actor ≠ some who := active
          simp only [observe, inactive, ↓reduceIte]
    have omitted := LegalOption.eq_none_of_inactive
      (E := app.protocol initial horizon scheduler) (joint who)
      ((app.protocol initial horizon scheduler).legalOption_of_legal legal who) active
    simpa only [absent, PMF.mem_support_pure_iff] using omitted

variable [Fintype Principal]

/-- A genuine reactive history whose complete player recalls are consistent
with a profile occurs in that profile's behavioral law at its exact trace depth.
The original history, including all realized commands and chance, is retained. -/
theorem history_mem_support_runBehavioral_of_consistent
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) :
    ∀ {state} (trace : (app.protocol initial horizon scheduler).Trace state),
      (∀ control, state = some control →
        ∀ who, (players who).Consistent (control.execution.recall who)) →
      (⟨state, trace⟩ : (app.protocol initial horizon scheduler).History) ∈
        ((app.information initial horizon scheduler).runBehavioral
          (fun who => app.encodePolicy (players who)) trace.length).support := by
  intro state trace
  induction trace with
  | start =>
      intro _consistent
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | @extend before after prior joint legal reached ih =>
      intro consistent
      have priorConsistent : ∀ control, before = some control →
          ∀ who, (players who).Consistent (control.execution.recall who) := by
        intro control current who
        have moved := reached
        change after ∈ (app.transition initial horizon scheduler before joint).support at moved
        rw [current] at moved
        obtain ⟨next, finalState, past⟩ := app.transition_recall_prefix initial horizon scheduler
          control after joint moved
        have valid := consistent next finalState who
        obtain ⟨tail, same⟩ := past who
        rw [← same] at valid
        exact valid.of_append
      have priorSupported := ih priorConsistent
      have draw := (app.information initial horizon scheduler).mem_support_behavioralJoint
        (fun who => app.encodePolicy (players who)) prior legal.1 joint legal
          (encoded_choice_supported_of_consistent_transition app initial horizon scheduler players
            prior joint legal reached consistent)
      change (⟨after, .extend prior joint legal reached⟩ :
          (app.protocol initial horizon scheduler).History) ∈
        ((app.information initial horizon scheduler).runBehavioralFrom
          (fun who => app.encodePolicy (players who)) (prior.length + 1)
            (app.protocol initial horizon scheduler).initHistory).support
      rw [(app.information initial horizon scheduler).runBehavioralFrom_add
        (fun who => app.encodePolicy (players who)) prior.length 1, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨⟨before, prior⟩, priorSupported, ?_⟩
      rw [(app.information initial horizon scheduler).runBehavioralFrom_succ_of_not_terminal
        (fun who => app.encodePolicy (players who)) 0 legal.1, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨⟨joint, legal⟩, draw, ?_⟩
      rw [PMF.support_bindOnSupport]
      refine Set.mem_iUnion₂.mpr ⟨after, reached, ?_⟩
      exact (PMF.mem_support_pure_iff _ _).mpr rfl

end Interaction.ReactiveApplication
