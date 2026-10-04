/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMenuRestriction
import Interaction.ReactiveMenuPolicy
import GameTheory.Protocol.RestrictionExecution

/-! # Legal physical continuations against unchanged opponents

A physical policy covered by the smaller response menu has compatible
representations in both games. Replacing one player by that policy therefore
preserves profile extension. Every resulting target continuation stays in the
embedded smaller game, even though opponents retain their original target
policies at all additional inputs.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu.IncludedIn

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  {smaller larger : app.ResponseMenu} (included : smaller.IncludedIn larger)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- Restricting one covered physical law commutes with menu inclusion. -/
theorem restrictPolicy_law (who : Principal) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ smaller.actions who past view) (info : app.Info) :
    larger.restrictPolicy initial horizon scheduler who policy info =
      (smaller.restrictPolicy initial horizon scheduler who policy info).map
        (included.choice initial horizon scheduler who info) := by
  cases info with
  | none => simp only [restrictPolicy, PMF.pure_map]; rfl
  | some input =>
      have largeCovered : ∀ response ∈ (policy input.1 input.2).support,
          response ∈ larger.actions who input.1 input.2 :=
        fun response supported => included who _ _ (covered _ _ response supported)
      simp only [restrictPolicy, dite_eq_left (covered input.1 input.2),
        dite_eq_left largeCovered, map_bindOnSupport]
      apply bindOnSupport_congr _
      intro response supported
      rw [PMF.pure_map]
      rfl

/-- Legal-history admission makes restriction to nested menus agree at every
actual smaller decision site. No coverage is required at nonexistent inputs. -/
theorem restrictProfile_extends_of_admissible
    (players : Principal → app.Policy)
    (covered : ∀ who, smaller.Admissible initial horizon scheduler who (players who)) :
    (included.actionRestriction initial horizon scheduler).ExtendsProfile
      (fun who => smaller.restrictPolicy initial horizon scheduler who (players who))
      (fun who => larger.restrictPolicy initial horizon scheduler who (players who)) := by
  intro who site
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active _ site history
  have observed := (smaller.info initial horizon scheduler who history.1.trace).symm.trans
    history.2
  cases current : history.1.state with
  | none =>
      rw [current] at active
      cases active
  | some control =>
      rw [current] at active observed
      have acting : control.actor = some who := active
      have trace : (smaller.protocol initial horizon scheduler).Trace (some control) :=
        current ▸ history.1.trace
      change (if control.actor = some who then
        some (control.execution.recall who, control.execution.observe app who) else none) =
          site.1 at observed
      rw [ite_eq_left acting] at observed
      have localCovered := covered who control trace acting
      change larger.restrictPolicy initial horizon scheduler who (players who) site.1 =
        (smaller.restrictPolicy initial horizon scheduler who (players who) site.1).map
          (included.choice initial horizon scheduler who site.1)
      rw [← observed]
      apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
      rw [larger.restrictPolicy_map_val initial horizon scheduler who (players who) _ _
        (fun response supported => included who _ _ (localCovered response supported)),
        PMF.map_comp]
      change _ = (smaller.restrictPolicy initial horizon scheduler who (players who)
        (some (control.execution.recall who, control.execution.observe app who))).map Subtype.val
      exact (smaller.restrictPolicy_map_val initial horizon scheduler who (players who) _ _
        localCovered).symm

/-- A globally legal replacement preserves the original target opponents. -/
theorem extends_restrictPolicy
    (source : ∀ who, (smaller.information initial horizon scheduler).BehavioralPolicy who)
    (target : ∀ who, (larger.information initial horizon scheduler).BehavioralPolicy who)
    (agrees : (included.actionRestriction initial horizon scheduler).ExtendsProfile source target)
    (who : Principal) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ smaller.actions who past view) :
    (included.actionRestriction initial horizon scheduler).ExtendsProfile
      (Function.update source who
        (smaller.restrictPolicy initial horizon scheduler who policy))
      (Function.update target who
        (larger.restrictPolicy initial horizon scheduler who policy)) := by
  intro actor site
  by_cases same : actor = who
  · subst actor
    simp only [Function.update_self]
    exact included.restrictPolicy_law initial horizon scheduler who policy covered site.1
  · simp only [Function.update_of_ne same]
    exact agrees actor site

variable [Fintype Principal]

/-- The complete legal continuation law uses the original opponents, including
their arbitrary responses at additional target inputs. -/
theorem runFrom_restrictPolicy
    (source : ∀ who, (smaller.information initial horizon scheduler).BehavioralPolicy who)
    (target : ∀ who, (larger.information initial horizon scheduler).BehavioralPolicy who)
    (agrees : (included.actionRestriction initial horizon scheduler).ExtendsProfile source target)
    (who : Principal) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ smaller.actions who past view)
    (fuel : Nat) (history : (smaller.protocol initial horizon scheduler).History) :
    ((smaller.information initial horizon scheduler).runBehavioralFrom
      (Function.update source who
        (smaller.restrictPolicy initial horizon scheduler who policy))
      fuel history).map (included.history initial horizon scheduler) =
    (larger.information initial horizon scheduler).runBehavioralFrom
      (Function.update target who
        (larger.restrictPolicy initial horizon scheduler who policy))
      fuel (included.history initial horizon scheduler history) :=
  (included.actionRestriction initial horizon scheduler).runFrom_law _ _
    (included.extends_restrictPolicy initial horizon scheduler source target agrees who policy
      covered) fuel history

/-- No unsupported target history can arise after a legal whole-policy
replacement at a retained history. -/
theorem runFrom_restrictPolicy_supported
    (source : ∀ who, (smaller.information initial horizon scheduler).BehavioralPolicy who)
    (target : ∀ who, (larger.information initial horizon scheduler).BehavioralPolicy who)
    (agrees : (included.actionRestriction initial horizon scheduler).ExtendsProfile source target)
    (who : Principal) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ smaller.actions who past view)
    (fuel : Nat) (history : (smaller.protocol initial horizon scheduler).History)
    (next : (larger.protocol initial horizon scheduler).History)
    (supported : next ∈ ((larger.information initial horizon scheduler).runBehavioralFrom
      (Function.update target who
        (larger.restrictPolicy initial horizon scheduler who policy))
      fuel (included.history initial horizon scheduler history)).support) :
    ∃ retained, retained ∈ ((smaller.information initial horizon scheduler).runBehavioralFrom
      (Function.update source who
        (smaller.restrictPolicy initial horizon scheduler who policy))
      fuel history).support ∧ included.history initial horizon scheduler retained = next := by
  rw [← included.runFrom_restrictPolicy initial horizon scheduler source target agrees who
    policy covered fuel history, PMF.support_map] at supported
  exact supported

/-- Evaluation of the legal replacement is the actual physical execution
against the unchanged target opponents. All private and public state is kept. -/
theorem runFrom_restrictPolicy_finish
    (source : ∀ who, (smaller.information initial horizon scheduler).BehavioralPolicy who)
    (target : ∀ who, (larger.information initial horizon scheduler).BehavioralPolicy who)
    (agrees : (included.actionRestriction initial horizon scheduler).ExtendsProfile source target)
    (who : Principal) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ smaller.actions who past view)
    (fuel : Nat) (history : (smaller.protocol initial horizon scheduler).History)
    (enough : app.rank horizon history.state ≤ fuel) :
    ((smaller.information initial horizon scheduler).runBehavioralFrom
      (Function.update source who
        (smaller.restrictPolicy initial horizon scheduler who policy))
      fuel history).map ExecutionProtocol.History.state =
      app.finish initial horizon scheduler
        (Function.update (larger.decodeProfile initial horizon scheduler target) who policy)
        history.state := by
  have law := congrArg (fun distribution => distribution.map ExecutionProtocol.History.state)
    (included.runFrom_restrictPolicy initial horizon scheduler source target agrees who
      policy covered fuel history)
  rw [PMF.map_comp] at law
  change _ = ((larger.information initial horizon scheduler).runBehavioralFrom
    (GameTheory.Profile.update
      (sig := (larger.information initial horizon scheduler).behavioralSignature) target who
      (larger.restrictPolicy initial horizon scheduler who policy))
    fuel (included.history initial horizon scheduler history)).map
      ExecutionProtocol.History.state at law
  rw [larger.run_eq_finish initial horizon scheduler _ fuel _ enough,
    larger.decodeProfile_update, larger.decode_restrictPolicy_of_covered
      initial horizon scheduler who policy
      (fun past view response supported => included who past view
        (covered past view response supported))] at law
  exact law

end Interaction.ReactiveApplication.ResponseMenu.IncludedIn
