/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAliasImplementation
import Interaction.ReactiveMenuPolicy

/-! # Finite-menu legality of realized alias deviations

At every input, each private implementation state selects responses admitted
by the normalized menu. If restored private names match the observed recall,
menu stability transfers legality from that raw recall. Otherwise the total
implementation uses the observed recall directly. Conditioning private state
on past play preserves this pointwise support property.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization) (raw : app.ResponseMenu)
  (stable : ∀ who past view,
    raw.actions who (normal.recall who past) view = raw.actions who past view)

include stable in
theorem aliasImplementation_respond_admissible
    (who : Principal) (reference : List app.PlayerEntry) (policy : app.Policy)
    (admitted : ∀ past view response, response ∈ (policy past view).support →
      response ∈ raw.actions who past view)
    (names : List app.Action) (past : List app.PlayerEntry) (view : app.PlayerView)
    (result : app.Action × List app.Action)
    (supported : result ∈
      ((normal.aliasImplementation who reference policy).respond names (past, view)).support) :
    result.1 ∈ (normal.menu raw).actions who past view := by
  classical
  by_cases usable : names.length = past.length ∧
      normal.recall who (restoreActions past names) = past
  · dsimp only [aliasImplementation] at supported
    rw [ite_eq_left usable, FinDist.support_map] at supported
    obtain ⟨response, supported, rfl⟩ := supported
    apply (normal.menu_mem raw who past view _).mpr
    refine ⟨response, ?_, ?_⟩
    · have menus := stable who (restoreActions past names) view
      rw [usable.2] at menus
      exact menus.symm ▸ admitted _ _ response supported
    · change normal.action who past view response =
        normal.action who (restoreActions past names) view response
      calc
        _ = normal.action who (normal.recall who (restoreActions past names)) view response :=
          congrArg (fun remembered => normal.action who remembered view response) usable.2.symm
        _ = _ := normal.action_recall who (restoreActions past names) view response
  · dsimp only [aliasImplementation] at supported
    rw [ite_eq_right usable, FinDist.support_map] at supported
    obtain ⟨response, supported, rfl⟩ := supported
    exact (normal.menu_mem raw who past view _).mpr
      ⟨response, admitted _ _ response supported, rfl⟩

include stable in
/-- A raw policy respecting its finite menu has a behavioral realization
respecting the normalized menu at every recall and current observation. -/
theorem aliasImplementation_policy_admissible
    (who : Principal) (reference : List app.PlayerEntry) (policy : app.Policy)
    (admitted : ∀ past view response, response ∈ (policy past view).support →
      response ∈ raw.actions who past view)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action)
    (supported : response ∈
      ((normal.aliasImplementation who reference policy).policy past view).support) :
    response ∈ (normal.menu raw).actions who past view := by
  rw [Implementation.policy_eq, FinDist.support_map] at supported
  obtain ⟨result, reached, rfl⟩ := supported
  obtain ⟨names, _remembered, supported⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  exact normal.aliasImplementation_respond_admissible raw stable who reference policy admitted
    names past view result supported

include stable in
theorem aliasImplementation_admissible [DecidableEq Principal]
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) (reference : List app.PlayerEntry) (policy : app.Policy)
    (admitted : ∀ past view response, response ∈ (policy past view).support →
      response ∈ raw.actions who past view) :
    (normal.menu raw).Admissible initial horizon scheduler who
      (normal.aliasImplementation who reference policy).policy := by
  intro control _history _active response supported
  exact normal.aliasImplementation_policy_admissible raw stable who reference policy admitted
    _ _ response supported

variable [DecidableEq Principal]
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- Simulate a whole raw continuation deviation, retaining its private action
names inside the strategy and choosing only normalized finite-menu responses. -/
def aliasDeviation (who : Principal) (reference : List app.PlayerEntry)
    (alternative : (raw.information initial horizon scheduler).BehavioralPolicy who) :
    ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who :=
  (normal.menu raw).restrictPolicy initial horizon scheduler who
    (normal.aliasImplementation who reference
      (app.decodePolicy (raw.embedPolicy initial horizon scheduler who alternative))).policy
    (normal.aliasImplementation_admissible raw stable initial horizon scheduler who reference _
      (raw.decode_embedPolicy_covered initial horizon scheduler who alternative))

theorem decode_aliasDeviation (who : Principal) (reference : List app.PlayerEntry)
    (alternative : (raw.information initial horizon scheduler).BehavioralPolicy who) :
    app.decodePolicy ((normal.menu raw).embedPolicy initial horizon scheduler who
      (normal.aliasDeviation raw stable initial horizon scheduler who reference alternative)) =
        (normal.aliasImplementation who reference
          (app.decodePolicy (raw.embedPolicy initial horizon scheduler who alternative))).policy :=
  (normal.menu raw).decode_restrictPolicy_of_covered initial horizon scheduler who _ _
    (normal.aliasImplementation_policy_admissible raw stable who reference _
      (raw.decode_embedPolicy_covered initial horizon scheduler who alternative))

end Interaction.ReactiveApplication.SubmissionNormalization
