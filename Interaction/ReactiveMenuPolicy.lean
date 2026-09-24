/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseEmbedding
import Interaction.ReactivePolicy

/-! # Representing covered policies in a finite menu

Coverage is required at every legal decision history, including off-path ones.
The total representation chooses a default only at inputs where coverage fails;
the admissibility certificate proves that branch unreachable in this instance.
At every legal history, response laws and complete continuation laws are exact.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

def Admissible (who : Principal) (policy : app.Policy) : Prop :=
  ∀ control, (menu.protocol initial horizon scheduler).Trace (some control) →
    control.actor = some who → ∀ action ∈
      (policy (control.execution.recall who) (control.execution.observe app who)).support,
      action ∈ menu.actions who (control.execution.recall who) (control.execution.observe app who)

open Classical in
def restrictPolicy (who : Principal) (policy : app.Policy)
    (_admissible : menu.Admissible initial horizon scheduler who policy) :
    (menu.information initial horizon scheduler).BehavioralPolicy who
  | none => FinDist.pure ⟨none, rfl⟩
  | some (past, view) =>
      if covered : ∀ action ∈ (policy past view).support,
          action ∈ menu.actions who past view then
        (policy past view).bindOnSupport fun action supported =>
          FinDist.pure ⟨some action, action, covered action supported, rfl⟩
      else FinDist.pure ⟨some (menu.nonempty who past view).choose,
        _, (menu.nonempty who past view).choose_spec, rfl⟩

theorem embed_restrictPolicy (who : Principal) (policy : app.Policy)
    (admissible : menu.Admissible initial horizon scheduler who policy)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (covered : ∀ action ∈ (policy past view).support, action ∈ menu.actions who past view) :
    menu.embedPolicy initial horizon scheduler who
        (menu.restrictPolicy initial horizon scheduler who policy admissible) (some (past, view)) =
      app.encodePolicy policy (some (past, view)) := by
  simp only [embedPolicy, restrictPolicy, dite_eq_left covered, FinDist.map_bindOnSupport,
    FinDist.map_pure, encodePolicy]
  rw [FinDist.map_eq_bind]
  apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
  intro action supported
  rfl

theorem decode_embedPolicy_covered (who : Principal)
    (policy : (menu.information initial horizon scheduler).BehavioralPolicy who)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action)
    (supported : response ∈
      (app.decodePolicy (menu.embedPolicy initial horizon scheduler who policy)
        past view).support) :
    response ∈ menu.actions who past view := by
  rw [decodePolicy, embedPolicy, FinDist.map_comp, FinDist.support_map] at supported
  obtain ⟨chosen, _supported, same⟩ := supported
  change chosen.1.getD ⟨none⟩ = response at same
  obtain ⟨action, member, value⟩ := chosen.2
  rw [value, Option.getD_some] at same
  exact same ▸ member

/-- All-input coverage makes finite restriction an exact decoding inverse,
including inputs outside the legal histories used by `Admissible`. -/
theorem decode_restrictPolicy_of_covered (who : Principal) (policy : app.Policy)
    (admissible : menu.Admissible initial horizon scheduler who policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ menu.actions who past view) :
    app.decodePolicy (menu.embedPolicy initial horizon scheduler who
      (menu.restrictPolicy initial horizon scheduler who policy admissible)) = policy := by
  funext past view
  change ((menu.embedPolicy initial horizon scheduler who
    (menu.restrictPolicy initial horizon scheduler who policy admissible))
      (some (past, view))).map _ = _
  rw [menu.embed_restrictPolicy initial horizon scheduler who policy admissible past view
    (covered past view)]
  exact congrFun (congrFun (app.decode_encodePolicy policy) past) view

theorem embed_restrictPolicy_history (who : Principal) (policy : app.Policy)
    (covered : menu.Admissible initial horizon scheduler who policy)
    (history : (menu.protocol initial horizon scheduler).History) :
    menu.embedPolicy initial horizon scheduler who
        (menu.restrictPolicy initial horizon scheduler who policy covered)
        ((app.information initial horizon scheduler).infoOf who
          (menu.toRawTrace initial horizon scheduler history.trace)) =
      app.encodePolicy policy ((app.information initial horizon scheduler).infoOf who
        (menu.toRawTrace initial horizon scheduler history.trace)) := by
  suffices pointwise : ∀ info : app.Info, info = app.observe who history.state →
      menu.embedPolicy initial horizon scheduler who
        (menu.restrictPolicy initial horizon scheduler who policy covered) info =
          app.encodePolicy policy info by
    exact pointwise _ (app.info initial horizon scheduler who _)
  intro info observed
  cases info with
  | none => simp [embedPolicy, restrictPolicy, encodePolicy, rawChoice]
  | some data =>
      rcases history with ⟨state, trace⟩
      cases state with
      | none => cases observed
      | some control =>
          change some data = (if control.actor = some who then
            some (control.execution.recall who, control.execution.observe app who) else none)
            at observed
          split at observed
          · rename_i active
            cases Option.some.inj observed
            exact menu.embed_restrictPolicy initial horizon scheduler who policy covered _ _
              (covered control trace active)
          · cases observed

variable [Fintype Principal]

theorem behavioralJoint_restrict (profile : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (profile who))
    (history : (menu.protocol initial horizon scheduler).History)
    (running : ¬ app.terminal history.state) :
    (app.information initial horizon scheduler).behavioralJoint
        (fun who => app.encodePolicy (profile who))
        (menu.toRawTrace initial horizon scheduler history.trace) running =
      ((menu.information initial horizon scheduler).behavioralJoint
        (fun who => menu.restrictPolicy initial horizon scheduler who (profile who) (covered who))
        history.trace running).map fun joint =>
          ⟨joint.1, menu.legal_raw initial horizon scheduler joint.2⟩ := by
  rw [← menu.behavioralJoint_embed]
  apply InformationModel.behavioralJoint_congr
  intro who
  exact (menu.embed_restrictPolicy_history initial horizon scheduler who (profile who)
    (covered who) history).symm

/-- Restriction changes no continuation, at any legal history or evaluation fuel.
It does not identify out-of-menu deviations with in-menu deviations. -/
theorem run_restrict (profile : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (profile who))
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (fun who => menu.restrictPolicy initial horizon scheduler who (profile who) (covered who))
      fuel history).map (menu.toRawHistory initial horizon scheduler) =
    (app.information initial horizon scheduler).runBehavioralFrom
      (fun who => app.encodePolicy (profile who)) fuel
      (menu.toRawHistory initial horizon scheduler history) := by
  induction fuel generalizing history with
  | zero => exact FinDist.map_pure _ _
  | succ fuel ih =>
      by_cases stopped : app.terminal history.state
      · rw [InformationModel.runBehavioralFrom_of_terminal _ _ _ stopped,
          InformationModel.runBehavioralFrom_of_terminal _ _ _ stopped, FinDist.map_pure]
      · rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ stopped,
          InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ stopped]
        simp only [toRawHistory]
        rw [menu.behavioralJoint_restrict initial horizon scheduler profile covered history stopped,
          FinDist.map_bind, FinDist.bind_map]
        apply FinDist.bind_congr
        intro joint _
        rw [FinDist.map_bindOnSupport]
        apply FinDist.bindOnSupport_congr
        intro target realized
        exact ih (history.extend joint.2 realized)

end Interaction.ReactiveApplication.ResponseMenu
