/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseEmbedding
import Interaction.ReactivePolicy

/-! # Representing covered policies in a finite menu

The total representation chooses a default only at inputs where coverage fails.
Local coverage gives exact response laws. An admissibility certificate extends
this equality to every legal decision history and complete continuation.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

def Admissible (who : Principal) (policy : app.Policy) : Prop :=
  ∀ control, (menu.protocol initial horizon scheduler).Trace (some control) →
    control.actor = some who → ∀ action ∈
      (policy (control.execution.recall who) (control.execution.observe app who)).support,
      action ∈ menu.actions who (control.execution.recall who) (control.execution.observe app who)

open Classical in
def restrictPolicy (who : Principal) (policy : app.Policy) :
    (menu.information initial horizon scheduler).BehavioralPolicy who
  | none => PMF.pure ⟨none, rfl⟩
  | some (past, view) =>
      if covered : ∀ action ∈ (policy past view).support,
          action ∈ menu.actions who past view then
        (policy past view).bindOnSupport fun action supported =>
          PMF.pure ⟨some action, action, covered action supported, rfl⟩
      else PMF.pure ⟨some (menu.nonempty who past view).choose,
        _, (menu.nonempty who past view).choose_spec, rfl⟩

theorem embed_restrictPolicy (who : Principal) (policy : app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (covered : ∀ action ∈ (policy past view).support, action ∈ menu.actions who past view) :
    menu.embedPolicy initial horizon scheduler who
        (menu.restrictPolicy initial horizon scheduler who policy) (some (past, view)) =
      app.encodePolicy policy (some (past, view)) := by
  simp only [embedPolicy, restrictPolicy, dite_eq_left covered, map_bindOnSupport,
    PMF.pure_map, encodePolicy]
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bindOnSupport_eq_bind_of_eq_on_support _
  intro action supported
  rfl

/-- At a covered input, forgetting the finite-menu witness recovers the
original physical response law exactly. -/
theorem restrictPolicy_map_val (who : Principal) (policy : app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (covered : ∀ action ∈ (policy past view).support, action ∈ menu.actions who past view) :
    ((menu.restrictPolicy initial horizon scheduler who policy)
      (some (past, view))).map Subtype.val = (policy past view).map some := by
  simp only [restrictPolicy, dite_eq_left covered, map_bindOnSupport, PMF.pure_map]
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bindOnSupport_eq_bind_of_eq_on_support _
  intro action supported
  rfl

theorem decode_embedPolicy_covered (who : Principal)
    (policy : (menu.information initial horizon scheduler).BehavioralPolicy who)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action)
    (supported : response ∈
      (app.decodePolicy (menu.embedPolicy initial horizon scheduler who policy)
        past view).support) :
    response ∈ menu.actions who past view := by
  rw [decodePolicy, embedPolicy, PMF.map_comp, PMF.support_map] at supported
  obtain ⟨chosen, _supported, same⟩ := supported
  change chosen.1.getD ⟨none⟩ = response at same
  obtain ⟨action, member, value⟩ := chosen.2
  rw [value, Option.getD_some] at same
  exact same ▸ member

/-- Decoding any finite-menu behavioral policy and restricting it back recovers
its complete policy, including inputs outside legal histories. -/
theorem restrict_decode_embedPolicy (who : Principal)
    (policy : (menu.information initial horizon scheduler).BehavioralPolicy who) :
    menu.restrictPolicy initial horizon scheduler who
        (app.decodePolicy (menu.embedPolicy initial horizon scheduler who policy)) = policy := by
  funext info
  apply pmf_map_injective (f := menu.rawChoice initial horizon scheduler who info)
  · intro first second equal
    have values := congrArg Subtype.val equal
    exact Subtype.ext values
  · change menu.embedPolicy initial horizon scheduler who
        (menu.restrictPolicy initial horizon scheduler who
          (app.decodePolicy (menu.embedPolicy initial horizon scheduler who policy))) info = _
    cases info with
    | none =>
        rw [show menu.embedPolicy initial horizon scheduler who
            (menu.restrictPolicy initial horizon scheduler who
              (app.decodePolicy (menu.embedPolicy initial horizon scheduler who policy))) none =
            app.encodePolicy
              (app.decodePolicy (menu.embedPolicy initial horizon scheduler who policy)) none by
          simp [embedPolicy, restrictPolicy, encodePolicy, rawChoice, PMF.pure_map]]
        exact congrFun (app.encode_decodePolicy
          (menu.embedPolicy initial horizon scheduler who policy)) none
    | some data =>
        rw [menu.embed_restrictPolicy initial horizon scheduler who _ data.1 data.2
          (menu.decode_embedPolicy_covered initial horizon scheduler who policy data.1 data.2)]
        exact congrFun (app.encode_decodePolicy
          (menu.embedPolicy initial horizon scheduler who policy)) (some data)

/-- All-input coverage makes finite restriction an exact decoding inverse,
including inputs outside the legal histories used by `Admissible`. -/
theorem decode_restrictPolicy_of_covered (who : Principal) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ menu.actions who past view) :
    app.decodePolicy (menu.embedPolicy initial horizon scheduler who
      (menu.restrictPolicy initial horizon scheduler who policy)) = policy := by
  funext past view
  change ((menu.embedPolicy initial horizon scheduler who
    (menu.restrictPolicy initial horizon scheduler who policy))
      (some (past, view))).map _ = _
  rw [menu.embed_restrictPolicy initial horizon scheduler who policy past view
    (covered past view)]
  exact congrFun (congrFun (app.decode_encodePolicy policy) past) view

theorem embed_restrictPolicy_history (who : Principal) (policy : app.Policy)
    (covered : menu.Admissible initial horizon scheduler who policy)
    (history : (menu.protocol initial horizon scheduler).History) :
    menu.embedPolicy initial horizon scheduler who
        (menu.restrictPolicy initial horizon scheduler who policy)
        ((app.information initial horizon scheduler).infoOf who
          (menu.toRawTrace initial horizon scheduler history.trace)) =
      app.encodePolicy policy ((app.information initial horizon scheduler).infoOf who
        (menu.toRawTrace initial horizon scheduler history.trace)) := by
  suffices pointwise : ∀ info : app.Info, info = app.observe who history.state →
      menu.embedPolicy initial horizon scheduler who
        (menu.restrictPolicy initial horizon scheduler who policy) info =
          app.encodePolicy policy info by
    exact pointwise _ (app.info initial horizon scheduler who _)
  intro info observed
  cases info with
  | none => simp [embedPolicy, restrictPolicy, encodePolicy, rawChoice, PMF.pure_map]
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
            exact menu.embed_restrictPolicy initial horizon scheduler who policy _ _
              (covered control trace active)
          · cases observed

/-- Full support is checked at all legal decisions. The representing policy's
irrelevant default at nonexistent inputs imposes no extra obligation. -/
theorem restrictProfile_fullSupport (profile : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (profile who))
    (positive : ∀ who control,
      (menu.protocol initial horizon scheduler).Trace (some control) →
      control.actor = some who → ∀ action ∈
        menu.actions who (control.execution.recall who) (control.execution.observe app who),
        action ∈ (profile who (control.execution.recall who)
          (control.execution.observe app who)).support) :
    ∀ who (site : (menu.information initial horizon scheduler).InformationSite who)
      (choice : (menu.information initial horizon scheduler).Choice who site.1),
      choice ∈
        (menu.restrictPolicy initial horizon scheduler who (profile who) site.1).support := by
  intro who site
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active _ site history
  have observed := (menu.info initial horizon scheduler who history.1.trace).symm.trans history.2
  cases stateEq : history.1.state with
  | none =>
      rw [stateEq] at active
      cases active
  | some control =>
      rw [stateEq] at active
      have acting : control.actor = some who := active
      have traced : (menu.protocol initial horizon scheduler).Trace (some control) :=
        stateEq ▸ history.1.trace
      rw [stateEq] at observed
      change (if control.actor = some who then
        some (control.execution.recall who, control.execution.observe app who) else none) = site.1
        at observed
      rw [ite_eq_left acting] at observed
      rcases site with ⟨info, occurs⟩
      dsimp only at observed ⊢
      cases observed
      intro choice
      suffices choice.1 ∈ ((menu.restrictPolicy initial horizon scheduler who (profile who)
          (some (control.execution.recall who,
            control.execution.observe app who))).map Subtype.val).support by
        obtain ⟨other, supported, same⟩ := PMF.support_map .. ▸ this
        exact (Subtype.ext same) ▸ supported
      have member := choice.2
      obtain ⟨action, allowed, chosen⟩ := member
      rw [menu.restrictPolicy_map_val initial horizon scheduler who (profile who)
        _ _ (covered who control traced acting), chosen, PMF.support_map]
      exact ⟨action, positive who control traced acting action allowed, rfl⟩

variable [Fintype Principal]

theorem behavioralJoint_restrict (profile : Principal → app.Policy)
    (covered : ∀ who, menu.Admissible initial horizon scheduler who (profile who))
    (history : (menu.protocol initial horizon scheduler).History)
    (running : ¬ app.terminal history.state) :
    (app.information initial horizon scheduler).behavioralJoint
        (fun who => app.encodePolicy (profile who))
        (menu.toRawTrace initial horizon scheduler history.trace) running =
      ((menu.information initial horizon scheduler).behavioralJoint
        (fun who => menu.restrictPolicy initial horizon scheduler who (profile who))
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
      (fun who => menu.restrictPolicy initial horizon scheduler who (profile who))
      fuel history).map (menu.toRawHistory initial horizon scheduler) =
    (app.information initial horizon scheduler).runBehavioralFrom
      (fun who => app.encodePolicy (profile who)) fuel
      (menu.toRawHistory initial horizon scheduler history) := by
  induction fuel generalizing history with
  | zero => exact PMF.pure_map _ _
  | succ fuel ih =>
      by_cases stopped : app.terminal history.state
      · rw [InformationModel.runBehavioralFrom_of_terminal _ _ _ stopped,
          InformationModel.runBehavioralFrom_of_terminal _ _ _ stopped, PMF.pure_map]
      · rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ stopped,
          InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ stopped]
        simp only [toRawHistory]
        rw [menu.behavioralJoint_restrict initial horizon scheduler profile covered history stopped,
          PMF.map_bind, PMF.bind_map]
        apply bind_congr_on_support _
        intro joint _
        rw [map_bindOnSupport]
        apply bindOnSupport_congr _
        intro target realized
        exact ih (history.extend joint.2 realized)

end Interaction.ReactiveApplication.ResponseMenu
