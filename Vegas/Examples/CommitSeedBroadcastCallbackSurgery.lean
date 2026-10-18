/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastFirstLateOccupation

/-! # Removing invisible silent callbacks preserves retained native inputs -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- Builder recall and the private knowledge of removed actors may differ.
All native preparation and the complete shared message state are retained. -/
structure CallbackAgreement (kept : Finset Player) (left right : app.Execution) : Prop where
  application : left.application = right.application
  network : left.network.publicView = right.network.publicView
  receipts : left.receipts = right.receipts
  leaked : ∀ owner ∈ kept, left.network.leaked owner = right.network.leaked owner
  ownWord : ∀ owner ∈ kept, left.recall owner = right.recall owner

namespace CallbackAgreement

theorem refl (kept : Finset Player) (execution : app.Execution) :
    CallbackAgreement kept execution execution := ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem trans {kept : Finset Player} {first middle last : app.Execution}
    (left : CallbackAgreement kept first middle) (right : CallbackAgreement kept middle last) :
    CallbackAgreement kept first last :=
  ⟨left.application.trans right.application, left.network.trans right.network,
    left.receipts.trans right.receipts, fun who member => (left.leaked who member).trans
      (right.leaked who member), fun who member => (left.ownWord who member).trans
        (right.ownWord who member)⟩

theorem physical {kept : Finset Player} {left right : app.Execution}
    (same : CallbackAgreement kept left right) :
    CallbackAgreement kept (physicalExecution left) (physicalExecution right) :=
  ⟨same.application, same.network, same.receipts, same.leaked, same.ownWord⟩

theorem input {kept : Finset Player} {left right : app.Execution}
    (same : CallbackAgreement kept left right) (owner : Player) (member : owner ∈ kept) :
    (left.recall owner, left.observe app owner) =
      (right.recall owner, right.observe app owner) := by
  have ledger := congrArg MessageNetwork.PublicView.ledger same.network
  change left.network.ledger = right.network.ledger at ledger
  apply Prod.ext (same.ownWord owner member)
  simp only [ReactiveApplication.Execution.observe, MessageNetwork.observe,
    same.application, same.receipts, same.leaked owner member, ledger]

theorem known {kept : Finset Player} {left right : app.Execution}
    (same : CallbackAgreement kept left right) (owner : Player) (member : owner ∈ kept) :
    left.network.known owner = right.network.known owner := by
  have inputs := congrArg MessageNetwork.PublicView.inputs same.network
  have ledger := congrArg MessageNetwork.PublicView.ledger same.network
  simp only [MessageNetwork.publicView] at inputs ledger
  simp only [MessageNetwork.known, inputs, ledger, same.leaked owner member]

theorem activate {kept : Finset Player} {left right : app.Execution}
    (same : CallbackAgreement kept left right) (actor : Player) (member : actor ∈ kept) :
    CallbackAgreement kept (completeActivation left actor) (completeActivation right actor) := by
  have pending := congrArg MessageNetwork.PublicView.pending same.network
  change left.network.pending = right.network.pending at pending
  have lookup : left.network.lookup = right.network.lookup := by
    funext identifier
    unfold MessageNetwork.lookup
    rw [pending]
  refine ⟨same.application, same.network, same.receipts, ?_, same.ownWord⟩
  intro observer retained
  change (left.network.learn actor (left.network.pending.map Message.id).toFinset).leaked
    observer = (right.network.learn actor (right.network.pending.map Message.id).toFinset).leaked
      observer
  by_cases active : observer = actor
  · subst observer
    simp only [MessageNetwork.learn, ite_true]
    rw [same.leaked actor member, pending, same.known actor member, lookup]
  · rw [MessageNetwork.learn_other left.network actor observer _ active,
      MessageNetwork.learn_other right.network actor observer _ active]
    exact same.leaked observer retained

theorem respond {kept : Finset Player} {left right : app.Execution}
    (same : CallbackAgreement kept left right) (actor : Player) (member : actor ∈ kept)
    (action : app.Action) :
    CallbackAgreement kept (left.respond app actor action) (right.respond app actor action) := by
  have observed := (Prod.mk.inj (same.input actor member)).2
  have pending := congrArg MessageNetwork.PublicView.pending same.network
  have ledger := congrArg MessageNetwork.PublicView.ledger same.network
  have inputs := congrArg MessageNetwork.PublicView.inputs same.network
  have serials := congrArg MessageNetwork.PublicView.nextSerial same.network
  change left.network.pending = right.network.pending at pending
  change left.network.ledger = right.network.ledger at ledger
  change left.network.inputs = right.network.inputs at inputs
  change left.network.nextSerial = right.network.nextSerial at serials
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      refine ⟨same.application, same.network, same.receipts, same.leaked, ?_⟩
      intro observer retained
      by_cases active : observer = actor
      · subst observer
        simp only [ReactiveApplication.Execution.respond, ite_true,
          same.ownWord actor member, observed]
      · rw [app.respond_recall_other _ actor observer active,
          app.respond_recall_other _ actor observer active]
        exact same.ownWord observer retained
  | some material =>
      have packet : app.packet (app.submit left.application actor material) actor
          (left.network.known actor) material =
        app.packet (app.submit right.application actor material) actor
          (right.network.known actor) material := by rw [same.application, same.known actor member]
      constructor
      · change app.submit left.application actor material =
          app.submit right.application actor material
        rw [same.application]
      · change (left.network.submit actor _).2.publicView =
          (right.network.submit actor _).2.publicView
        simp only [MessageNetwork.submit, MessageNetwork.publicView, packet,
          pending, ledger, inputs, serials]
      · exact same.receipts
      · exact same.leaked
      · intro observer retained
        by_cases active : observer = actor
        · subst observer
          simp only [ReactiveApplication.Execution.respond, ite_true, MessageNetwork.submit,
            same.ownWord actor member, observed, packet, serials]
        · rw [app.respond_recall_other _ actor observer active,
            app.respond_recall_other _ actor observer active]
          exact same.ownWord observer retained

/-- A removed actor's genuine passive sampling and silent response leave all
retained native fields and complete inputs unchanged. -/
theorem silent_other (kept : Finset Player) (execution : app.Execution) (actor : Player)
    (removed : actor ∉ kept) :
    CallbackAgreement kept (quietResponse execution actor) execution := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro observer retained
    have different : observer ≠ actor := fun equal => removed (equal ▸ retained)
    exact MessageNetwork.learn_other execution.network actor observer _ different
  · intro observer retained
    have different : observer ≠ actor := fun equal => removed (equal ▸ retained)
    exact app.respond_recall_other (completeActivation execution actor) actor observer
      different ⟨none⟩

end CallbackAgreement

private theorem physicalCallbacks_cons_intro (players : Player → app.Policy)
    (actor : Player) (owners : List Player) (execution final : app.Execution) (action : app.Action)
    (chosen : action ∈ (players actor ((completeActivation (physicalExecution execution)
      actor).recall actor) ((completeActivation (physicalExecution execution) actor).observe
        app actor)).support)
    (future : final ∈ (physicalCallbacks players owners
      ((completeActivation (physicalExecution execution) actor).respond app actor
        action)).support) :
    final ∈ (physicalCallbacks players (actor :: owners) execution).support := by
  rw [physicalCallbacks_cons, PMF.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨(completeActivation (physicalExecution execution) actor).respond app actor action,
    ?_, future⟩
  rw [ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
  change _ ∈ ((players actor _ _).map _).support
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨action, chosen, rfl⟩

/-- Filtering genuine silent callbacks creates an actual supported callback
prefix with the same retained full inputs. No foreign future policy is changed. -/
theorem physicalCallbacks_remove_silent (players : Player → app.Policy)
    (kept : Finset Player) (owners : List Player) (distinct : owners.Nodup)
    (execution target final : app.Execution) (same : CallbackAgreement kept execution target)
    (reached : final ∈ (physicalCallbacks players owners execution).support)
    (silent : ∀ actor ∈ owners, actor ∉ kept →
      ((final.recall actor).getLast?).map ReactiveApplication.PlayerEntry.action =
        some (⟨none⟩ : app.Action)) :
    ∃ next ∈ (physicalCallbacks players (owners.filter fun actor => actor ∈ kept) target).support,
      CallbackAgreement kept final next := by
  induction owners generalizing execution target with
  | nil =>
      have finalEq : final = physicalExecution execution := by
        simpa only [physicalCallbacks, commandComposition, List.map_nil, List.foldr_nil,
          PMF.pure_map, physicalExecution_idempotent, PMF.mem_support_pure_iff] using reached
      subst final
      refine ⟨physicalExecution target, ?_, same.physical⟩
      simp only [List.filter_nil, physicalCallbacks, commandComposition, List.map_nil,
        List.foldr_nil, PMF.pure_map, physicalExecution_idempotent, PMF.mem_support_pure_iff]
  | cons actor owners ih =>
      have noRepeat := List.nodup_cons.mp distinct
      obtain ⟨action, chosen, future⟩ := physicalCallbacks_cons_support players actor owners
        execution final reached
      have tailSilent : ∀ owner ∈ owners, owner ∉ kept →
          ((final.recall owner).getLast?).map ReactiveApplication.PlayerEntry.action =
            some (⟨none⟩ : app.Action) := fun owner member =>
        silent owner (List.mem_cons_of_mem actor member)
      by_cases retained : actor ∈ kept
      · have activeSame := same.physical.activate actor retained
        have actionPossible : action ∈ (players actor
            ((completeActivation (physicalExecution target) actor).recall actor)
            ((completeActivation (physicalExecution target) actor).observe app actor)).support := by
          have input := activeSame.input actor retained
          rw [← (Prod.mk.inj input).1, ← (Prod.mk.inj input).2]
          exact chosen
        obtain ⟨next, supported, finalSame⟩ := ih noRepeat.2
          ((completeActivation (physicalExecution execution) actor).respond app actor action)
          ((completeActivation (physicalExecution target) actor).respond app actor action)
          (activeSame.respond actor retained action) future tailSilent
        refine ⟨next, ?_, finalSame⟩
        simp only [List.filter_cons, decide_eq_true retained, ite_true]
        exact physicalCallbacks_cons_intro players actor _ target next action actionPossible
          supported
      · have last := silent actor (List.mem_cons_self ..) retained
        have recallEq := physicalCallbacks_no_own_response players owners actor noRepeat.1
          ((completeActivation (physicalExecution execution) actor).respond app actor action)
          final future
        obtain ⟨emitted, word⟩ := app.respond_recall_entry
          (completeActivation (physicalExecution execution) actor) actor action
        rw [recallEq, word, List.getLast?_append_of_ne_nil _ (by simp),
          List.getLast?_singleton, Option.map_some] at last
        have actionEq : action = ⟨none⟩ := Option.some.inj last
        subst action
        have afterSame := (CallbackAgreement.silent_other kept (physicalExecution execution)
          actor retained).trans same.physical
        obtain ⟨next, supported, finalSame⟩ := ih noRepeat.2 _ (physicalExecution target)
          afterSame future tailSilent
        refine ⟨next, ?_, finalSame⟩
        simpa only [List.filter_cons, decide_eq_false retained, Bool.false_eq_true, ite_false,
          physicalCallbacks, physicalExecution_idempotent] using supported

end Vegas.Examples.CommitSeedBroadcast
