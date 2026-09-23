/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveMenusLaw
import GameTheoryExtensions.Protocol.BehavioralContinuation
import Mathlib.Tactic.IntervalCases

/-! # Adaptive reactive deviations attain both residual benchmarks -/

noncomputable section

namespace VegasTests.ReactiveMenus

open GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

def preferredValue (preferOne : Bool) : Int := if preferOne then 1 else 2
def preferredSlot (preferOne : Bool) : Nat := if preferOne then 0 else 1
def openingPacket (preferOne : Bool) : Payload graph :=
  .opening 1 ((), .prepared (preferredSlot preferOne)) ⟨.int, preferredValue preferOne⟩
def openingAction (preferOne : Bool) : app.Action :=
  ⟨default, some (.submit ⟨openingPacket preferOne, none⟩)⟩
def selectionAction (preferOne bit : Bool) : app.Action :=
  if preferOne == bit then openingAction preferOne else ⟨default, none⟩

def observedSignal (view : app.PlayerView) : Bool :=
  view.messages.inbox.head?.any (fun message => message.id = ((), 0))

/-- The policy uses the received packet and public grant, without accessing
the network's pending pool, scheduler cursor, or unobserved random choice. -/
def recoveryPolicy (preferOne : Bool) : app.Policy := fun _ view =>
  FinDist.pure (if view.application.publicView.serviceGrant == some 1 ||
      preferOne == observedSignal view then openingAction preferOne else ⟨default, none⟩)

theorem recovery_at_response (preferOne bit : Bool) :
    recoveryPolicy preferOne ((beforeResponse bit).recall ())
      ((beforeResponse bit).observe app ()) = FinDist.pure (selectionAction preferOne bit) := by
  cases preferOne <;> cases bit <;> rfl

theorem recovery_selects (preferOne bit : Bool) :
    selectedId (response bit (selectionAction preferOne bit)).network =
        ((), preferredSlot preferOne) ∧
      selectedValue bit (selectionAction preferOne bit) = preferredValue preferOne := by
  cases preferOne <;> cases bit <;> exact ⟨rfl, rfl⟩

private def sampleRecord (execution : app.Execution) : app.Execution :=
  record execution (.application (.executeSample 0)) execution
private def waitRecord (execution : app.Execution) : app.Execution :=
  record execution .wait execution

private def snapshot (preferOne bit : Bool) (stage : Nat) : app.Execution :=
  let s3 := selected bit (selectionAction preferOne bit)
  let s4 := included s3 ((), if preferOne then 1 else 0)
  let s5 := sampleRecord s4
  let s6 := grant s5 1
  let s7 := (activate s6).respond app () (openingAction preferOne)
  let s8 := waitRecord s7
  let s9 := waitRecord s8
  let s10 := waitRecord s9
  let s11 := waitRecord s10
  match stage with
  | 0 => contested
  | 1 => delivered contested bit
  | 2 => response bit (selectionAction preferOne bit)
  | 3 => s3
  | 4 => s4
  | 5 => s5
  | 6 => s6
  | 7 => s7
  | 8 => s8
  | 9 => s9
  | 10 => s10
  | 11 => s11
  | _ + 12 => included s11 ((), if preferOne == bit then 3 else 2)

private theorem binding_ready (preferOne bit : Bool) :
    (snapshot preferOne bit 2).application.config.cut.Ready 0 := by
  cases preferOne <;> cases bit <;> decide

private def boundApplication (preferOne bit : Bool) : State graph :=
  let before := (snapshot preferOne bit 2).application
  let candidate := ((), Slot.prepared (preferredSlot preferOne))
  { (before.complete 0 (binding_ready preferOne bit)
      (.success (preferredValue preferOne)) (.success (preferredValue preferOne))) with
    accepted := Function.update before.accepted (.inr 0) (some candidate)
    candidates := before.candidates.freeze candidate }

private theorem binding_handler (preferOne bit : Bool) (serial : Nat) :
    handle runtime (snapshot preferOne bit 2).application
      ⟨((), serial), .commitment 0 ((), .prepared (preferredSlot preferOne))⟩ =
        some (boundApplication preferOne bit) := by
  have law := handle_commitment_eq runtime (snapshot preferOne bit 2).application
    ((), serial) 0 ((), .prepared (preferredSlot preferOne)) () .int rfl rfl rfl
    (binding_ready preferOne bit) (by
      cases preferOne <;> cases bit <;> change 0 < 2 <;> decide) rfl rfl
    (by cases preferOne <;> cases bit <;> rfl) (by
      intro field
      cases field with
      | inl index => exact Fin.elim0 index
      | inr event => cases preferOne <;> cases bit <;> exact nofun)
  have value : (snapshot preferOne bit 2).application.bindingResult
      ((), .prepared (preferredSlot preferOne)) .int =
        PublicationResult.success (preferredValue preferOne) := by
    cases preferOne <;> cases bit <;> rfl
  simpa only [value, cast_eq, boundApplication] using law

private theorem included_application (execution : app.Execution) (id : MessageId Unit)
    (message : Message Unit (Payload graph)) (found : execution.network.lookup id = some message) :
    (included execution id).application = (handle runtime execution.application message).getD
      execution.application := by
  simp only [included, record, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, found]
  rfl

private theorem bound_application (preferOne bit : Bool) :
    (snapshot preferOne bit 3).application = boundApplication preferOne bit := by
  have pending : (snapshot preferOne bit 2).network.lookup ((), preferredSlot preferOne) =
      some ⟨((), preferredSlot preferOne),
        .commitment 0 ((), .prepared (preferredSlot preferOne))⟩ := by
    cases preferOne <;> cases bit <;> rfl
  change (included (snapshot preferOne bit 2)
    (selectedId (response bit (selectionAction preferOne bit)).network)).application = _
  rw [(recovery_selects preferOne bit).1, included_application _ _ _ pending,
    binding_handler, Option.getD_some]

private theorem bound_not_ready (preferOne bit : Bool) :
    ¬ (boundApplication preferOne bit).config.cut.Ready 0 := by
  intro ready
  apply ready.1
  change 0 ∈ insert 0 _
  exact Finset.mem_insert_self _ _

private theorem leftover_application (preferOne bit : Bool) :
    (snapshot preferOne bit 4).application = boundApplication preferOne bit := by
  have pending : (snapshot preferOne bit 3).network.lookup ((), if preferOne then 1 else 0) =
      some ⟨((), if preferOne then 1 else 0),
        .commitment 0 ((), .prepared (if preferOne then 1 else 0))⟩ := by
    cases preferOne <;> cases bit <;> rfl
  have rejected : handle runtime (snapshot preferOne bit 3).application
      ⟨((), if preferOne then 1 else 0),
        .commitment 0 ((), .prepared (if preferOne then 1 else 0))⟩ = none := by
    rw [bound_application]
    simp only [handle, dite_eq_right (bound_not_ready preferOne bit)]
  change (included (snapshot preferOne bit 3) _).application = _
  rw [included_application _ _ _ pending, rejected, Option.getD_none,
    bound_application]

private def disclosureApplication (preferOne bit : Bool) : State graph :=
  { boundApplication preferOne bit with serviceGrant := some 1 }

private theorem disclosure_application (preferOne bit : Bool) :
    (snapshot preferOne bit 11).application = disclosureApplication preferOne bit := by
  change { (snapshot preferOne bit 4).application with serviceGrant := some 1 } = _
  rw [leftover_application]
  rfl

private theorem publication_ready (preferOne bit : Bool) :
    (disclosureApplication preferOne bit).config.cut.Ready 1 := by
  cases preferOne <;> cases bit <;> decide

private theorem publication_handler (preferOne bit : Bool) (serial : Nat) :
    handle runtime (snapshot preferOne bit 11).application
      ⟨((), serial), openingPacket preferOne⟩ =
        some ((disclosureApplication preferOne bit).complete 1 (publication_ready preferOne bit)
          true (.success (preferredValue preferOne))) := by
  rw [disclosure_application]
  apply handle_opening_eq runtime (disclosureApplication preferOne bit)
    ((), serial) 1 ((), .prepared (preferredSlot preferOne)) () .int PendingMenus.binding []
    rfl rfl rfl (publication_ready preferOne bit)
  · cases preferOne <;> cases bit <;> change 0 < 2 <;> decide
  · rfl
  · rfl
  · simp only [disclosureApplication, boundApplication, Function.update_self]
  · cases preferOne <;> cases bit <;> rfl
  · exact EventGraph.Config.complete_output_same _ _ _ _ _
  · change EventGraph.EventCode.resolveOutput? PendingMenus.binding [] true
      (disclosureApplication preferOne bit).config.store = _
    simp only [EventGraph.EventCode.resolveOutput?, EventGraph.FieldRef.get?,
      EventGraph.Config.store, disclosureApplication, boundApplication, State.complete,
      EventGraph.Config.complete_output_same, bind, Option.bind_some,
      EventGraph.GuardCheck.allAccepted?]
    rfl

private theorem publication_snapshot (preferOne bit : Bool) :
    (snapshot preferOne bit 12).application.config.outputs 1 =
      some (.success (preferredValue preferOne)) := by
  have pending : (snapshot preferOne bit 11).network.lookup
      ((), if preferOne == bit then 3 else 2) =
      some ⟨((), if preferOne == bit then 3 else 2), openingPacket preferOne⟩ := by
    cases preferOne <;> cases bit <;> rfl
  change (included (snapshot preferOne bit 11) _).application.config.outputs 1 = _
  rw [included_application _ _ _ pending, publication_handler, Option.getD_some]
  exact EventGraph.Config.complete_output_same _ _ _ _ _

private def suffixCommand (preferOne bit : Bool) : Nat → app.Command
  | 3 => .include ((), if preferOne then 1 else 0)
  | 4 => .application (.executeSample 0)
  | 5 => .application (.grant 1)
  | 6 => .activate ()
  | 11 => .include ((), if preferOne == bit then 3 else 2)
  | _ => .wait

private theorem suffix_scheduler (preferOne bit : Bool) (stage : Nat)
    (lower : 3 ≤ stage) (upper : stage < 12) :
    scheduler (snapshot preferOne bit stage).environmentRecall
      ((snapshot preferOne bit stage).observeEnvironment app) =
        FinDist.pure (suffixCommand preferOne bit stage) := by
  interval_cases stage <;> cases preferOne <;> cases bit
  all_goals first
    | rfl
    | (change (FinDist.pure (NetworkChoice.wait : NetworkChoice Unit)).map _ = _
       rw [FinDist.map_pure]; rfl)

private theorem sample_step (execution : app.Execution)
    (blocked : ¬ execution.application.config.cut.Ready 0) :
    execution.environmentStep app (.application (.executeSample 0)) =
      FinDist.pure (sampleRecord execution) := by
  change ((environmentStep runtime execution.application (.executeSample 0)).map _).map _ = _
  rw [environmentStep_executeSample_of_not_ready runtime _ 0 blocked]
  simp only [FinDist.map_pure]
  rfl

private theorem suffix_round (preferOne bit : Bool) (stage : Nat)
    (lower : 3 ≤ stage) (upper : stage < 12) :
    app.round scheduler (fun _ => recoveryPolicy preferOne) (snapshot preferOne bit stage) =
      FinDist.pure (snapshot preferOne bit (stage + 1)) := by
  rw [ReactiveApplication.round, suffix_scheduler preferOne bit stage lower upper,
    FinDist.pure_bind, ReactiveApplication.dispatch]
  interval_cases stage <;> simp only [suffixCommand]
  · rw [include_step, FinDist.pure_bind]
    rfl
  · rw [sample_step _ (by rw [leftover_application]; exact bound_not_ready preferOne bit),
      FinDist.pure_bind]
    rfl
  · rw [grant_step, FinDist.pure_bind]
    rfl
  · rw [activate_step, FinDist.pure_bind]
    change (recoveryPolicy preferOne _ _).map _ = _
    have action : recoveryPolicy preferOne
        ((activate (snapshot preferOne bit 6)).recall ())
        ((activate (snapshot preferOne bit 6)).observe app ()) =
          FinDist.pure (openingAction preferOne) := by
      simp only [recoveryPolicy]
      rfl
    rw [action, FinDist.map_pure]
    rfl
  all_goals first
    | (rw [include_step, FinDist.pure_bind]; rfl)
    | (simp only [ReactiveApplication.Execution.environmentStep,
        FinDist.map_pure, FinDist.pure_bind]; rfl)

private theorem recovery_suffix (preferOne bit : Bool) (count : Nat) (small : count ≤ 9) :
    app.runRounds scheduler (fun _ => recoveryPolicy preferOne) count
      (snapshot preferOne bit 3) = FinDist.pure (snapshot preferOne bit (3 + count)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [app.runRounds_add,
        ih (by omega), FinDist.pure_bind, ReactiveApplication.runRounds,
        suffix_round preferOne bit (3 + count) (by omega) (by omega), FinDist.pure_bind]
      rfl

private theorem recovery_twelve (preferOne : Bool) :
    app.runRounds scheduler (fun _ => recoveryPolicy preferOne) 12 contested =
      (FinDist.uniformOfFintype (α := Bool)).map (fun bit => snapshot preferOne bit 12) := by
  rw [show 12 = 3 + 9 from rfl, app.runRounds_add, first_three_rounds,
    FinDist.bind_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro bit _
  rw [recovery_at_response, FinDist.map_pure, FinDist.pure_bind]
  exact recovery_suffix preferOne bit 9 (by omega)

theorem recovery_rounds_value (preferOne : Bool) (extra : Nat) :
    (app.runRounds scheduler (fun _ => recoveryPolicy preferOne) (12 + extra) contested).expect
      (fun final => PendingMenus.publicUtility preferOne (final.application.config.outputs 1)) =
        2 := by
  trans (app.runRounds scheduler (fun _ => recoveryPolicy preferOne)
    (12 + extra) contested).expect (fun _ => (2 : ℝ))
  swap
  · exact FinDist.expect_const _ _
  apply FinDist.expect_congr
  intro final supported
  rw [app.runRounds_add, recovery_twelve, FinDist.bind_map, FinDist.support_bind] at supported
  obtain ⟨bit, _, suffix⟩ := Set.mem_iUnion₂.mp supported
  have stored := ((runtime.reactiveStoreInvariant (.inr 1)
    (.success (preferredValue preferOne))).policyInvariant app
      (fun _ => recoveryPolicy preferOne)).runRounds scheduler extra _ final
        (publication_snapshot preferOne bit) suffix
  change final.application.config.outputs 1 = some (.success (preferredValue preferOne)) at stored
  rw [stored]
  cases preferOne <;> norm_num [preferredValue, PendingMenus.publicUtility]

end VegasTests.ReactiveMenus
