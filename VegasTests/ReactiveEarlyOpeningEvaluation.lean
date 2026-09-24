/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveEarlyOpening
import Vegas.Pending.ReactiveStateInvariant

/-! # Exact laws under uniform inclusion at fixed service times -/

noncomputable section

namespace VegasTests.ReactiveEarlyOpening

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction
open Vegas Vegas.EventGraphRuntime

def half {α : Type*} (first second : FinDist α) : FinDist α :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) first second

def third {α : Type*} (first rest : FinDist α) : FinDist α :=
  FinDist.mix (1 / 3) (by norm_num) (by norm_num) first rest

def bindingAction : app.Action :=
  ⟨some (.submit ⟨⟨.commitment 0 ((), .prepared 1), some ⟨.int, 0⟩⟩, .none⟩)⟩

def earlyOpening : app.Action :=
  ⟨some (.submit (disclosureSubmission (.opening 1 ((), .prepared 0) ⟨.int, 1⟩)))⟩

def firstResponse (repair : Bool) : app.Action := if repair then bindingAction else earlyOpening

def afterResponse (repair : Bool) : app.Execution :=
  (activated contested).respond app () (firstResponse repair)

def selectedId (fresh : Bool) : MessageId Unit := ((), if fresh then 2 else 0)

def included (repair fresh : Bool) : app.Execution :=
  let before := afterResponse repair
  { before.includePending app (selectedId fresh) with
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment app, .include (selectedId fresh)⟩] }

def granted (repair fresh : Bool) : app.Execution :=
  let before := included repair fresh
  { before with
    application := { before.application with serviceGrant := some 1 }
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment app, .application (.grant 1)⟩] }

def finalOpening (fresh : Bool) : app.Action :=
  ⟨some (.submit
    (disclosureSubmission
      (.opening 1 ((), .prepared (if fresh then 1 else 0)) ⟨.int, if fresh then 0 else 1⟩)))⟩

def disclosed (repair fresh : Bool) : app.Execution :=
  (activated (granted repair fresh)).respond app () (finalOpening fresh)

def finished (repair fresh : Bool) (serial : Nat) : app.Execution :=
  let before := disclosed repair fresh
  { before.includePending app ((), serial) with
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment app, .include ((), serial)⟩] }

theorem selection_pair (a b : MessageId Unit) (different : a ≠ b) :
    MessageNetwork.chooseUniform {a, b} = half (FinDist.pure (some a))
      (FinDist.pure (some b)) := by
  rw [MessageNetwork.chooseUniform_insert {b} (Finset.singleton_nonempty b) a (by
    simpa using different), MessageNetwork.chooseUniform_singleton]
  simp only [Finset.card_singleton, Nat.cast_one]
  norm_num [half]

theorem binding_selection (repair : Bool) :
    select 0 ((afterResponse repair).observeEnvironment app) =
      if repair then half (FinDist.pure (.include ((), 0)))
        (FinDist.pure (.include ((), 2)))
      else FinDist.pure (.include ((), 0)) := by
  cases repair with
  | false =>
      change ((MessageNetwork.chooseUniform {((), 0)}).map _).map _ = _
      rw [MessageNetwork.chooseUniform_singleton, FinDist.map_pure, FinDist.map_pure]
      rfl
  | true =>
      change ((MessageNetwork.chooseUniform {((), 0), ((), 2)}).map _).map _ = _
      rw [selection_pair _ _ (by decide)]
      simp only [half, FinDist.map_mix, FinDist.map_pure]
      rfl

def candidate (fresh : Bool) : Handle graph := ((), .prepared (if fresh then 1 else 0))

def selectedValue (fresh : Bool) : Int := if fresh then 0 else 1

theorem binding_ready (repair : Bool) :
    (afterResponse repair).application.config.cut.Ready 0 := by cases repair <;> decide

def boundState (repair fresh : Bool) : State graph :=
  let before := (afterResponse repair).application
  { before.complete 0 (binding_ready repair) (.success (selectedValue fresh))
      (.success (selectedValue fresh)) with
    accepted := Function.update before.accepted (.inr 0) (some (candidate fresh))
    candidates := before.candidates.freeze (candidate fresh) }

theorem included_state (repair fresh : Bool) (possible : fresh = true → repair = true) :
    (included repair fresh).application = boundState repair fresh := by
  have pending : (afterResponse repair).network.lookup (selectedId fresh) =
      some ⟨selectedId fresh, ⟨.commitment 0 (candidate fresh), none⟩⟩ := by
    cases repair <;> cases fresh <;> first | contradiction | rfl
  have law := handle_commitment_eq runtime (afterResponse repair).application
    (selectedId fresh) 0 (candidate fresh) () .int rfl rfl rfl (binding_ready repair)
    (by cases repair <;> change 0 < 2 <;> decide) rfl rfl (by cases repair <;> rfl)
    (by
      intro field
      cases field with
      | inl impossible => exact Fin.elim0 impossible
      | inr event =>
          cases repair <;> change (none : Option (Handle graph)) ≠ some _ <;> simp)
  have meaning : (afterResponse repair).application.bindingResult (candidate fresh) .int =
      .success (selectedValue fresh) := by
    cases repair <;> cases fresh <;> first | contradiction | rfl
  dsimp only [included, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending]
  rw [pending]
  dsimp only [app, reactiveApplication]
  rw [law, meaning]
  rfl

theorem disclosed_state (repair fresh : Bool) (possible : fresh = true → repair = true) :
    (disclosed repair fresh).application =
      { boundState repair fresh with serviceGrant := some 1 } := by
  change { (included repair fresh).application with serviceGrant := some 1 } = _
  rw [included_state repair fresh possible]

theorem disclosure_ready (repair fresh : Bool) (possible : fresh = true → repair = true) :
    (disclosed repair fresh).application.config.cut.Ready 1 := by
  rw [disclosed_state repair fresh possible]
  cases repair <;> cases fresh <;> decide

theorem disclosure_timely (repair fresh : Bool) (possible : fresh = true → repair = true) :
    (disclosed repair fresh).application.WithinDeadline runtime 1 := by
  rw [disclosed_state repair fresh possible]
  cases repair <;> cases fresh <;> change 0 < 2 <;> decide

theorem final_opening_emitted (repair fresh : Bool) (possible : fresh = true → repair = true) :
    (disclosureSubmission (.opening 1 (candidate fresh) ⟨.int, selectedValue fresh⟩)).emit
      (granted repair fresh).application () ((granted repair fresh).network.known ()) =
        ⟨.opening 1 (candidate fresh) ⟨.int, selectedValue fresh⟩,
          some ⟨candidate fresh, ⟨.int, selectedValue fresh⟩⟩⟩ := by
  have meaning : (granted repair fresh).application.candidates.lookup (candidate fresh) =
      .openable ⟨.int, selectedValue fresh⟩ := by
    change (disclosed repair fresh).application.candidates.lookup _ = _
    rw [disclosed_state repair fresh possible]
    cases repair <;> cases fresh <;> first | contradiction | rfl
  have owned : (candidate fresh).1 = () := rfl
  simp [disclosureSubmission, WitnessedSubmission.emit, CommitmentCandidates.verify, meaning,
    owned]

theorem final_opening_pending (repair fresh : Bool) (possible : fresh = true → repair = true) :
    (disclosed repair fresh).network.lookup ((), 3) =
      some ⟨((), 3), ⟨.opening 1 (candidate fresh) ⟨.int, selectedValue fresh⟩,
        some ⟨candidate fresh, ⟨.int, selectedValue fresh⟩⟩⟩⟩ := by
  have emitted := final_opening_emitted repair fresh possible
  have pending : (disclosed repair fresh).network.lookup ((), 3) =
      some ⟨((), 3),
        (disclosureSubmission (.opening 1 (candidate fresh) ⟨.int, selectedValue fresh⟩)).emit
          (granted repair fresh).application () ((granted repair fresh).network.known ())⟩ := by
    cases repair <;> cases fresh <;> rfl
  rw [pending, emitted]

theorem disclosed_pending (repair fresh : Bool) (possible : fresh = true → repair = true) :
    (disclosed repair fresh).network.pending = (granted repair fresh).network.pending ++
      [⟨((), 3), ⟨.opening 1 (candidate fresh) ⟨.int, selectedValue fresh⟩,
        some ⟨candidate fresh, ⟨.int, selectedValue fresh⟩⟩⟩⟩] := by
  have emitted := final_opening_emitted repair fresh possible
  have pending : (disclosed repair fresh).network.pending =
      (granted repair fresh).network.pending ++ [⟨((), 3),
        (disclosureSubmission (.opening 1 (candidate fresh) ⟨.int, selectedValue fresh⟩)).emit
          (granted repair fresh).application () ((granted repair fresh).network.known ())⟩] := by
    cases repair <;> cases fresh <;> rfl
  rw [pending, emitted]

theorem finished_withholding (repair fresh : Bool) (possible : fresh = true → repair = true) :
    (finished repair fresh 1).application.config.outputs 1 = some .failure := by
  have pending : (disclosed repair fresh).network.lookup ((), 1) =
      some ⟨((), 1), ⟨.withhold 1, none⟩⟩ := by cases repair <;> cases fresh <;> rfl
  have ready := disclosure_ready repair fresh possible
  have timely := disclosure_timely repair fresh possible
  have remembered : (disclosed repair fresh).application.remembered 1 = none := by
    rw [disclosed_state repair fresh possible]
    cases repair <;> rfl
  have accepted := handle_withhold_unremembered_eq runtime (disclosed repair fresh).application
    ((), 1) 1 () .int PendingMenus.binding [] rfl rfl rfl ready timely rfl remembered
  dsimp only [finished, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending]
  rw [pending]
  change (((handle runtime (disclosed repair fresh).application ⟨((), 1), .withhold 1⟩).getD
    (disclosed repair fresh).application).config.outputs 1) = _
  rw [accepted]
  exact EventGraph.Config.complete_output_same ..

theorem finished_opening (repair fresh : Bool) (possible : fresh = true → repair = true)
    (serial : Nat) (pending : (disclosed repair fresh).network.lookup ((), serial) =
      some ⟨((), serial), ⟨.opening 1 (candidate fresh) ⟨.int, selectedValue fresh⟩,
        some ⟨candidate fresh, ⟨.int, selectedValue fresh⟩⟩⟩⟩) :
    (finished repair fresh serial).application.config.outputs 1 =
      some (.success (selectedValue fresh)) := by
  have associated : (disclosed repair fresh).application.accepted PendingMenus.binding.field =
      some (candidate fresh) := by
    rw [disclosed_state repair fresh possible]
    simp only [boundState, Function.update_self]
  have meaning : (disclosed repair fresh).application.candidates.lookup (candidate fresh) =
      .openable ⟨.int, selectedValue fresh⟩ := by
    rw [disclosed_state repair fresh possible]
    cases repair <;> cases fresh <;> first | contradiction | rfl
  have stored : PendingMenus.binding.get? (disclosed repair fresh).application.config.store =
      some (.success (selectedValue fresh)) := by
    rw [disclosed_state repair fresh possible]
    exact EventGraph.Config.complete_output_same ..
  have resolved : EventGraph.EventCode.resolveOutput? PendingMenus.binding [] true
      (disclosed repair fresh).application.config.store =
        some (.success (selectedValue fresh)) := by
    simp [EventGraph.EventCode.resolveOutput?, stored, EventGraph.GuardCheck.allAccepted?]
  have accepted := handle_opening_eq runtime (disclosed repair fresh).application
    ((), serial) 1 (candidate fresh) () .int PendingMenus.binding [] rfl rfl rfl
    (disclosure_ready repair fresh possible) (disclosure_timely repair fresh possible)
    rfl rfl associated (selectedValue fresh) meaning stored
    (.success (selectedValue fresh)) resolved
  dsimp only [finished, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending]
  rw [pending]
  dsimp only [app, reactiveApplication]
  rw [accepted]
  exact EventGraph.Config.complete_output_same ..

theorem repaired_opening (fresh : Bool) :
    (finished true fresh 3).application.config.outputs 1 =
      some (.success (if fresh then 0 else 1)) := by
  exact finished_opening true fresh (by simp) 3 (final_opening_pending true fresh (by simp))

theorem early_withholding :
    (finished false false 1).application.config.outputs 1 = some .failure :=
  finished_withholding false false (by simp)

theorem early_opening :
    (finished false false 2).application.config.outputs 1 = some (.success 1) :=
  finished_opening false false (by simp) 2 rfl

theorem later_opening :
    (finished false false 3).application.config.outputs 1 = some (.success 1) :=
  finished_opening false false (by simp) 3 (final_opening_pending false false (by simp))

end VegasTests.ReactiveEarlyOpening
