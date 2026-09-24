/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAliasLaw
import Interaction.ReactiveRecallEntries

/-! # Selecting private aliases from one reference recall

The selector is a proof strategy for analyzing a fixed raw information fiber.
It uses the next reference response when that response is currently legal and
normalizes to the already selected source choice. Otherwise it uses the
canonical representative. Every selection therefore has the same normalized
choice; the reference recall does not change the runtime compiler.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization) (raw : app.ResponseMenu)
  (stable : ∀ who past view,
    raw.actions who (normal.recall who past) view = raw.actions who past view)
  (closed : ∀ who past view response, response ∈ raw.actions who past view →
    normal.action who past view response ∈ raw.actions who past view)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

def selectChoice (who : Principal) (reference : List app.PlayerEntry) (observed : app.Info)
    (chosen : ((normal.menu raw).information initial horizon scheduler).Choice who
      (normal.info who observed)) :
    (raw.information initial horizon scheduler).Choice who observed := by
  classical
  cases observed with
  | none => exact normal.canonicalChoice raw stable closed initial horizon scheduler who none chosen
  | some data =>
      exact if entry : reference[data.1.length]?.isSome then
        let response := (reference[data.1.length]?.get entry).action
        if usable : response ∈ raw.actions who data.1 data.2 ∧
            some (normal.action who data.1 data.2 response) = chosen.1 then
          ⟨some response, response, usable.1, rfl⟩
        else normal.canonicalChoice raw stable closed initial horizon scheduler who
          (some data) chosen
      else normal.canonicalChoice raw stable closed initial horizon scheduler who (some data) chosen

@[simp] theorem choice_selectChoice (who : Principal) (reference : List app.PlayerEntry)
    (observed : app.Info)
    (chosen : ((normal.menu raw).information initial horizon scheduler).Choice who
      (normal.info who observed)) :
    normal.choice raw stable initial horizon scheduler who observed
        (normal.selectChoice raw stable closed initial horizon scheduler who reference observed
          chosen) = chosen := by
  classical
  cases observed with
  | none => exact normal.choice_canonicalChoice raw stable closed initial horizon scheduler who _ _
  | some data =>
      dsimp only [selectChoice]
      split
      · split
        · rename_i available
          apply Subtype.ext
          exact available.2
        · exact normal.choice_canonicalChoice raw stable closed initial horizon scheduler who _ _
      · exact normal.choice_canonicalChoice raw stable closed initial horizon scheduler who _ _

theorem selectChoice_uses_reference (who : Principal) (reference past : List app.PlayerEntry)
    (view : app.PlayerView) (entry : app.PlayerEntry)
    (next : reference[past.length]? = some entry)
    (member : entry.action ∈ raw.actions who past view)
    (chosen : ((normal.menu raw).information initial horizon scheduler).Choice who
      (normal.info who (some (past, view))))
    (same : some (normal.action who past view entry.action) = chosen.1) :
    (normal.selectChoice raw stable closed initial horizon scheduler who reference
      (some (past, view)) chosen).1 = some entry.action := by
  classical
  simp only [selectChoice, next, Option.isSome_some, dite_true, Option.get_some, member,
    same, and_self]

def selectorPolicy (who : Principal) (reference : List app.PlayerEntry)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who) :
    (raw.information initial horizon scheduler).BehavioralPolicy who := fun observed =>
  (source (normal.info who observed)).map
    (normal.selectChoice raw stable closed initial horizon scheduler who reference observed)

theorem selectorPolicy_project (who : Principal) (reference : List app.PlayerEntry)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (observed : app.Info) :
    ((normal.selectorPolicy raw stable closed initial horizon scheduler who reference source)
      observed).map (normal.choice raw stable initial horizon scheduler who observed) =
        source (normal.info who observed) := by
  rw [selectorPolicy, FinDist.map_comp]
  change (source (normal.info who observed)).map
    (fun chosen => normal.choice raw stable initial horizon scheduler who observed
      (normal.selectChoice raw stable closed initial horizon scheduler who reference observed
        chosen)) = _
  simp only [choice_selectChoice]
  exact FinDist.map_id _

theorem selectorPolicy_supported_reference (who : Principal)
    (reference past : List app.PlayerEntry) (view : app.PlayerView) (entry : app.PlayerEntry)
    (next : reference[past.length]? = some entry)
    (member : entry.action ∈ raw.actions who past view)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (response : app.Action)
    (supported : some response ∈
      (((normal.selectorPolicy raw stable closed initial horizon scheduler who reference source)
        (some (past, view))).map Subtype.val).support)
    (same : normal.action who past view response = normal.action who past view entry.action) :
    response = entry.action := by
  rw [selectorPolicy, FinDist.map_comp, FinDist.support_map] at supported
  obtain ⟨chosen, _supported, chosenEq⟩ := supported
  change (normal.selectChoice raw stable closed initial horizon scheduler who reference
    (some (past, view)) chosen).1 = some response at chosenEq
  have projects := congrArg Subtype.val
    (normal.choice_selectChoice raw stable closed initial horizon scheduler who reference
      (some (past, view)) chosen)
  rw [normal.choice_val] at projects
  change ((normal.selectChoice raw stable closed initial horizon scheduler who reference
    (some (past, view)) chosen).1).map (normal.action who past view) = chosen.1 at projects
  rw [chosenEq, Option.map_some, same] at projects
  have selected := normal.selectChoice_uses_reference raw stable closed initial horizon scheduler
    who reference past view entry next member chosen projects
  exact Option.some.inj (chosenEq.symm.trans selected)

omit [DecidableEq Principal] in
@[simp] theorem recall_length (who : Principal) (past : List app.PlayerEntry) :
    (normal.recall who past).length = past.length := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      simp only [recall_append_action, List.length_append, List.length_singleton, ih]

omit [DecidableEq Principal] in
theorem recall_getElem? (who : Principal) (past : List app.PlayerEntry) (index : Nat) :
    (normal.recall who past)[index]? = past[index]?.map (fun entry =>
      { entry with action := normal.action who (past.take index) entry.beforeView entry.action }) :=
    by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [recall_append_action]
      by_cases inside : index < past.length
      · rw [List.getElem?_append_left (by simpa only [recall_length] using inside),
          List.getElem?_append_left inside, List.take_append_of_le_length inside.le, ih]
      · have outside : past.length ≤ index := Nat.le_of_not_gt inside
        rw [List.getElem?_append_right (by simpa only [recall_length] using outside),
          List.getElem?_append_right outside, recall_length]
        by_cases last : index = past.length
        · subst index
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.map_some, List.take_left]
        · have positive : 0 < index - past.length := by omega
          obtain ⟨offset, offsetEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
          rw [offsetEq]
          simp only [List.getElem?_cons_succ, List.getElem?_nil, Option.map_none]

/-- If selected raw responses project to the reference record, every entry is
the reference entry. The test for legal aliases is discharged at each recorded
view; no source-compatible hidden history is singled out. -/
theorem selector_reconstructs_recall (who : Principal) (reference past : List app.PlayerEntry)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (normalized : normal.recall who past = normal.recall who reference)
    (legal : ∀ index (inside : index < reference.length),
      reference[index].action ∈ raw.actions who (reference.take index) reference[index].beforeView)
    (played : ∀ index (inside : index < past.length), some past[index].action ∈
      (((normal.selectorPolicy raw stable closed initial horizon scheduler who reference source)
        (some (past.take index, past[index].beforeView))).map Subtype.val).support) :
    past = reference := by
  have lengths : past.length = reference.length := by
    simpa only [recall_length] using congrArg List.length normalized
  have agree : ∀ index (inside : index < past.length) (other : index < reference.length),
      past[index] = reference[index] := by
    intro index
    induction index using Nat.strong_induction_on with
    | h index ih =>
        intro inside other
        have earlier : past.take index = reference.take index := by
          apply List.ext_getElem
          · simp only [List.length_take, lengths]
          · intro before pastBound referenceBound
            rw [List.length_take] at pastBound referenceBound
            have first := lt_min_iff.mp pastBound
            have second := lt_min_iff.mp referenceBound
            simpa only [List.getElem_take] using ih before first.1 first.2 second.2
        have transformed := congrArg (fun remembered => remembered[index]?) normalized
        rw [normal.recall_getElem?, normal.recall_getElem?] at transformed
        simp only [List.getElem?_eq_getElem inside, List.getElem?_eq_getElem other,
          Option.map_some] at transformed
        have entries := Option.some.inj transformed
        have views := congrArg PlayerEntry.beforeView entries
        have emissions := congrArg PlayerEntry.emitted entries
        have actions := congrArg PlayerEntry.action entries
        change normal.action who (past.take index) past[index].beforeView past[index].action =
          normal.action who (reference.take index) reference[index].beforeView
            reference[index].action at actions
        change past[index].beforeView = reference[index].beforeView at views
        change past[index].emitted = reference[index].emitted at emissions
        have admitted := legal index other
        rw [← earlier, ← views] at actions admitted
        have next : reference[(past.take index).length]? = some reference[index] := by
          simpa only [List.length_take, Nat.min_eq_left inside.le] using
            List.getElem?_eq_getElem other
        have selected := normal.selectorPolicy_supported_reference raw stable closed
          initial horizon scheduler who reference (past.take index) past[index].beforeView
            reference[index] next admitted source past[index].action (played index inside) actions
        have entryExt (first second : app.PlayerEntry)
            (viewEq : first.beforeView = second.beforeView)
            (actionEq : first.action = second.action)
            (emittedEq : first.emitted = second.emitted) : first = second := by
          rcases first with ⟨firstView, firstAction, firstEmission⟩
          rcases second with ⟨secondView, secondAction, secondEmission⟩
          cases viewEq
          cases actionEq
          cases emittedEq
          rfl
        exact entryExt _ _ views selected emissions
  exact List.ext_getElem lengths agree

/-- A positive selector history in the projected information fiber has the
exact reference recall. The source fiber is therefore not narrowed by fixing
the focal player's private alias choices. -/
theorem selector_information_fiber [Fintype Principal]
    (who : Principal) (reference : (raw.protocol initial horizon scheduler).History)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (referenceInfo : (raw.information initial horizon scheduler).infoOf who reference.trace =
      some (past, view))
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (profile : ∀ player, (raw.information initial horizon scheduler).BehavioralPolicy player)
    (own : profile who =
      normal.selectorPolicy raw stable closed initial horizon scheduler who past source)
    (history : (raw.protocol initial horizon scheduler).History)
    (positive : 0 < (raw.information initial horizon scheduler).historyReachProbability
      profile history)
    (projected : normal.info who
      ((raw.information initial horizon scheduler).infoOf who history.trace) =
        normal.info who (some (past, view))) :
    (raw.information initial horizon scheduler).infoOf who history.trace = some (past, view) := by
  cases observed : (raw.information initial horizon scheduler).infoOf who history.trace with
  | none => rw [observed] at projected; cases projected
  | some data =>
      rcases data with ⟨remembered, seen⟩
      rw [observed] at projected
      have equality := Option.some.inj projected
      have recalls := congrArg Prod.fst equality
      have views := congrArg Prod.snd equality
      have same : remembered = past := by
        apply normal.selector_reconstructs_recall raw stable closed initial horizon scheduler
          who past remembered source recalls
        · exact raw.recall_entry_legal initial horizon scheduler who reference past view
            referenceInfo
        · intro index inside
          have supported := raw.recall_entry_supported initial horizon scheduler profile who
            history positive remembered seen observed index inside
          rw [own] at supported
          exact supported
      cases same
      cases views
      rfl

end Interaction.ReactiveApplication.SubmissionNormalization
