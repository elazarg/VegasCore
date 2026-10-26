/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketHonestDecision

/-! # Source turns at decoded views

**One event per source action.** A source action encodes at no more than one
event of a program (`Vegas.encodeEventAction?_event_unique`): a commitment
names a fresh variable, so no later commitment names it again, and a reveal
removes its commitment from the open names, to which only fresh variables are
added later.

**The decoded view's turn.** At a view decoded at a count, every action the
intended game offers encodes at the event of that count, and a player whose
turn the view shows owns that event (`Vegas.decodeViewPrefix?_intended`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Unique

/-- A commitment action encodes only at a commitment to a variable not yet in
the context. -/
theorem encodeEventAction?_commit_fresh : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (event : Fin (eventCount program))
    {owner : Player} {name : VarId} {payload : L.Ty} {choice : PublicationResult (L.Val payload)},
    (encodeEventAction? program event (.commit owner name payload choice)).isSome →
      name ∉ Γ.map Prod.fst
  | _, _, .ret _, event, _, _, _, _, _ => nomatch event
  | _, _, .sample _ _ _ next, event, _, _, _, _, encoded => by
      cases event using Fin.cases with
      | zero => simp [encodeEventAction?] at encoded
      | succ tail =>
          simp only [encodeEventAction?, Fin.cases_succ] at encoded
          exact fun member =>
            encodeEventAction?_commit_fresh next tail encoded (List.mem_cons_of_mem _ member)
  | _, _, .commit _ _ fresh _ next, event, _, _, _, _, encoded => by
      cases event using Fin.cases with
      | zero =>
          simp only [encodeEventAction?, Fin.cases_zero] at encoded
          split_ifs at encoded with ownerEq nameEq
          · subst nameEq
            exact fresh
          all_goals cases encoded
      | succ tail =>
          simp only [encodeEventAction?, Fin.cases_succ] at encoded
          exact fun member =>
            encodeEventAction?_commit_fresh next tail encoded (List.mem_cons_of_mem _ member)
  | _, _, .reveal _ _ _ _ _ _ next, event, _, _, _, _, encoded => by
      cases event using Fin.cases with
      | zero => simp [encodeEventAction?] at encoded
      | succ tail =>
          simp only [encodeEventAction?, Fin.cases_succ] at encoded
          exact fun member =>
            encodeEventAction?_commit_fresh next tail encoded (List.mem_cons_of_mem _ member)

/-- A reveal action encodes only at a reveal of an open commitment, or of one
committed later. -/
theorem encodeEventAction?_reveal_open : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (event : Fin (eventCount program))
    {owner : Player} {name : VarId} {disclose : Bool},
    (encodeEventAction? program event (.reveal owner name disclose)).isSome →
      name ∈ O ∨ name ∉ Γ.map Prod.fst
  | _, _, .ret _, event, _, _, _, _ => nomatch event
  | _, _, .sample _ _ _ next, event, _, _, _, encoded => by
      cases event using Fin.cases with
      | zero => simp [encodeEventAction?] at encoded
      | succ tail =>
          simp only [encodeEventAction?, Fin.cases_succ] at encoded
          rcases encodeEventAction?_reveal_open next tail encoded with opened | later
          · exact Or.inl opened
          · exact Or.inr fun member => later (List.mem_cons_of_mem _ member)
  | _, _, .commit _ _ fresh _ next, event, _, _, _, encoded => by
      cases event using Fin.cases with
      | zero => simp [encodeEventAction?] at encoded
      | succ tail =>
          simp only [encodeEventAction?, Fin.cases_succ] at encoded
          rcases encodeEventAction?_reveal_open next tail encoded with opened | later
          · rcases Finset.mem_insert.mp opened with same | opened
            · subst same
              exact Or.inr fresh
            · exact Or.inl opened
          · exact Or.inr fun member => later (List.mem_cons_of_mem _ member)
  | _, _, .reveal _ _ _ _ _ unresolved next, event, _, _, _, encoded => by
      cases event using Fin.cases with
      | zero =>
          simp only [encodeEventAction?, Fin.cases_zero] at encoded
          split_ifs at encoded with ownerEq nameEq
          · subst nameEq
            exact Or.inl unresolved
          all_goals cases encoded
      | succ tail =>
          simp only [encodeEventAction?, Fin.cases_succ] at encoded
          rcases encodeEventAction?_reveal_open next tail encoded with opened | later
          · exact Or.inl (Finset.mem_of_mem_erase opened)
          · exact Or.inr fun member => later (List.mem_cons_of_mem _ member)

/-- **One event per source action.** A source action encodes at no more than
one event of a program. -/
theorem encodeEventAction?_event_unique : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (first second : Fin (eventCount program))
    (action : OwnAction Player L),
    (encodeEventAction? program first action).isSome →
      (encodeEventAction? program second action).isSome → first = second
  | _, _, .ret _, first, _, _, _, _ => nomatch first
  | _, _, .sample _ _ _ next, first, second, action, firstEncoded, secondEncoded => by
      cases first using Fin.cases with
      | zero => simp [encodeEventAction?] at firstEncoded
      | succ firstTail =>
          cases second using Fin.cases with
          | zero => simp [encodeEventAction?] at secondEncoded
          | succ secondTail =>
              simp only [encodeEventAction?, Fin.cases_succ] at firstEncoded secondEncoded
              exact congrArg Fin.succ (encodeEventAction?_event_unique next firstTail
                secondTail action firstEncoded secondEncoded)
  | _, _, .commit _ _ _ _ next, first, second, action, firstEncoded, secondEncoded => by
      cases first using Fin.cases with
      | zero =>
          cases second using Fin.cases with
          | zero => rfl
          | succ secondTail =>
              simp only [encodeEventAction?, Fin.cases_zero] at firstEncoded
              simp only [encodeEventAction?, Fin.cases_succ] at secondEncoded
              cases action with
              | reveal => simp at firstEncoded
              | commit =>
                  simp only at firstEncoded
                  split_ifs at firstEncoded with ownerEq nameEq
                  · subst nameEq
                    exact (encodeEventAction?_commit_fresh next secondTail secondEncoded
                      List.mem_cons_self).elim
                  all_goals cases firstEncoded
      | succ firstTail =>
          cases second using Fin.cases with
          | zero =>
              simp only [encodeEventAction?, Fin.cases_succ] at firstEncoded
              simp only [encodeEventAction?, Fin.cases_zero] at secondEncoded
              cases action with
              | reveal => simp at secondEncoded
              | commit =>
                  simp only at secondEncoded
                  split_ifs at secondEncoded with ownerEq nameEq
                  · subst nameEq
                    exact (encodeEventAction?_commit_fresh next firstTail firstEncoded
                      List.mem_cons_self).elim
                  all_goals cases secondEncoded
          | succ secondTail =>
              simp only [encodeEventAction?, Fin.cases_succ] at firstEncoded secondEncoded
              exact congrArg Fin.succ (encodeEventAction?_event_unique next firstTail
                secondTail action firstEncoded secondEncoded)
  | _, _, .reveal _ _ _ _ source _ next, first, second, action, firstEncoded, secondEncoded => by
      cases first using Fin.cases with
      | zero =>
          cases second using Fin.cases with
          | zero => rfl
          | succ secondTail =>
              simp only [encodeEventAction?, Fin.cases_zero] at firstEncoded
              simp only [encodeEventAction?, Fin.cases_succ] at secondEncoded
              cases action with
              | commit => simp at firstEncoded
              | reveal =>
                  simp only at firstEncoded
                  split_ifs at firstEncoded with ownerEq nameEq
                  · subst nameEq
                    rcases encodeEventAction?_reveal_open next secondTail secondEncoded with
                      opened | later
                    · exact (Finset.notMem_erase _ _ opened).elim
                    · exact (later (List.mem_cons_of_mem _ source.mem_map_fst)).elim
                  all_goals cases firstEncoded
      | succ firstTail =>
          cases second using Fin.cases with
          | zero =>
              simp only [encodeEventAction?, Fin.cases_succ] at firstEncoded
              simp only [encodeEventAction?, Fin.cases_zero] at secondEncoded
              cases action with
              | commit => simp at secondEncoded
              | reveal =>
                  simp only at secondEncoded
                  split_ifs at secondEncoded with ownerEq nameEq
                  · subst nameEq
                    rcases encodeEventAction?_reveal_open next firstTail firstEncoded with
                      opened | later
                    · exact (Finset.notMem_erase _ _ opened).elim
                    · exact (later (List.mem_cons_of_mem _ source.mem_map_fst)).elim
                  all_goals cases secondEncoded
          | succ secondTail =>
              simp only [encodeEventAction?, Fin.cases_succ] at firstEncoded secondEncoded
              exact congrArg Fin.succ (encodeEventAction?_event_unique next firstTail
                secondTail action firstEncoded secondEncoded)

end Unique

section View

variable {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}

/-- **The decoded view's turn.** At a view decoded at a count, every action the
intended game offers encodes at the event of that count, and a player whose
turn the view shows owns that event. -/
theorem decodeViewPrefix?_intended (who : Player) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (own : List (OwnAction Player L))
      (view : ProtocolView who program),
      decodeViewPrefix? who program refs outputs count store own = some view →
      (∀ action ∈ ProtocolView.intendedAvailable who program view,
        ∃ event : Fin (eventCount program), event.val = count ∧
          (encodeEventAction? program event action).isSome) ∧
      (ProtocolView.actor who program view = some who →
        ∃ event : Fin (eventCount program), event.val = count ∧
          eventOwner? program event = some who) ∧
      (∀ event : Fin (eventCount program), event.val = count →
        ProtocolView.actor who program view = eventOwner? program event)
  | 0, _, _, .ret _, _, _, _, _, _, _ =>
      ⟨fun _ member => member.elim, fun turn => (by cases turn), fun event => Fin.elim0 event⟩
  | 0, _, _, .sample _ _ _ _, _, _, _, _, view, decoded => by
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
      refine ⟨fun _ member => member.elim, fun turn => (by cases turn), fun event named => ?_⟩
      obtain rfl : event = ⟨0, Nat.succ_pos _⟩ := Fin.ext named
      rfl
  | 0, _, _, .commit _ _ _ _ _, _, _, _, _, view, decoded => by
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
      refine ⟨fun action member => ?_, fun turn => ⟨⟨0, Nat.succ_pos _⟩, rfl, turn⟩,
        fun event named => ?_⟩
      · obtain ⟨value, _, rfl⟩ := member
        exact ⟨⟨0, Nat.succ_pos _⟩, rfl, by simp [encodeEventAction?]⟩
      · obtain rfl : event = ⟨0, Nat.succ_pos _⟩ := Fin.ext named
        rfl
  | 0, _, _, .reveal _ _ _ _ _ _ _, _, _, _, _, view, decoded => by
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
      refine ⟨fun action member => ?_, fun turn => ⟨⟨0, Nat.succ_pos _⟩, rfl, turn⟩,
        fun event named => ?_⟩
      · obtain rfl := Set.mem_singleton_iff.mp member
        exact ⟨⟨0, Nat.succ_pos _⟩, rfl, by simp [encodeEventAction?]⟩
      · obtain rfl : event = ⟨0, Nat.succ_pos _⟩ := Fin.ext named
        rfl
  | _ + 1, _, _, .ret _, _, _, _, _, _, decoded => by cases decoded
  | count + 1, _, _, .sample _ _ _ next, _, _, _, _, view, decoded => by
      obtain ⟨later, laterDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
      obtain ⟨available, owned, actorEq⟩ :=
        decodeViewPrefix?_intended who count next _ _ _ _ later laterDecoded
      refine ⟨fun action member => ?_, fun turn => ?_, fun event named => ?_⟩
      · obtain ⟨event, named, encoded⟩ := available action member
        exact ⟨event.succ, by simp [named], by simpa [encodeEventAction?] using encoded⟩
      · obtain ⟨event, named, ownerEq⟩ := owned turn
        exact ⟨event.succ, by simp [named], by simpa [eventOwner?] using ownerEq⟩
      · cases event using Fin.cases with
        | zero => cases named
        | succ tail =>
            simp only [eventOwner?, Fin.cases_succ]
            exact actorEq tail (by simpa using named)
  | count + 1, _, _, .commit _ _ _ _ next, _, _, _, _, view, decoded => by
      obtain ⟨later, laterDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
      obtain ⟨available, owned, actorEq⟩ :=
        decodeViewPrefix?_intended who count next _ _ _ _ later laterDecoded
      refine ⟨fun action member => ?_, fun turn => ?_, fun event named => ?_⟩
      · obtain ⟨event, named, encoded⟩ := available action member
        exact ⟨event.succ, by simp [named], by simpa [encodeEventAction?] using encoded⟩
      · obtain ⟨event, named, ownerEq⟩ := owned turn
        exact ⟨event.succ, by simp [named], by simpa [eventOwner?] using ownerEq⟩
      · cases event using Fin.cases with
        | zero => cases named
        | succ tail =>
            simp only [eventOwner?, Fin.cases_succ]
            exact actorEq tail (by simpa using named)
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, _, _, _, _, view, decoded => by
      obtain ⟨later, laterDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
      obtain ⟨available, owned, actorEq⟩ :=
        decodeViewPrefix?_intended who count next _ _ _ _ later laterDecoded
      refine ⟨fun action member => ?_, fun turn => ?_, fun event named => ?_⟩
      · obtain ⟨event, named, encoded⟩ := available action member
        exact ⟨event.succ, by simp [named], by simpa [encodeEventAction?] using encoded⟩
      · obtain ⟨event, named, ownerEq⟩ := owned turn
        exact ⟨event.succ, by simp [named], by simpa [eventOwner?] using ownerEq⟩
      · cases event using Fin.cases with
        | zero => cases named
        | succ tail =>
            simp only [eventOwner?, Fin.cases_succ]
            exact actorEq tail (by simpa using named)

/-- **The intended game offers no failure.** Every action it offers commits a
successful value or discloses. -/
theorem intendedAvailable_success (who : Player) : ∀ {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (view : ProtocolView who program)
    (action : OwnAction Player L), action ∈ ProtocolView.intendedAvailable who program view →
      (∀ owner name payload, action ≠ .commit owner name payload .failure) ∧
        ∀ owner name, action ≠ .reveal owner name false
  | _, _, .ret _, _, _, member => member.elim
  | _, _, .sample _ _ _ next, view, action, member => by
      cases view with
      | inl _ => exact member.elim
      | inr later => exact intendedAvailable_success who next later action member
  | _, _, .commit _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          obtain ⟨value, _, rfl⟩ := member
          exact ⟨fun _ _ _ same => (by cases same), fun _ _ same => (by cases same)⟩
      | inr later => exact intendedAvailable_success who next later action member
  | _, _, .reveal _ _ _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          obtain rfl := Set.mem_singleton_iff.mp member
          exact ⟨fun _ _ _ same => (by cases same), fun _ _ same => (by cases same)⟩
      | inr later => exact intendedAvailable_success who next later action member

end View

section Native

private theorem eq_pure_of_support_subset {α : Type} (law : PMF α) (a : α)
    (only : ∀ x ∈ law.support, x = a) : law = PMF.pure a := by
  have support : law.support = {a} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, only⟩
    obtain ⟨x, member⟩ := law.support_nonempty
    exact only x member ▸ member
  ext x
  by_cases same : x = a
  · subst same
    rw [(PMF.apply_eq_one_iff _ _).mpr support, PMF.pure_apply_self]
  · rw [PMF.pure_apply_of_ne _ _ same, (PMF.apply_eq_zero_iff _ _).mpr (by
      rw [support]
      exact same)]

variable {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The view of a decoded point is the view decoded at its rank. -/
private theorem decodeViewPrefix?_rank (who : Player)
    (execution : (application setup runtime leaks).Execution) (rank : Nat)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point) :
    decodeViewPrefix? who setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
      rank ((graph setup).playerStore who execution.application.config.store)
      (decodeCompletions setup.program
        (((graph setup).ownCompletions who execution.application.config.history).map
          (setup.eventGraph.fromModeCompletion .sequential))) =
      some (ProtocolState.observe who setup.program point) := by
  refine (decodeViewPrefix?_playerStore (graph := graph setup) who rank setup.program _ _ _
    _).trans ?_
  refine (congrArg (fun own => decodeViewPrefix? who setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
    rank execution.application.config.store (decodeCompletions setup.program own))
    (ownCompletions_fromModeCompletion setup (mode := .sequential) who
      execution.application.config.history)).trans ?_
  exact decodeViewPrefix?_eq_observe who rank setup.program _ [] _ _ _ _ point decoded

/-- A source choice of the intended game at a point's view: an action the
intended game offers when the view shows the player's turn, no action
otherwise. -/
private theorem intendedChoice_cases (who : Player) (point : ProtocolState setup.program)
    (intended : setup.intendedModel.Choice who (setup.protocolObserve who (some point))) :
    (∃ action, intended.1 = some action ∧
      ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
        some who ∧
      action ∈ ProtocolView.intendedAvailable who setup.program
        (ProtocolState.observe who setup.program point)) ∨
    (intended.1 = none ∧
      ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) ≠
        some who) := by
  have legal := intended.2
  change intended.1 ∈ setup.intendedMenu who (some (ProtocolState.observe who setup.program
    point)) at legal
  change ProtocolView.intendedMenu who setup.program _ intended.1 at legal
  rcases chosen : intended.1 with _ | action
  · rw [chosen] at legal
    exact Or.inr ⟨rfl, legal⟩
  · rw [chosen] at legal
    exact Or.inl ⟨action, rfl, legal.1, legal.2⟩

/-- **As-if-honest play encodes at the turn.** At an execution decoding at its
completed prefix, at the player's turn at an event, every source choice
as-if-honest play supports encodes at the event. -/
theorem asIfHonestProfile_encodes (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (execution : (application setup runtime leaks).Execution) (rank : Nat)
    (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (past : List (application setup runtime leaks).PlayerEntry) (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (choice : Option (OwnAction Player L))
    (supported : choice ∈ (asIfHonestProfile setup runtime leaks assessment who
      (some (past, execution.observe (application setup runtime leaks) who))).support) :
    (choice.bind (encodeEventAction? setup.program event)).isSome := by
  obtain ⟨intended, _, rfl⟩ := (mem_support_asIfHonestProfile_observe setup runtime leaks
    assessment who
    execution rank ordered point decoded past choice).mp supported
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have atRank := (ready_iff_rank setup _ rank ordered event).mp ready
  obtain ⟨available, _, actorEq⟩ := decodeViewPrefix?_intended who rank setup.program _ _ _ _ _
    (decodeViewPrefix?_rank (runtime := runtime) who execution rank point decoded)
  rcases intendedChoice_cases who point intended with
    ⟨action, chosen, _, offered⟩ | ⟨_, notTurn⟩
  · rw [chosen]
    obtain ⟨site, named, encoded⟩ := available action offered
    have same : site = event := Fin.ext (named.trans atRank.symm)
    subst same
    exact encoded
  · exact (notTurn ((actorEq event atRank).trans
      ((eventOwner?_eq_actor setup.program event).trans owned))).elim

/-- **No action without a turn.** At an execution decoding at its completed
prefix, where the player has no turn, as-if-honest play chooses no action. -/
theorem asIfHonestProfile_eq_pure_none (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (execution : (application setup runtime leaks).Execution) (rank : Nat)
    (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (past : List (application setup runtime leaks).PlayerEntry)
    (noTurn : execution.application.publicView.ownTurn? who = none) :
    asIfHonestProfile setup runtime leaks assessment who
        (some (past, execution.observe (application setup runtime leaks) who)) = PMF.pure none := by
  refine eq_pure_of_support_subset _ _ fun choice supported => ?_
  obtain ⟨intended, _, rfl⟩ := (mem_support_asIfHonestProfile_observe setup runtime leaks
    assessment who
    execution rank ordered point decoded past _).mp supported
  obtain ⟨_, owned, _⟩ := decodeViewPrefix?_intended who rank setup.program _ _ _ _ _
    (decodeViewPrefix?_rank (runtime := runtime) who execution rank point decoded)
  rcases intendedChoice_cases who point intended with
    ⟨action, _, isTurn, _⟩ | ⟨chosen, _⟩
  · obtain ⟨event, atRank, ownerEq⟩ := owned isTurn
    have ready : execution.application.publicView.EventReady event :=
      (execution.application.publicView_eventReady event).mpr
        ((ready_iff_rank setup _ rank ordered event).mpr atRank)
    have actorEq : (graph setup).actor? event = some who :=
      (eventOwner?_eq_actor setup.program event).symm.trans ownerEq
    unfold PublicView.ownTurn? at noTurn
    exact absurd (decide_eq_true ⟨ready, actorEq⟩)
      (List.find?_eq_none.mp noTurn event (List.mem_finRange event))
  · exact chosen

/-- **As-if-honest play chooses no failure.** At an execution decoding at its
completed prefix, every source action as-if-honest play supports commits a
successful value or discloses. -/
theorem asIfHonestProfile_success (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (execution : (application setup runtime leaks).Execution) (rank : Nat)
    (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (past : List (application setup runtime leaks).PlayerEntry) (action : OwnAction Player L)
    (supported : some action ∈ (asIfHonestProfile setup runtime leaks assessment who
      (some (past, execution.observe (application setup runtime leaks) who))).support) :
    (∀ owner name payload, action ≠ .commit owner name payload .failure) ∧
      ∀ owner name, action ≠ .reveal owner name false := by
  obtain ⟨intended, _, same⟩ := (mem_support_asIfHonestProfile_observe setup runtime leaks
    assessment who
    execution rank ordered point decoded past _).mp supported
  rcases intendedChoice_cases who point intended with
    ⟨chosen, choiceEq, _, offered⟩ | ⟨choiceEq, _⟩
  · rw [choiceEq] at same
    have equal := Option.some.inj same
    subst equal
    exact intendedAvailable_success who setup.program _ _ offered
  · rw [choiceEq] at same
    cases same

end Native

end Vegas
