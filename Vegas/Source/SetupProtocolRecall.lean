/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ObservationRecall
import Vegas.Source.SetupProtocol
import GameTheory.Protocol.DecisionRecall

/-! # Perfect recall of the source protocol

A source view keeps the player's own action list, and
`Vegas.SourceProgram.ProtocolView.entryView` recovers the view at the start of
every instruction already passed. The record of a player's own moves, each with
the view it was taken at, is therefore a function of the current view
(`Vegas.SourceProgram.ProtocolView.ownPlay`). Hence the setup protocol has
perfect recall, and decision recall, under every commitment interface.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

/-- The own moves taken before a view, each with the view it was taken at, most
recent first. A move's action is the last entry of the own action list after
it. -/
def ownPlay (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program →
      List (ProtocolView who program × OwnAction Player L)
  | _, _, .ret _, _ => []
  | _, _, .sample _ _ _ next, view =>
      view.elim (fun _ => []) fun later =>
        (ownPlay who next later).map (Prod.map Sum.inr id)
  | _, _, .commit _ owner _ _ next, view =>
      view.elim (fun _ => []) fun later =>
        (ownPlay who next later).map (Prod.map Sum.inr id) ++
          if owner = who then
            ((entryView who next later).2.getLast?.map fun action =>
              (Sum.inl ((entryView who next later).back (decide (owner = who))),
                action)).toList
          else []
  | _, _, .reveal _ owner _ _ _ _ next, view =>
      view.elim (fun _ => []) fun later =>
        (ownPlay who next later).map (Prod.map Sum.inr id) ++
          if owner = who then
            ((entryView who next later).2.getLast?.map fun action =>
              (Sum.inl ((entryView who next later).back (decide (owner = who))),
                action)).toList
          else []

@[simp] theorem ownPlay_observe_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    ownPlay who program (ProtocolState.observe who program (ProtocolState.entry program config)) =
      [] := by
  cases program <;> rfl

private theorem eq_none_of_actor_ne (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} {admission : CommitmentInterface program}
    {view : ProtocolView who program} {choice : Option (OwnAction Player L)}
    (legal : menu who program admission view choice) (other : actor who program view ≠ some who) :
    choice = none := by
  cases choice with
  | none => rfl
  | some _ => exact (other legal.1).elim

/-- One legal source transition appends exactly the mover's own move to the
record read from the view. -/
theorem ownPlay_step (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (before after : ProtocolState program) → (joint : Player → Option (OwnAction Player L)) →
    menu who program admission (ProtocolState.observe who program before) (joint who) →
    after ∈ (ProtocolState.step program before joint).support →
    ownPlay who program (ProtocolState.observe who program after) =
      ((joint who).map fun action => (ProtocolState.observe who program before, action)).toList ++
        ownPlay who program (ProtocolState.observe who program before)
  | _, _, .ret _, _, before, after, joint, legal, supported => by
      have same := (PMF.mem_support_pure_iff _ _).mp supported
      subst after
      rw [eq_none_of_actor_ne who legal (by simp [actor])]
      rfl
  | _, _, .sample name fresh law next, admission, before, after, joint, legal, supported => by
      cases before with
      | inl config =>
          simp only [ProtocolState.step, Sum.elim_inl, PMF.support_map,
            Set.mem_image] at supported
          obtain ⟨value, _, rfl⟩ := supported
          rw [eq_none_of_actor_ne who legal (by simp [actor, ProtocolState.observe])]
          simp [ProtocolState.observe, ownPlay]
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map,
            Set.mem_image] at supported
          obtain ⟨after, reached, rfl⟩ := supported
          have tail := ownPlay_step who next admission rest after joint legal reached
          simp only [ProtocolState.observe, Sum.elim_inr, ownPlay, tail, List.map_append]
          cases joint who <;> rfl
  | _, _, .commit name owner fresh guard next, admission, before, after, joint, legal,
      supported => by
      cases before with
      | inl config =>
          simp only [ProtocolState.step, Sum.elim_inl, PMF.mem_support_pure_iff] at supported
          subst after
          by_cases same : owner = who
          · subst who
            cases chosen : joint owner with
            | none =>
                rw [chosen] at legal
                exact (legal rfl).elim
            | some action =>
                rw [chosen] at legal
                obtain ⟨_, choice, _, rfl⟩ := legal
                simp [ProtocolState.observe, ownPlay, Config.view, commitSuccessor]
          · rw [eq_none_of_actor_ne who legal (by simpa [actor, ProtocolState.observe] using same)]
            simp [ProtocolState.observe, ownPlay, same]
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map,
            Set.mem_image] at supported
          obtain ⟨after, reached, rfl⟩ := supported
          have tail := ownPlay_step who next (fun site => admission (some site)) rest after joint
            legal reached
          have entry := entryView_step who next rest after joint reached
          simp only [ProtocolState.observe, Sum.elim_inr, ownPlay, tail, entry, List.map_append,
            List.append_assoc]
          cases joint who <;> rfl
  | _, _, .reveal published owner name fresh source unresolved next, admission, before, after,
      joint, legal, supported => by
      cases before with
      | inl config =>
          simp only [ProtocolState.step, Sum.elim_inl, PMF.mem_support_pure_iff] at supported
          subst after
          by_cases same : owner = who
          · subst who
            cases chosen : joint owner with
            | none =>
                rw [chosen] at legal
                exact (legal rfl).elim
            | some action =>
                rw [chosen] at legal
                obtain ⟨_, disclose, rfl⟩ := legal
                simp [ProtocolState.observe, ownPlay, Config.view, revealSuccessor,
                  OwnAction.disclosure]
          · rw [eq_none_of_actor_ne who legal (by simpa [actor, ProtocolState.observe] using same)]
            simp [ProtocolState.observe, ownPlay, same]
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map,
            Set.mem_image] at supported
          obtain ⟨after, reached, rfl⟩ := supported
          have tail := ownPlay_step who next admission rest after joint legal reached
          have entry := entryView_step who next rest after joint reached
          simp only [ProtocolState.observe, Sum.elim_inr, ownPlay, tail, entry, List.map_append,
            List.append_assoc]
          cases joint who <;> rfl

end ProtocolView

namespace Setup

/-- The own moves recorded in a setup view: none before the setup draw. -/
def ownPlayView (setup : Setup (Player := Player) (L := L)) (who : Player) :
    setup.ProtocolView who → List (setup.ProtocolView who × OwnAction Player L)
  | none => []
  | some view => (ProtocolView.ownPlay who setup.program view).map (Prod.map some id)

/-- A player's own play along a setup history is read from its current view. -/
theorem protocol_ownPlay (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player) :
    ∀ {state} (trace : (setup.executionProtocol admission).Trace state),
      (setup.protocolSignals admission).ownPlay who trace =
        setup.ownPlayView who (setup.protocolObserve who state)
  | _, .start => rfl
  | _, .extend (source := before) (target := after) prior joint legal realized => by
      rw [InfoSignals.ownPlay_extend, protocol_ownPlay setup admission who prior,
        protocol_info setup admission who prior]
      have localLegal := legalOption_of_legal legal who
      cases before with
      | none =>
          have inactive : joint who = none := by
            revert localLegal
            cases joint who with
            | none => exact fun _ => rfl
            | some _ => exact fun permitted => permitted.1.elim
          change after ∈ (setup.initialLaw.map _).support at realized
          rw [PMF.support_map] at realized
          obtain ⟨initial, _, rfl⟩ := realized
          rw [inactive]
          simp [ownPlayView, protocolObserve]
      | some before =>
          change after ∈ ((SourceProgram.ProtocolState.step setup.program before joint).map
            some).support at realized
          rw [PMF.support_map] at realized
          obtain ⟨after, reached, rfl⟩ := realized
          have permitted : ProtocolView.menu who setup.program admission
              (ProtocolState.observe who setup.program before) (joint who) := by
            revert localLegal
            cases joint who <;> exact id
          have step := ProtocolView.ownPlay_step who setup.program admission before after joint
            permitted reached
          simp only [protocolObserve, Option.map_some, ownPlayView, step, List.map_append]
          cases joint who <;> rfl

/-- **Perfect recall.** A source player reaching one view by two histories has
taken the same own moves at the same views along both. -/
theorem protocol_perfectRecall (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    (setup.informationModel admission).PerfectRecall := by
  intro who first second firstTrace secondTrace same
  change (setup.protocolSignals admission).infoOf who firstTrace =
    (setup.protocolSignals admission).infoOf who secondTrace at same
  change (setup.protocolSignals admission).ownPlay who firstTrace =
    (setup.protocolSignals admission).ownPlay who secondTrace
  rw [protocol_info, protocol_info] at same
  rw [protocol_ownPlay, protocol_ownPlay, same]

theorem protocol_decisionRecall (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    (setup.informationModel admission).DecisionRecall :=
  (setup.informationModel admission).decisionRecall_of_perfectRecall
    (setup.protocol_perfectRecall admission)

end Setup

end Vegas.SourceProgram
