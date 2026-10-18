/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryWordLift

/-! # Labeled joint words on the original source hybrid history -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def proposalRecoverySpliceWord (focal : Player)
    (mine others : List (Player → Option (ProposalRecoveryMove Player L))) :
    List (Player → Option (ProposalRecoveryMove Player L)) :=
  List.zipWith (fun left right => Function.update right focal (left focal)) mine others

omit [IExpr.ResultTypes L] in
theorem proposalRecoverySpliceWord_coordinate (focal who : Player)
    (mine others : List (Player → Option (ProposalRecoveryMove Player L)))
    (clock : mine.length = others.length) :
    (proposalRecoverySpliceWord focal mine others).map (fun joint => joint who) =
      if who = focal then mine.map (fun joint => joint who)
      else others.map (fun joint => joint who) := by
  induction mine generalizing others with
  | nil =>
      cases others with
      | nil => simp only [proposalRecoverySpliceWord, List.zipWith_nil_left, List.map_nil, ite_self]
      | cons right rest => simp only [List.length_nil, List.length_cons] at clock; omega
  | cons left rest ih =>
      cases others with
      | nil => simp only [List.length_nil, List.length_cons] at clock; omega
      | cons right remaining =>
          have previous : rest.length = remaining.length := Nat.succ.inj clock
          by_cases own : who = focal
          · subst who
            simpa only [proposalRecoverySpliceWord, List.zipWith_cons_cons,
              List.map_cons, Function.update_self, ite_true] using
              congrArg (List.cons (left focal)) (ih remaining previous)
          · simpa only [proposalRecoverySpliceWord, List.zipWith_cons_cons,
              List.map_cons, Function.update_of_ne own, own, ite_false] using
              congrArg (List.cons (right who)) (ih remaining previous)

omit [IExpr.ResultTypes L] in
theorem proposalRecoverySpliceWord_valid (focal : Player)
    (mine others : List (Player → Option (ProposalRecoveryMove Player L)))
    (leftValid : ∀ joint ∈ mine, ∀ who move, joint who = some move → move.Valid)
    (rightValid : ∀ joint ∈ others, ∀ who move, joint who = some move → move.Valid) :
    ∀ joint ∈ proposalRecoverySpliceWord focal mine others,
      ∀ who move, joint who = some move → move.Valid := by
  induction mine generalizing others with
  | nil => simp only [proposalRecoverySpliceWord, List.zipWith_nil_left, List.not_mem_nil,
      false_implies, implies_true]
  | cons left rest ih =>
      cases others with
      | nil => simp only [proposalRecoverySpliceWord, List.zipWith_nil_right,
          List.not_mem_nil, false_implies, implies_true]
      | cons right remaining =>
          intro joint member who move selected
          rcases List.mem_cons.mp member with same | prior
          · subst joint
            by_cases own : who = focal
            · subst who
              exact leftValid left List.mem_cons_self focal move
                (by simpa only [Function.update_self] using selected)
            · exact rightValid right List.mem_cons_self who move
                ((Function.update_of_ne own _ _).symm.trans selected)
          · exact ih remaining
              (fun joint member => leftValid joint (List.mem_cons_of_mem _ member))
              (fun joint member => rightValid joint (List.mem_cons_of_mem _ member))
              joint prior who move selected

/-- Decorate the existing semantic hybrid path with the original labeled
coordinates. The source transition and original Nature outcomes are reused. -/
theorem proposalRecovery_lift_spliced_word (focal : Player)
    {mineState othersState hybridState : setup.proposalRecoveryProtocol.State}
    (mine : setup.proposalRecoveryProtocol.Trace mineState)
    (others : setup.proposalRecoveryProtocol.Trace othersState)
    (hybrid : setup.commitRecoveryProtocol.Trace hybridState)
    (clock : mine.length = others.length)
    (coordinates : ∀ who,
      (setup.recoveryJointRecall hybrid).map (fun joint => joint who) =
        if who = focal then
          (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace mine)).map
            (fun joint => joint who)
        else (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace others)).map
          (fun joint => joint who)) :
    ∃ lifted : setup.proposalRecoveryProtocol.Trace hybridState,
      setup.proposalRecoveryEraseTrace lifted = hybrid ∧
      ∀ who, (setup.proposalRecoveryJointRecall lifted).map (fun joint => joint who) =
        if who = focal then
          (setup.proposalRecoveryJointRecall mine).map (fun joint => joint who)
        else (setup.proposalRecoveryJointRecall others).map (fun joint => joint who) := by
  let word := proposalRecoverySpliceWord focal
    (setup.proposalRecoveryJointRecall mine) (setup.proposalRecoveryJointRecall others)
  have lengths : (setup.proposalRecoveryJointRecall mine).length =
      (setup.proposalRecoveryJointRecall others).length := by
    have size {state} (trace : setup.proposalRecoveryProtocol.Trace state) :
        (setup.proposalRecoveryJointRecall trace).length = trace.length := by
      induction trace with
      | start => rfl
      | extend prior joint legal supported ih => exact congrArg Nat.succ ih
    exact (size mine).trans (clock.trans (size others).symm)
  have selected who := proposalRecoverySpliceWord_coordinate focal who
    (setup.proposalRecoveryJointRecall mine) (setup.proposalRecoveryJointRecall others) lengths
  have semanticCoordinate who :
      (word.map proposalRecoveryJoint).map (fun joint => joint who) =
        (setup.recoveryJointRecall hybrid).map (fun joint => joint who) := by
    rw [List.map_map]
    have mapped := congrArg (List.map (Option.map ProposalRecoveryMove.semantic)) (selected who)
    rw [coordinates]
    by_cases own : who = focal
    · simp only [own, ite_true] at mapped ⊢
      rw [← setup.proposalRecoveryJointRecall_semantic]
      simpa only [List.map_map, proposalRecoveryJoint, Function.comp_def] using mapped
    · simp only [own, ite_false] at mapped ⊢
      rw [← setup.proposalRecoveryJointRecall_semantic]
      simpa only [List.map_map, proposalRecoveryJoint, Function.comp_def] using mapped
  have semantic : word.map proposalRecoveryJoint = setup.recoveryJointRecall hybrid := by
    have size : (word.map proposalRecoveryJoint).length =
        (setup.recoveryJointRecall hybrid).length := by
      simpa only [List.length_map] using congrArg List.length (semanticCoordinate focal)
    apply List.ext_getElem size
    intro index leftInside rightInside
    funext who
    have atIndex := congrArg (fun xs => xs[index]?) (semanticCoordinate who)
    simpa only [List.getElem?_map, List.getElem?_eq_getElem leftInside,
      List.getElem?_eq_getElem rightInside, Option.map_some, Option.some.injEq] using atIndex
  obtain ⟨lifted, erased, labeled⟩ := setup.proposalRecovery_lift_joint_word hybrid word semantic
    (proposalRecoverySpliceWord_valid focal _ _
      (setup.proposalRecoveryJointRecall_valid mine)
      (setup.proposalRecoveryJointRecall_valid others))
  exact ⟨lifted, erased, fun who => labeled ▸ selected who⟩

end Vegas.SourceProgram.Setup
