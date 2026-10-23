/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryErasedContinuation

/-! # Retaining an original source instruction suffix after a failed attempt

Supported source continuations are lifted through equality of the actual
erased histories. The same raw joints and original chance support are used;
the statement constructs genuine histories of the existing protocol.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem step_erased_state
    {first second : setup.commitRecoveryProtocol.State}
    (same : first.map CommitRecoveryState.eraseHistory =
      second.map CommitRecoveryState.eraseHistory)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (firstLegal : setup.commitRecoveryProtocol.Legal first joint)
    (secondLegal : setup.commitRecoveryProtocol.Legal second joint) :
    (setup.commitRecoveryProtocol.step first ⟨joint, firstLegal⟩).map
        (Option.map CommitRecoveryState.eraseHistory) =
      (setup.commitRecoveryProtocol.step second ⟨joint, secondLegal⟩).map
        (Option.map CommitRecoveryState.eraseHistory) := by
  cases first with
  | none => cases second <;> cases same; rfl
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          have states := Option.some.inj same
          simp only [commitRecoveryProtocol, PMF.map_comp]
          change (first.step joint).map (some ∘ CommitRecoveryState.eraseHistory) =
            (second.step joint).map (some ∘ CommitRecoveryState.eraseHistory)
          rw [← PMF.map_comp, ← PMF.map_comp, ← first.step_eraseHistory,
            ← second.step_eraseHistory, states]

private theorem legal_of_erased_history_eq
    (first second : setup.commitRecoveryProtocol.History)
    (same : setup.commitRecoveryErasedHistory first = setup.commitRecoveryErasedHistory second)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal first.state joint) :
    setup.commitRecoveryProtocol.Legal second.state joint := by
  have running : ¬ setup.commitRecoveryProtocol.terminal second.state := fun terminal =>
    legal.1 ((setup.commitRecovery_terminal_eq_of_erased (congrArg Prod.fst same)).mpr terminal)
  apply setup.commitRecoveryProtocol.legal_of_legalOption running
  intro who
  apply (setup.commitRecoveryModel.menu_adequate who second.trace (joint who)).mp
  have equal : setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who first.trace) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who second.trace) :=
    congrFun (congrArg Prod.snd same) who
  have menus : setup.commitRecoveryModel.menu who
        (setup.commitRecoveryModel.infoOf who first.trace) =
      setup.commitRecoveryModel.menu who
        (setup.commitRecoveryModel.infoOf who second.trace) := by
    rw [← setup.commitRecoveryErasedInformation_menu who
      (setup.commitRecoveryModel.infoOf who first.trace), equal,
      setup.commitRecoveryErasedInformation_menu]
  rw [← menus]
  exact (setup.commitRecoveryModel.menu_adequate who first.trace (joint who)).mpr
    (setup.commitRecoveryProtocol.legalOption_of_legal legal who)

/-- Every actual original joint has a genuinely supported counterpart at an
erased-equal history, with the SAME instruction and erased successor. No
desired transition or continuation law is assumed. -/
theorem commitRecovery_supported_step_of_erased_history_eq
    (first second : setup.commitRecoveryProtocol.History)
    (same : setup.commitRecoveryErasedHistory first = setup.commitRecoveryErasedHistory second)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal first.state joint)
    {target : setup.commitRecoveryProtocol.State}
    (supported : target ∈ (setup.commitRecoveryProtocol.step first.state ⟨joint, legal⟩).support) :
    ∃ rightLegal : setup.commitRecoveryProtocol.Legal second.state joint,
      ∃ rightTarget : setup.commitRecoveryProtocol.State,
        ∃ rightSupported : rightTarget ∈
          (setup.commitRecoveryProtocol.step second.state ⟨joint, rightLegal⟩).support,
          setup.commitRecoveryErasedHistory (first.extend legal supported) =
            setup.commitRecoveryErasedHistory (second.extend rightLegal rightSupported) := by
  have rightLegal := setup.legal_of_erased_history_eq first second same joint legal
  have mapped : target.map CommitRecoveryState.eraseHistory ∈
      ((setup.commitRecoveryProtocol.step first.state ⟨joint, legal⟩).map
        (Option.map CommitRecoveryState.eraseHistory)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨target, supported, rfl⟩
  rw [setup.step_erased_state (congrArg Prod.fst same) joint legal rightLegal] at mapped
  obtain ⟨rightTarget, rightSupported, targetSame⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp mapped
  refine ⟨rightLegal, rightTarget, rightSupported, ?_⟩
  rw [setup.commitRecoveryErasedHistory_extend, setup.commitRecoveryErasedHistory_extend,
    same, targetSame]

end Vegas.SourceProgram.Setup
