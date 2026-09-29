/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceLocalContinuation

/-! # Admitted source policies for one changed decision

A finite replacement law at one source observation decodes to one admitted
syntactic policy. The same policy works at every hidden history with that
observation. Its continuation first samples the replacement and then follows
the original profile, so local runtime comparisons can use the ordinary
whole-policy source assessment interface.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)

/-- One admitted syntactic alternative realizes an arbitrary local choice law
at every actual history in the information fiber. Subsequent decisions use the
baseline profile; the alternative is fixed before choosing a hidden history. -/
theorem exists_admitted_local_law
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission)
    (who : Player) (info : setup.ProtocolView who)
    (law : PMF ((setup.informationModel admission).Choice who info)) :
    ∃ alternative : BehavioralPolicy who setup.program,
      alternative.Admitted setup.program admission ∧
      ∀ (history : (setup.executionProtocol admission).History)
        (_running : ¬ (setup.executionProtocol admission).terminal history.state)
        (_active : (setup.executionProtocol admission).active history.state who)
        (_observed : (setup.informationModel admission).infoOf who history.trace = info),
        setup.continuationLaw (Function.update profile who alternative) history.state =
          law.bind (fun choice =>
            (setup.protocolStep history.state
              (fun player => if player = who then choice.1 else none)).bind
                (setup.continuationLaw profile)) := by
  classical
  let := Fintype.ofFinite Player
  let model := setup.informationModel admission
  let encoded : Profile model.behavioralSignature := fun player =>
    setup.toProtocolBehavioralPolicy admission player (profile player) (permitted player)
  let changed := (encoded who).withLaw info law
  let alternative := (setup.behavioralPolicyEquiv admission who).symm changed
  let updated := Profile.update (sig := model.behavioralSignature) encoded who changed
  have decoded : setup.decodeBehavioralProfile admission encoded = profile := by
    funext player
    exact congrArg Subtype.val ((setup.behavioralPolicyEquiv admission player).symm_apply_apply
      ⟨profile player, permitted player⟩)
  have decodedUpdated : setup.decodeBehavioralProfile admission updated =
      Function.update profile who alternative.1 := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [decodeBehavioralProfile, updated, Profile.update_same, Function.update_self]
      rfl
    · simp only [decodeBehavioralProfile, updated, Profile.update_of_ne _ _ same,
        Function.update_of_ne same]
      exact congrFun decoded player
  refine ⟨alternative.1, alternative.2, ?_⟩
  intro history running active observed
  let fuel := setup.protocolRemaining history.state
  have enough : setup.protocolRemaining history.state ≤ fuel + 1 := by omega
  have first := setup.run_local_law_readout admission encoded history who running active
    observed law fuel enough
  have whole := setup.runBehavioralFrom_readout admission updated (fuel + 1) history enough
  rw [decoded] at first
  rw [decodedUpdated] at whole
  apply pmf_map_injective (Option.some_injective _)
  rw [PMF.map_bind]
  exact whole.symm.trans first

end Vegas.SourceProgram.Setup
