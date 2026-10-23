/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveLocalContinuation
import GameTheory.Protocol.BehavioralMixture

/-! # Full behavioral response histories factor through the actual raw action -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

local notation "N" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

open Classical in
/-- At a genuine pending response, one full-history transition depends on the
profile only through the actor's actual raw law. The derived kernel retains
the exact history, not only its projected control or public observation. -/
theorem exists_response_history_kernel
    (baseline : ∀ who, (N).BehavioralPolicy who) (who : Principal) (remaining : Nat)
    (execution : app.Execution)
    (trace : (E).Trace (some ⟨remaining, some who, execution⟩)) :
    ∃ kernel : app.Action → PMF (E).History,
      (∀ profile : ∀ owner, (N).BehavioralPolicy owner,
        (N).runBehavioralFrom profile 1 ⟨some ⟨remaining, some who, execution⟩, trace⟩ =
          (menu.decodeProfile initial horizon scheduler profile who (execution.recall who)
            (execution.observe app who)).bind kernel) ∧
      ∀ profile : ∀ owner, (N).BehavioralPolicy owner, ∀ action,
        action ∈ (menu.decodeProfile initial horizon scheduler profile who
          (execution.recall who) (execution.observe app who)).support →
        (kernel action).map History.state =
          PMF.pure (some ⟨remaining, none, execution.respond app who action⟩) := by
  let history : (E).History := ⟨some ⟨remaining, some who, execution⟩, trace⟩
  let info := (N).infoOf who trace
  let erase : (N).Choice who info → app.Action := fun choice => choice.1.getD ⟨none⟩
  have running : ¬ (E).terminal history.state := by
    rintro ⟨_, impossible⟩
    cases impossible
  have active : (E).active history.state who := rfl
  have unique : ∀ owner, (E).active history.state owner → owner = who := by
    intro owner yes
    exact Option.some.inj yes.symm
  have erased (choice : (N).Choice who info) : choice.1 = some (erase choice) := by
    have legal := ((N).menu_adequate who trace choice.1).mp choice.2
    obtain ⟨action, same⟩ := LegalOption.exists_eq_some_of_active choice.1 legal active
    simp only [erase, same, Option.getD_some]
  have injective : Function.Injective erase := by
    intro first second same
    apply Subtype.ext
    rw [erased first, erased second, same]
  let : Nonempty ((N).Choice who info) :=
    ⟨(baseline who info).support_nonempty.choose⟩
  let recover : app.Action → (N).Choice who info := Function.invFun erase
  have recover_erase : ∀ choice, recover (erase choice) = choice :=
    Function.leftInverse_invFun injective
  let branch := fun choice : (N).Choice who info =>
    (N).runBehavioralFrom (Profile.update (sig := (N).behavioralSignature) baseline who
      ((baseline who).commit info choice)) 1 history
  have decoded (profile : ∀ owner, (N).BehavioralPolicy owner) :
      menu.decodeProfile initial horizon scheduler profile who
        (execution.recall who) (execution.observe app who) = (profile who info).map erase := by
    have observed : info = some (execution.recall who, execution.observe app who) :=
      ((menu.info initial horizon scheduler who trace).trans (by
        simp only [ReactiveApplication.observe, ite_true]))
    dsimp only [erase]
    rw [observed]
    simp only [decodeProfile, decodePolicy, embedPolicy, PMF.map_comp, Function.comp_def]
    rfl
  refine ⟨fun action => branch (recover action), ?_, ?_⟩
  · intro profile
    let installed := Profile.update (sig := (N).behavioralSignature) baseline who
      ((baseline who).withLaw info (profile who info))
    have current : ∀ owner, profile owner ((N).infoOf owner trace) =
        installed owner ((N).infoOf owner trace) := by
      intro owner
      by_cases own : owner = who
      · subst owner
        change profile who info = installed who info
        simp only [installed, Profile.update_same, BehavioralPolicy.withLaw_self]
      · exact (N).behavioral_eq_of_not_active _ _ trace
          (fun yes => own (unique owner yes))
    have switched : (N).runBehavioralFrom profile 1 history =
        (N).runBehavioralFrom installed 1 history := by
      rw [(N).runBehavioralFrom_succ_of_not_terminal profile 0 running,
        (N).runBehavioralFrom_succ_of_not_terminal installed 0 running,
        (N).behavioralJoint_congr trace running current]
      rfl
    have affine : (N).runBehavioralFrom installed 1 history =
        (profile who info).bind branch := by
      rw [(N).runBehavioralFrom_succ_of_not_terminal installed 0 running]
      rw [(N).behavioralJoint_update_withLaw_eq_bind baseline who (baseline who) info
        (profile who info) trace running rfl, PMF.bind_bind]
      apply bind_congr_on_support
      intro choice _
      dsimp only [branch]
      rw [(N).runBehavioralFrom_succ_of_not_terminal _ 0 running]
      rfl
    rw [switched, affine, decoded, PMF.bind_map]
    apply bind_congr_on_support
    intro choice _
    change branch choice = branch (recover (erase choice))
    rw [recover_erase]
  · intro profile action present
    rw [decoded] at present
    obtain ⟨choice, _, rfl⟩ := PMF.support_map .. ▸ present
    change (branch (recover (erase choice))).map History.state = _
    rw [recover_erase]
    exact menu.run_commit_response initial horizon scheduler baseline history who remaining
      execution rfl choice (erase choice) (erased choice)

end Interaction.ReactiveApplication.ResponseMenu
