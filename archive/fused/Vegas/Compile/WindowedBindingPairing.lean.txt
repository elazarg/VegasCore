/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingLocality
import Vegas.Compile.WindowedGatedExecution

/-! # Paired execution of unchanged binding blocks -/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal : P}
variable {left right : runtime.application.PolicyExecution}

/-- Two exact binding-controller laws may follow a gated player prefix. The
private draws may differ, but the resulting opaque submissions agree. -/
theorem binding_polls_after_gated_prefix
    (agreement : PolicyAgreement runtime focal left right)
    (owner : P) (howner : owner ≠ focal) (code : BindingCode P L)
    (replacement : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (base players : P → runtime.application.PlayerPolicy)
    (hfocal : players focal = fun history view => FinDist.pure (replacement history view))
    (hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor))
    (instruction : ApplicationInstruction P L) (before : List (@Invocation P))
    (hplayers : ∀ invocation ∈ before, ∃ actor, invocation = .player actor)
    (hgate : ∀ actor, Invocation.player actor ∈ before → actor ≠ focal →
      instruction.submitter ≠ some actor)
    (environment : runtime.application.EnvironmentPolicy)
    (hplayerLengths : ∀ actor, (left.principalHistory actor).length =
      (right.principalHistory actor).length)
    (hplayerIndex : ∀ actor index, (left.principalHistory actor).length ≤ index →
      index < (left.principalHistory actor).length +
        before.countP (playerCountFor actor) →
      runtime.image.instructions[index / 3]? = some instruction)
    (leftChoices rightChoices : FinDist (L.Val code.ty))
    (hleftOwnerLaw : ∀ middle,
      middle ∈ (runtime.application.runPolicies players environment before left).support →
      runtime.application.runPolicies players environment
        [.player owner, .player owner] middle =
          leftChoices.bind fun value =>
            (runtime.application.playerStep owner middle
              (.privateCommand (.register code.sourceSlot ⟨code.ty, value⟩))).bind
                fun registered => runtime.application.playerStep owner registered
                  (.submit (.binding code.node (owner, code.sourceSlot))))
    (hrightOwnerLaw : ∀ middle,
      middle ∈ (runtime.application.runPolicies players environment before right).support →
      runtime.application.runPolicies players environment
        [.player owner, .player owner] middle =
          rightChoices.bind fun value =>
            (runtime.application.playerStep owner middle
              (.privateCommand (.register code.sourceSlot ⟨code.ty, value⟩))).bind
                fun registered => runtime.application.playerStep owner registered
                  (.submit (.binding code.node (owner, code.sourceSlot))))
    (leftSubmitted rightSubmitted : runtime.application.PolicyExecution)
    (hleft : leftSubmitted ∈ (runtime.application.runPolicies players environment
      (before ++ [.player owner, .player owner]) left).support)
    (hright : rightSubmitted ∈ (runtime.application.runPolicies players environment
      (before ++ [.player owner, .player owner]) right).support) :
    PolicyAgreement runtime focal leftSubmitted rightSubmitted ∧
      ∃ leftMiddle,
        leftMiddle ∈ (runtime.application.runPolicies players environment before left).support ∧
        leftSubmitted.native.pool = (leftMiddle.native.pool.submit owner
          (.binding code.node (owner, code.sourceSlot))).2 := by
  rw [MessageApplication.runPolicies_append] at hleft hright
  simp only [FinDist.support_bind, Set.mem_iUnion] at hleft hright
  obtain ⟨leftMiddle, hleftBefore, hleftOwner⟩ := hleft
  obtain ⟨rightMiddle, hrightBefore, hrightOwner⟩ := hright
  have middleAgreement := agreement.runPolicies_players_gated replacement base players
    hfocal hothers instruction before hplayers hgate environment hplayerLengths
    hplayerIndex leftMiddle rightMiddle hleftBefore hrightBefore
  have hresult := middleAgreement.binding_twoRunLaw_other howner code leftChoices rightChoices
    players players environment environment leftSubmitted rightSubmitted
    (hleftOwnerLaw leftMiddle hleftBefore)
    (hrightOwnerLaw rightMiddle hrightBefore) hleftOwner hrightOwner
  exact ⟨hresult.1, leftMiddle, hleftBefore, hresult.2⟩

end Vegas.WindowedApplication.PolicyAgreement

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.binding_polls_after_gated_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.binding_polls_after_gated_prefix
