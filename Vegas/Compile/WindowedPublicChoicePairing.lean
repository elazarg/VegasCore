/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedGatedExecution

/-! # Paired execution of unchanged public-choice polls -/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal : P}
variable {left right : runtime.application.PolicyExecution}

/-- After a paired gated prefix, equal supported public-choice draws give equal
nonfocal submissions. The source kernels themselves may differ. The result
retains membership in both actual prefix executions. -/
theorem publicChoice_polls_after_gated_prefix
    (agreement : PolicyAgreement runtime focal left right)
    (owner : P) (howner : owner ≠ focal) (address : Nat) (ty : L.Ty)
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
    (leftKernel rightKernel : FinDist (L.Val ty))
    (hleftOwnerLaw : ∀ middle,
      middle ∈ (runtime.application.runPolicies players environment before left).support →
      runtime.application.runPolicies players environment
        [.player owner, .player owner] middle =
          leftKernel.bind fun value =>
            (runtime.application.playerStep owner middle
              (.submit (.choice address ⟨ty, value⟩))).bind fun submitted =>
                runtime.application.playerStep owner submitted .wait)
    (hrightOwnerLaw : ∀ middle,
      middle ∈ (runtime.application.runPolicies players environment before right).support →
      runtime.application.runPolicies players environment
        [.player owner, .player owner] middle =
          rightKernel.bind fun value =>
            (runtime.application.playerStep owner middle
              (.submit (.choice address ⟨ty, value⟩))).bind fun submitted =>
                runtime.application.playerStep owner submitted .wait)
    (value : L.Val ty) (hleftValue : value ∈ leftKernel.support)
    (hrightValue : value ∈ rightKernel.support)
    (leftMiddle rightMiddle leftSubmitted rightSubmitted leftFinal rightFinal :
      runtime.application.PolicyExecution)
    (hleftMiddle : leftMiddle ∈
      (runtime.application.runPolicies players environment before left).support)
    (hrightMiddle : rightMiddle ∈
      (runtime.application.runPolicies players environment before right).support)
    (hleftSubmitted : leftSubmitted ∈
      (runtime.application.playerStep owner leftMiddle
        (.submit (.choice address ⟨ty, value⟩))).support)
    (hrightSubmitted : rightSubmitted ∈
      (runtime.application.playerStep owner rightMiddle
        (.submit (.choice address ⟨ty, value⟩))).support)
    (hleftFinal : leftFinal ∈
      (runtime.application.playerStep owner leftSubmitted .wait).support)
    (hrightFinal : rightFinal ∈
      (runtime.application.playerStep owner rightSubmitted .wait).support) :
    PolicyAgreement runtime focal leftFinal rightFinal ∧
      leftFinal ∈ (runtime.application.runPolicies players environment
        (before ++ [.player owner, .player owner]) left).support ∧
      rightFinal ∈ (runtime.application.runPolicies players environment
        (before ++ [.player owner, .player owner]) right).support := by
  have middleAgreement := agreement.runPolicies_players_gated replacement base players
    hfocal hothers instruction before hplayers hgate environment hplayerLengths
    hplayerIndex leftMiddle rightMiddle hleftMiddle hrightMiddle
  have submittedAgreement := middleAgreement.playerStep_submit_other owner howner
    (.choice address ⟨ty, value⟩) leftSubmitted rightSubmitted
    hleftSubmitted hrightSubmitted
  refine ⟨submittedAgreement.playerStep_wait_other owner howner leftFinal rightFinal
    hleftFinal hrightFinal, ?_, ?_⟩
  · rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨leftMiddle, hleftMiddle, ?_⟩
    rw [hleftOwnerLaw leftMiddle hleftMiddle]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨value, hleftValue, leftSubmitted,
      hleftSubmitted, hleftFinal⟩
  · rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨rightMiddle, hrightMiddle, ?_⟩
    rw [hrightOwnerLaw rightMiddle hrightMiddle]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨value, hrightValue, rightSubmitted,
      hrightSubmitted, hrightFinal⟩

end Vegas.WindowedApplication.PolicyAgreement

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.publicChoice_polls_after_gated_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.WindowedApplication.PolicyAgreement.publicChoice_polls_after_gated_prefix
