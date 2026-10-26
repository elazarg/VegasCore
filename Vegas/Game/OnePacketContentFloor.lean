/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFactorization

/-! # The content floor and the combined tremble floor

**The content floor.** A response of the one-packet game carries a content
factor: the mass the as-if-honest law at the responder's projected source view
gives the source action the response decodes to (`Vegas.contentFactor`). Over
the finitely many pairs of one-packet histories and the finitely many responses
the menu offers before each, the content factors that are positive have a least
element, the content floor (`Vegas.contentFloor`). Every positive content factor
of a step of the one-packet game is at least the floor
(`Vegas.contentFloor_le_of_step`). The floor depends on the assessment, so a
tremble sequence has one floor per stage.

**The combined floor.** The smaller of the intended step floor and the content
floor (`Vegas.combinedFloor`) bounds both the steps of intended play and the
content factors of native responses. The tremble scale built from it
(`Vegas.trembleScale`) vanishes, is negligible against the floor, its square is
negligible against the floor to the power of the depth, and the scale itself is
negligible against that power (`Vegas.tendsto_trembleScale_div_pow`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

section Scale

variable (floors : ℕ → ℝ) (positive : ∀ n, 0 < floors n) (le_one : ∀ n, floors n ≤ 1)
  {depth : ℕ}
include positive le_one

/-- **The tremble scale is negligible against the floor to the power of the
depth.** -/
theorem tendsto_trembleScale_div_pow :
    Tendsto (fun n => trembleScale (floors n) depth n / floors n ^ depth) atTop (nhds 0) := by
  refine squeeze_zero
    (fun n => div_nonneg (trembleScale_nonneg (positive n).le) (pow_nonneg (positive n).le _))
    (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  have floorPos := positive n
  have rewritten : trembleScale (floors n) depth n / floors n ^ depth =
      floors n / ((n : ℝ) + 4) := by
    unfold trembleScale
    field_simp
    ring
  rw [rewritten]
  have cast : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [le_one n]

end Scale

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The content factor of a response is at most one. -/
theorem contentFactor_le_one (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (before after : (application setup runtime leaks).Execution)
    (action : (application setup runtime leaks).Action) :
    contentFactor setup runtime leaks assessment who before after action ≤ 1 := by
  unfold contentFactor
  split
  · exact le_rfl
  · exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one _ _)

/-- Silence has content factor one. -/
theorem contentFactor_silence (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (before after : (application setup runtime leaks).Execution) :
    contentFactor setup runtime leaks assessment who before after ⟨none⟩ = 1 := rfl

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

/-- The content factors of the responses the one-packet menu offers `who`
between two native states. -/
def responseContents (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    (application setup runtime leaks).ProtocolState → (application setup runtime
      leaks).ProtocolState →
      Finset ℝ
  | some control, some next =>
      ((bounds.onePacketMenu runtime leaks).actions who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who)).image
          (contentFactor setup runtime leaks assessment who control.execution next.execution)
  | _, _ => ∅

open Classical in
/-- The positive content factors of responses between one-packet histories. -/
def contentMasses [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]
    (assessment : setup.intendedModel.BehavioralAssessment) : Finset ℝ :=
  let := Fintype.ofFinite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History
  ((Finset.univ : Finset ((onePacketProtocol setup runtime leaks bounds horizon scheduler).History ×
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).History × Player)).biUnion
    fun triple => responseContents setup runtime leaks bounds assessment triple.2.2 triple.1.state
      triple.2.1.state).filter (0 < ·)

/-- **The content floor.** The smallest positive content factor of a response
the one-packet menu offers between two one-packet histories. It is one when no
such factor is positive. -/
def contentFloor [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]
    (assessment : setup.intendedModel.BehavioralAssessment) : ℝ :=
  if nonempty : (contentMasses setup runtime leaks bounds horizon scheduler assessment).Nonempty
    then
    (contentMasses setup runtime leaks bounds horizon scheduler assessment).min' nonempty
  else 1

variable [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]

theorem mem_contentMasses (assessment : setup.intendedModel.BehavioralAssessment) {mass : ℝ}
    (member : mass ∈ contentMasses setup runtime leaks bounds horizon scheduler assessment) :
    0 < mass ∧ mass ≤ 1 := by
  classical
  unfold contentMasses at member
  rw [Finset.mem_filter, Finset.mem_biUnion] at member
  obtain ⟨⟨triple, _, contents⟩, positive⟩ := member
  refine ⟨positive, ?_⟩
  unfold responseContents at contents
  split at contents
  · obtain ⟨action, _, rfl⟩ := Finset.mem_image.mp contents
    exact contentFactor_le_one setup runtime leaks assessment _ _ _ action
  · cases contents

theorem contentFloor_pos (assessment : setup.intendedModel.BehavioralAssessment) :
    0 < contentFloor setup runtime leaks bounds horizon scheduler assessment := by
  unfold contentFloor
  split
  · rename_i nonempty
    exact (mem_contentMasses setup runtime leaks bounds horizon scheduler assessment
      ((contentMasses setup runtime leaks bounds horizon scheduler assessment).min'_mem nonempty)).1
  · exact zero_lt_one

theorem contentFloor_le_one (assessment : setup.intendedModel.BehavioralAssessment) :
    contentFloor setup runtime leaks bounds horizon scheduler assessment ≤ 1 := by
  unfold contentFloor
  split
  · rename_i nonempty
    exact (mem_contentMasses setup runtime leaks bounds horizon scheduler assessment
      ((contentMasses setup runtime leaks bounds horizon scheduler assessment).min'_mem nonempty)).2
  · exact le_rfl

variable {setup runtime leaks bounds horizon scheduler}

/-- **Positive content factors are at least the content floor.** At every step
of the one-packet game from an initialized state, the content factor of the
actor's response, when positive, is at least the content floor. -/
theorem contentFloor_le_of_step (assessment : setup.intendedModel.BehavioralAssessment)
    {before after : (application setup runtime leaks).ProtocolState}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
      before
      ⟨joint, legal⟩).support)
    (control next : (application setup runtime leaks).Control) (initialized : before = some control)
    (reached : after = some next) (actor : Player)
    (positive : 0 < contentFactor setup runtime leaks assessment actor control.execution
      next.execution
      ((joint actor).getD ⟨none⟩)) :
    contentFloor setup runtime leaks bounds horizon scheduler assessment ≤
      contentFactor setup runtime leaks assessment actor control.execution next.execution
        ((joint actor).getD ⟨none⟩) := by
  classical
  cases chosen : joint actor with
  | none =>
      rw [Option.getD_none, contentFactor_silence]
      exact contentFloor_le_one setup runtime leaks bounds horizon scheduler assessment
  | some action =>
      rw [chosen, Option.getD_some] at positive
      rw [Option.getD_some]
      have offered : action ∈ (bounds.onePacketMenu runtime leaks).actions actor
          (control.execution.recall actor)
          (control.execution.observe (application setup runtime leaks) actor) := by
        have localLegal := legal.2 actor
        rw [chosen] at localLegal
        subst initialized
        exact localLegal.2
      have member : contentFactor setup runtime leaks assessment actor control.execution
        next.execution
          action ∈ contentMasses setup runtime leaks bounds horizon scheduler assessment := by
        let := Fintype.ofFinite (onePacketProtocol setup runtime leaks bounds horizon
          scheduler).History
        unfold contentMasses
        rw [Finset.mem_filter, Finset.mem_biUnion]
        refine ⟨⟨(⟨before, prior⟩, ⟨after, prior.extend joint legal realized⟩, actor),
          Finset.mem_univ _, ?_⟩, positive⟩
        subst initialized reached
        exact Finset.mem_image.mpr ⟨action, offered, rfl⟩
      unfold contentFloor
      rw [dite_eq_left ⟨_, member⟩]
      exact Finset.min'_le _ _ member

variable (setup runtime leaks bounds horizon scheduler)

/-- **The combined floor.** The smaller of the intended step floor and the
content floor. -/
def combinedFloor [Finite setup.intendedProtocol.History]
    (assessment : setup.intendedModel.BehavioralAssessment) : ℝ :=
  min (setup.intendedStepFloor assessment)
    (contentFloor setup runtime leaks bounds horizon scheduler assessment)

variable [Finite setup.intendedProtocol.History]

theorem combinedFloor_pos (assessment : setup.intendedModel.BehavioralAssessment) :
    0 < combinedFloor setup runtime leaks bounds horizon scheduler assessment :=
  lt_min (setup.intendedStepFloor_pos assessment)
    (contentFloor_pos setup runtime leaks bounds horizon scheduler assessment)

theorem combinedFloor_le_one (assessment : setup.intendedModel.BehavioralAssessment) :
    combinedFloor setup runtime leaks bounds horizon scheduler assessment ≤ 1 :=
  (min_le_left _ _).trans (setup.intendedStepFloor_le_one assessment)

theorem combinedFloor_le_contentFloor (assessment : setup.intendedModel.BehavioralAssessment) :
    combinedFloor setup runtime leaks bounds horizon scheduler assessment ≤
      contentFloor setup runtime leaks bounds horizon scheduler assessment :=
  min_le_right _ _

end Vegas
