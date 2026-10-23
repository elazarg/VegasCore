/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedEffectiveOpening
import Vegas.Game.SourceServiceTimedContinuation

/-! # The intended effective opening stays in the intended game

From a point of the intended game carrying the program's registry and
publication status, every step of the intended effective opening reaches such a
point again (`Vegas.SourceProgram.Setup.intendedOpening_step_closed`): there the
opening plays the intended law, which offers only intended actions. Hence its
source continuation from such a point records no failed reveal of anyone
(`Vegas.SourceProgram.Setup.intendedOpening_continuation_failedReveals`).
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- **The intended effective opening keeps the intended game.** -/
theorem intendedOpening_step_closed [Fintype Player]
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (state target : SourceProgram.ProtocolState setup.program)
    (static : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) state)
    (intendedState : ProtocolState.Intended setup.program state)
    (reached : target ∈ (ProtocolState.behavioralStateStep setup.program
      (setup.intendedOpeningProfile intended) state).support) :
    ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) target ∧
      ProtocolState.Intended setup.program target := by
  classical
  unfold ProtocolState.behavioralStateStep at reached
  split at reached
  · rw [PMF.mem_support_pure_iff] at reached
    subst reached
    exact ⟨static, intendedState⟩
  · obtain ⟨joint, drawn, stepped⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
    rw [independentProduct_support_iff] at drawn
    refine ⟨ProtocolState.staticAt_step setup.program _ _ state joint target static stepped,
      ProtocolState.intended_step setup.program state joint target intendedState
        (fun who => ?_) stepped⟩
    have chosen := drawn who
    have disclosing : Disclosing setup.program (setup.decodeBehavioralProfile
        (CommitmentInterface.values setup.program) (setup.intendedSourceProfile intended) who) :=
      BehavioralPolicy.disclosing_fromProtocol setup.program _ _
        (fun view => setup.intendedSourceProfile_notRefusal intended who (some view))
    change joint who ∈ (((setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
      (setup.intendedSourceProfile intended) who).effectiveOpening setup.program []
        (Revelations.initial setup.context)).protocolAction setup.program
          (ProtocolState.observe who setup.program state)).support at chosen
    rw [BehavioralPolicy.protocolAction_effectiveOpening setup.program _ _ _ disclosing state
      static intendedState] at chosen
    change joint who ∈ ((BehavioralPolicy.fromProtocol setup.program
      (CommitmentInterface.values setup.program)
      (fun view => setup.intendedSourceProfile intended who (some view))).protocolAction
        setup.program (ProtocolState.observe who setup.program state)).support at chosen
    rw [BehavioralPolicy.protocolAction_fromProtocol, PMF.support_map] at chosen
    obtain ⟨choice, member, same⟩ := chosen
    obtain ⟨intendedChoice, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same]
    exact intendedChoice.2

/-- **No failed reveal from intended points.** From a point of the intended game
carrying the program's registry and publication status, the source
continuation of the intended effective opening records no failed reveal. -/
theorem intendedOpening_continuation_failedReveals [Finite Player]
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    ∀ (bound : Nat) (state : SourceProgram.ProtocolState setup.program),
      ProtocolState.remaining setup.program state ≤ bound →
      ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) state →
      ProtocolState.Intended setup.program state →
      ∀ terminal ∈ (ProtocolState.continuationLaw setup.program
          (setup.intendedOpeningProfile intended) state).support,
        ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0 := by
  have := Fintype.ofFinite Player
  intro bound
  induction bound with
  | zero =>
      intro state short _ intendedState terminal member who
      have stopped := (ProtocolState.remaining_zero_iff_terminal setup.program state).mp
        (by omega)
      have law := ProtocolState.continuationLaw_terminal setup.program
        (setup.intendedOpeningProfile intended) state stopped
      have readout : some terminal ∈ (PMF.pure (ProtocolState.readout setup.program state)).support
        := by
        rw [← law]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨terminal, member, rfl⟩
      exact ProtocolState.failedReveals_eq_zero_of_intended who setup.program state intendedState
        ((PMF.mem_support_pure_iff _ _).mp readout).symm
  | succ bound ih =>
      intro state short static intendedState terminal member who
      by_cases stopped : ProtocolState.terminal setup.program state
      · have law := ProtocolState.continuationLaw_terminal setup.program
          (setup.intendedOpeningProfile intended) state stopped
        have readout : some terminal ∈
            (PMF.pure (ProtocolState.readout setup.program state)).support := by
          rw [← law]
          exact (PMF.mem_support_map_iff _ _ _).mpr ⟨terminal, member, rfl⟩
        exact ProtocolState.failedReveals_eq_zero_of_intended who setup.program state
          intendedState ((PMF.mem_support_pure_iff _ _).mp readout).symm
      · rw [← sourceStep_continuation] at member
        obtain ⟨next, reached, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
        obtain ⟨nextStatic, nextIntended⟩ := setup.intendedOpening_step_closed intended state next
          static intendedState reached
        have decreased : ProtocolState.remaining setup.program next + 1 =
            ProtocolState.remaining setup.program state := by
          unfold ProtocolState.behavioralStateStep at reached
          simp only [stopped, ↓reduceIte] at reached
          obtain ⟨joint, _, stepped⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
          exact ProtocolState.remaining_step setup.program state next joint stopped stepped
        exact ih next (by omega) nextStatic nextIntended terminal rest who

end Vegas.SourceProgram.Setup
