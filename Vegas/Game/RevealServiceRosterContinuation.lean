/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefix
import Vegas.Pending.ReactiveOpeningSettlement
import Vegas.Game.SourceStateKernel
import Vegas.Game.SourceInformation
import Vegas.Game.SourcePrefixKernel
import Vegas.Game.RevealServicePayoffs
import Vegas.Compile.EventGraphReadoutComplete

/-! # Source continuations after completed roster phases

The existing public checkpoint locates the source protocol state inside the
original program. Executing the remaining actual roster blocks has its exact
source continuation law. Actual response counts and published-message invariants
are retained; there is no reset of private recall or passive observations.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem decodePrefix_terminal_readout
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (reveals : program.RevealOnly)
    (refs : ContextRefs layout Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L) :
    (decodePrefix? program refs revelations outputs (eventCount program) store history).bind
        (ProtocolState.readout program) =
      decodeState? (terminalRefsWith program refs outputs) store := by
  induction program with
  | ret payoffs =>
      simp only [eventCount, decodePrefix?, terminalRefsWith]
      cases decoded : decodeState? refs store <;> rfl
  | sample name fresh law next ih => exact reveals.elim
  | commit name owner fresh guard next ih => exact reveals.elim
  | reveal published owner name fresh selected unresolved next ih =>
      simp only [eventCount, decodePrefix?, terminalRefsWith, Option.bind_map]
      exact ih reveals _ _ _

private theorem source_prefix_terminal_readout
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (reveals : program.RevealOnly)
    (profile : BehavioralProfile program) (source : Config Player L Γ) :
    ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[eventCount program]
      (PMF.pure (ProtocolState.entry program source))).map (ProtocolState.readout program) =
      (runFrom program profile source).map some := by
  induction program with
  | ret payoffs =>
      simp [eventCount, runFrom, runWith, ProtocolState.readout, ProtocolState.entry, PMF.pure_map]
  | sample name fresh law next ih => exact reveals.elim
  | commit name owner fresh guard next ih => exact reveals.elim
  | reveal published owner name fresh selected unresolved next ih =>
      rw [eventCount, ProtocolState.behavioralStatePrefix_reveal, PMF.map_bind,
        runFrom_reveal, PMF.map_bind]
      apply bind_congr_on_support _
      intro disclose _
      rw [PMF.map_comp]
      exact ih reveals (afterReveal profile) (revealSuccessor published selected source disclose)

omit [Fintype Player] in
/-- The compiler's terminal context contains every event output. Consequently
the explicit terminal-cut guard is redundant with successful typed decoding,
even at an arbitrary structurally valid native control state, in every
dependency mode. -/
theorem serviceSourceReadout_eq_decode (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (control : (serviceApplication setup mode deadline leaks).Control) :
    serviceSourceReadout setup mode deadline leaks (some control) =
      decodeState? (terminalRefs setup.program) control.execution.application.config.store := by
  unfold serviceSourceReadout
  rw [Option.bind_some]
  cases decoded : decodeState? (terminalRefs setup.program)
      control.execution.application.config.store with
  | none => simp only [decoded, ite_self]
  | some source =>
      have complete := terminal_decode_complete setup.program mode
        control.execution.application.config (by rw [decoded]; rfl)
      dsimp only
      rw [ite_eq_left complete, decoded]

omit [Fintype Player] in
theorem sourceReadout_eq_decode (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (control : (application setup leaks).Control) :
    sourceReadout setup leaks (some control) =
      decodeState? (terminalRefs setup.program) control.execution.application.config.store :=
  serviceSourceReadout_eq_decode setup leaks control

end Vegas
