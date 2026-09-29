/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceContinuation

/-! # One-step reductions for the actual source protocol

The syntactic policy supplies the action marginals in the existing protocol
step. These equations reduce public sampling, binding and disclosure and
commute with the protocol's residual-state embedding. They introduce no
alternative runner.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

open Classical in
/-- The existing protocol step after drawing the encoded syntactic action
marginals, retaining the protocol's ordinary terminal absorption. -/
def behavioralStateStep {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (state : ProtocolState program) : PMF (ProtocolState program) :=
  if terminal program state then PMF.pure state else
    (independentProduct fun who => (profile who).protocolAction program
      (observe who program state)).bind (step program state)

theorem behavioralStateStep_ret {Γ : SourceCtx Player L}
    (result : List (Player × L.Expr (SourcePublicCtx L Γ) L.int))
    (profile : BehavioralProfile (.ret result)) (state : Config Player L Γ) :
    behavioralStateStep (.ret result) profile state = PMF.pure state := by
  simp [behavioralStateStep, terminal]

section Sample

variable {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
  {fresh : name ∉ Γ.map Prod.fst} {law : L.DistExpr (SourcePublicCtx L Γ) payload}
  {next : SourceProgram Player L ((name, .publicData payload) :: Γ) O}

/-- The source chance step draws the original public distribution and does
not depend on the players' simultaneous action marginals. -/
theorem behavioralStateStep_sample_entry
    (profile : BehavioralProfile (.sample name fresh law next))
    (config : Config Player L Γ) :
    behavioralStateStep (.sample name fresh law next) profile (.inl config) =
      (L.evalDist law (sourcePublicEnv config.state)).map (fun value =>
        Sum.inr (entry next (sampleSuccessor name config value))) := by
  simp only [behavioralStateStep, terminal, ite_false, step, Sum.elim_inl, PMF.bind_const]

theorem behavioralStateStep_sample_tail
    (profile : BehavioralProfile (.sample name fresh law next))
    (state : ProtocolState next) :
    behavioralStateStep (.sample name fresh law next) profile (.inr state) =
      (behavioralStateStep next (afterSample profile) state).map Sum.inr := by
  classical
  by_cases stopped : terminal next state
  · simp [behavioralStateStep, terminal, stopped]
  · simp only [behavioralStateStep, terminal, stopped, ite_false, observe,
      BehavioralPolicy.protocolAction, Sum.elim_inr, afterSample, step, PMF.map_bind]

/-- A source prefix samples once and continues in the same residual protocol. -/
theorem behavioralStatePrefix_sample
    (profile : BehavioralProfile (.sample name fresh law next))
    (config : Config Player L Γ) (count : Nat) :
    (fun distribution => distribution.bind (behavioralStateStep
      (.sample name fresh law next) profile))^[count + 1]
        (PMF.pure (entry _ config)) =
      (L.evalDist law (sourcePublicEnv config.state)).bind fun value =>
        ((fun distribution => distribution.bind
          (behavioralStateStep next (afterSample profile)))^[count]
          (PMF.pure (entry next (sampleSuccessor name config value)))).map Sum.inr := by
  induction count with
  | zero =>
      simp only [entry]
      rw [Function.iterate_one, PMF.pure_bind, behavioralStateStep_sample_entry]
      simp only [Function.iterate_zero_apply, PMF.pure_map, ← ← PMF.bind_pure_comp, Function.comp_def]
      rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, PMF.bind_bind]
      apply bind_congr_on_support _
      intro value _supported
      rw [Function.iterate_succ_apply', PMF.bind_map, PMF.map_bind]
      exact bind_congr_on_support _ fun state _ => behavioralStateStep_sample_tail profile state

end Sample

section Binding

variable {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId}
  {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
  {guard : SourceGuard L Γ owner name payload}
  {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}

/-- Only the owner's actual binding marginal affects the source commitment
step; no support conditioning or new commitment interface is introduced. -/
theorem behavioralStateStep_commit_entry
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (config : Config Player L Γ) :
    behavioralStateStep (.commit name owner fresh guard next) profile (.inl config) =
      (commitKernel profile (config.view owner)).map (fun value =>
        Sum.inr (entry next (commitSuccessor name guard config value))) := by
  classical
  let program := SourceProgram.commit name owner fresh guard next
  let laws who := (profile who).protocolAction program (observe who program (.inl config))
  let advance (action : Option (OwnAction Player L)) :=
    Sum.inr (α := Config Player L Γ)
      (entry next (commitSuccessor name guard config (OwnAction.binding owner name payload action)))
  simp only [behavioralStateStep, terminal, ite_false, step, Sum.elim_inl]
  change ((independentProduct laws).bind fun joint => PMF.pure (advance (joint owner))) = _
  rw [← ← PMF.bind_pure_comp, Function.comp_def]
  change (independentProduct laws).map (advance ∘ fun joint => joint owner) = _
  rw [← PMF.map_comp, FinDist.map_apply_pi]
  simp only [laws, program, BehavioralPolicy.protocolAction, observe, Sum.elim_inl,
    dite_true, PMF.map_comp, Function.comp_def, advance, OwnAction.binding_commit, commitKernel]

theorem behavioralStateStep_commit_tail
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (state : ProtocolState next) :
    behavioralStateStep (.commit name owner fresh guard next) profile (.inr state) =
      (behavioralStateStep next (afterCommit profile) state).map Sum.inr := by
  classical
  by_cases stopped : terminal next state
  · simp [behavioralStateStep, terminal, stopped]
  · simp only [behavioralStateStep, terminal, stopped, ite_false, observe,
      BehavioralPolicy.protocolAction, Sum.elim_inr, afterCommit, step, PMF.map_bind]

/-- A finite source prefix draws the original binding policy and then executes
its residual source protocol, retaining the exact private binding choice. -/
theorem behavioralStatePrefix_commit
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (config : Config Player L Γ) (count : Nat) :
    (fun law => law.bind (behavioralStateStep
      (.commit name owner fresh guard next) profile))^[count + 1]
        (PMF.pure (entry _ config)) =
      (commitKernel profile (config.view owner)).bind fun value =>
        ((fun law => law.bind (behavioralStateStep next (afterCommit profile)))^[count]
          (PMF.pure (entry next (commitSuccessor name guard config value)))).map Sum.inr := by
  induction count with
  | zero =>
      simp only [entry]
      rw [Function.iterate_one, PMF.pure_bind, behavioralStateStep_commit_entry]
      simp only [Function.iterate_zero_apply, PMF.pure_map, ← ← PMF.bind_pure_comp, Function.comp_def]
      rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, PMF.bind_bind]
      apply bind_congr_on_support _
      intro value _supported
      rw [Function.iterate_succ_apply', PMF.bind_map, PMF.map_bind]
      exact bind_congr_on_support _ fun state _ => behavioralStateStep_commit_tail profile state

end Binding

variable {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
  {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
  {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
  {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}

theorem behavioralStateStep_reveal_entry
    (profile : BehavioralProfile (.reveal published owner name fresh source unresolved next))
    (config : Config Player L Γ) :
    behavioralStateStep (.reveal published owner name fresh source unresolved next)
        profile (.inl config) =
      (revealKernel profile (config.view owner)).map (fun disclose =>
        Sum.inr (entry next (revealSuccessor published source config disclose))) := by
  classical
  let program := SourceProgram.reveal published owner name fresh source unresolved next
  let laws who := (profile who).protocolAction program (observe who program (.inl config))
  let advance (action : Option (OwnAction Player L)) :=
    Sum.inr (α := Config Player L Γ)
      (entry next (revealSuccessor published source config (OwnAction.disclosure action)))
  simp only [behavioralStateStep, terminal, ite_false, step, Sum.elim_inl]
  change ((independentProduct laws).bind fun joint => PMF.pure (advance (joint owner))) = _
  rw [← ← PMF.bind_pure_comp, Function.comp_def]
  change (independentProduct laws).map (advance ∘ fun joint => joint owner) = _
  rw [← PMF.map_comp, FinDist.map_apply_pi]
  simp only [laws, program, BehavioralPolicy.protocolAction, observe, Sum.elim_inl,
    dite_true, PMF.map_comp, Function.comp_def, advance, OwnAction.disclosure, revealKernel]

theorem behavioralStateStep_reveal_tail
    (profile : BehavioralProfile (.reveal published owner name fresh source unresolved next))
    (state : ProtocolState next) :
    behavioralStateStep (.reveal published owner name fresh source unresolved next)
        profile (.inr state) =
      (behavioralStateStep next (afterReveal profile) state).map Sum.inr := by
  classical
  by_cases stopped : terminal next state
  · simp [behavioralStateStep, terminal, stopped]
  · simp only [behavioralStateStep, terminal, stopped, ite_false, observe,
      BehavioralPolicy.protocolAction, Sum.elim_inr, afterReveal, step, PMF.map_bind]

/-- A finite source prefix first draws its actual reveal choice and then
executes the residual source protocol. -/
theorem behavioralStatePrefix_reveal
    (profile : BehavioralProfile (.reveal published owner name fresh source unresolved next))
    (config : Config Player L Γ) (count : Nat) :
    (fun law => law.bind (behavioralStateStep
      (.reveal published owner name fresh source unresolved next) profile))^[count + 1]
        (PMF.pure (entry _ config)) =
      (revealKernel profile (config.view owner)).bind fun disclose =>
        ((fun law => law.bind (behavioralStateStep next (afterReveal profile)))^[count]
          (PMF.pure (entry next
            (revealSuccessor published source config disclose)))).map Sum.inr := by
  induction count with
  | zero =>
      simp only [entry]
      rw [Function.iterate_one, PMF.pure_bind, behavioralStateStep_reveal_entry]
      simp only [Function.iterate_zero_apply, PMF.pure_map, ← ← PMF.bind_pure_comp, Function.comp_def]
      rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, PMF.bind_bind]
      apply bind_congr_on_support _
      intro disclose _supported
      rw [Function.iterate_succ_apply', PMF.bind_map, PMF.map_bind]
      exact bind_congr_on_support _ fun state _ => behavioralStateStep_reveal_tail profile state

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)

/-- The actual initial protocol step samples setup once, irrespective of the
strategic profile. Correlations in the setup law are retained. -/
theorem behavioralStateStep_none
    (profile : Profile (setup.informationModel admission).behavioralSignature) :
    setup.behavioralStateStep admission profile none =
      setup.initialLaw.map (fun initial =>
        some (ProtocolState.entry setup.program (setup.initialConfig initial))) := by
  simp [behavioralStateStep, protocolStep, PMF.bind_const]

/-- Encoding the syntactic policies gives exactly their action-marginal
kernel after setup, with only the existing `some` state embedding. -/
theorem behavioralStateStep_encoded_some
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission)
    (state : SourceProgram.ProtocolState setup.program) :
    setup.behavioralStateStep admission
        (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who))
        (some state) =
      (ProtocolState.behavioralStateStep setup.program profile state).map some := by
  classical
  by_cases stopped : ProtocolState.terminal setup.program state
  · simp [behavioralStateStep, ProtocolState.behavioralStateStep, stopped]
  · simp only [behavioralStateStep, Option.elim_some, stopped, ite_false, protocolStep,
      ProtocolState.behavioralStateStep, PMF.map_bind]
    let choices who := setup.toProtocolBehavioralPolicy admission who
      (profile who) (permitted who) (setup.protocolObserve who (some state))
    have factors :
        independentProduct (fun who => (profile who).protocolAction setup.program
          (ProtocolState.observe who setup.program state)) =
        (independentProduct choices).map (fun selected who => (selected who).1) := by
      rw [← FinDist.pi_map]
      congr 1
      funext who
      exact (setup.toProtocolBehavioralPolicy_map_val admission who (profile who)
        (permitted who) (some (ProtocolState.observe who setup.program state))).symm
    rw [factors, PMF.bind_map]

end Setup

end Vegas.SourceProgram
