/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefixFactorization
import Vegas.Game.SourceServiceLaw

/-! # Exact timed continuations at supported source boundaries

The existing joint prefix induction also starts at an arbitrary supported
typed checkpoint. Its terminal marginal preserves the entire typed source
store, including persistent initial parameters and public outcomes. The
physical continuation uses the existing remaining service blocks.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem statePrefix_readout
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (source : Config Player L Γ) :
    ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[eventCount program]
      (PMF.pure (ProtocolState.entry program source))).map (ProtocolState.readout program) =
        (runFrom program profile source).map some := by
  induction program with
  | ret payoffs =>
      simp only [eventCount, Function.iterate_zero_apply, ProtocolState.entry,
        ProtocolState.readout, runFrom, runWith, PMF.pure_map]
  | sample name fresh distribution next ih =>
      have law := ProtocolState.behavioralStatePrefix_sample profile source (eventCount next)
      have mapped := congrArg (PMF.map (ProtocolState.readout _)) law
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
        ProtocolState.readout, Sum.elim_inr] at mapped
      refine mapped.trans ?_
      rw [runFrom_sample, PMF.map_bind]
      exact bind_congr_on_support _ fun value _ => ih (afterSample profile)
        (sampleSuccessor name source value)
  | commit name owner fresh guard next ih =>
      have law := ProtocolState.behavioralStatePrefix_commit profile source (eventCount next)
      have mapped := congrArg (PMF.map (ProtocolState.readout _)) law
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
        ProtocolState.readout, Sum.elim_inr] at mapped
      refine mapped.trans ?_
      rw [runFrom_commit, PMF.map_bind]
      exact bind_congr_on_support _ fun value _ => ih (afterCommit profile)
        (commitSuccessor name guard source value)
  | reveal published owner name fresh binding unresolved next ih =>
      have law := ProtocolState.behavioralStatePrefix_reveal profile source (eventCount next)
      have mapped := congrArg (PMF.map (ProtocolState.readout _)) law
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
        ProtocolState.readout, Sum.elim_inr] at mapped
      refine mapped.trans ?_
      rw [runFrom_reveal, PMF.map_bind]
      exact bind_congr_on_support _ fun disclose _ => ih (afterReveal profile)
        (revealSuccessor published binding source disclose)

/-- One source step followed by the source continuation is the source
continuation. -/
theorem sourceStep_continuation
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (state : ProtocolState program) :
    (ProtocolState.behavioralStateStep program profile state).bind
      (ProtocolState.continuationLaw program profile) =
        ProtocolState.continuationLaw program profile state := by
  classical
  unfold ProtocolState.behavioralStateStep
  split
  · exact PMF.pure_bind _ _
  · rename_i running
    exact ProtocolState.continuationLaw_behavioral_step program profile state running
      (independentProduct fun who => (profile who).protocolAction program
        (ProtocolState.observe who program state)) (fun who => independentProduct_map_eval _ who)

private theorem liftedPrefix_continuation
    {Γ Δ : SourceCtx Player L} {names restNames : Finset VarId}
    (whole : SourceProgram Player L Γ names) (wholeProfile : BehavioralProfile whole)
    (program : SourceProgram Player L Δ restNames) (profile : BehavioralProfile program)
    (lift : ProtocolState program → ProtocolState whole)
    (commutes : ∀ state, ProtocolState.behavioralStateStep whole wholeProfile (lift state) =
      (ProtocolState.behavioralStateStep program profile state).map lift)
    (source : Config Player L Δ) (count : Nat) :
    ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
      (PMF.pure (ProtocolState.entry program source))).bind
        (fun state => ProtocolState.continuationLaw whole wholeProfile (lift state)) =
      ProtocolState.continuationLaw whole wholeProfile
        (lift (ProtocolState.entry program source)) := by
  induction count with
  | zero => simp only [Function.iterate_zero_apply, PMF.pure_bind]
  | succ count ih =>
      rw [Function.iterate_succ_apply', PMF.bind_bind]
      trans ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
        (PMF.pure (ProtocolState.entry program source))).bind
          (fun state => ProtocolState.continuationLaw whole wholeProfile (lift state))
      · apply bind_congr_on_support _
        intro state _
        refine (PMF.bind_map _ lift
          (ProtocolState.continuationLaw whole wholeProfile)).symm.trans ?_
        rw [← commutes]
        exact sourceStep_continuation whole wholeProfile (lift state)
      · exact ih

end Vegas
