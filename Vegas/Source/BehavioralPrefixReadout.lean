module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT License (see LICENSE). -/

public import Vegas.Source.BehavioralStateKernel
public import Vegas.Source.InitialState

@[expose] public section

/-! # Typed cells and public defaults at source prefixes -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The typed environment at the current instruction and the full public default record. -/
abbrev PrefixReadout (Player : Type) (L : IExpr) :=
  Σ Γ : SourceCtx Player L, State L Γ × DefaultHistory Player

/-- Read the source cells and public defaults at an arbitrary source program point. -/
def ProtocolState.prefixReadout : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → PrefixReadout Player L
  | _, _, .ret _, config => ⟨_, config.state, config.defaults⟩
  | _, _, .sample _ _ _ next, state =>
      state.elim (fun config => ⟨_, config.state, config.defaults⟩) (prefixReadout next)
  | _, _, .commit _ _ _ _ next, state =>
      state.elim (fun config => ⟨_, config.state, config.defaults⟩) (prefixReadout next)
  | _, _, .reveal _ _ _ _ _ _ next, state =>
      state.elim (fun config => ⟨_, config.state, config.defaults⟩) (prefixReadout next)

/-- The initial default record is recoverable by removing the entries for the suffix. -/
private theorem initialDefaults_runFrom
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) (final : Config Player L program.terminalCtx)
    (reached : final ∈ (runFrom program profile config).support) :
    DefaultHistory.back^[instructionCount program] final.defaults = config.defaults := by
  induction program with
  | ret payoffs =>
      have same := (PMF.mem_support_pure_iff _ _).mp reached
      subst final
      rfl
  | sample name fresh law next ih =>
      rw [runFrom_sample, PMF.support_bind] at reached
      obtain ⟨value, _, present⟩ := Set.mem_iUnion₂.mp reached
      rw [instructionCount, Function.iterate_succ_apply', ih _ _ _ present]
      exact DefaultHistory.back_record _ _
  | commit name owner fresh guard next ih =>
      rw [runFrom_commit, PMF.support_bind] at reached
      obtain ⟨choice, _, present⟩ := Set.mem_iUnion₂.mp reached
      rw [instructionCount, Function.iterate_succ_apply', ih _ _ _ present]
      exact DefaultHistory.back_record _ _
  | reveal published owner name fresh selected unresolved next ih =>
      rw [runFrom_reveal, PMF.support_bind] at reached
      obtain ⟨disclose, _, present⟩ := Set.mem_iUnion₂.mp reached
      rw [instructionCount, Function.iterate_succ_apply', ih _ _ _ present]
      exact DefaultHistory.back_record _ _

/-- Later instructions only add typed cells and public default entries, so the terminal
readout determines the readout after any given number of instructions. -/
def terminalPrefixReadout : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Nat →
      State L program.terminalCtx × DefaultHistory Player → PrefixReadout Player L
  | Γ, _, program, 0, final =>
      ⟨Γ, initialState program final.1, DefaultHistory.back^[instructionCount program] final.2⟩
  | Γ, _, .ret _, _ + 1, final => ⟨Γ, final⟩
  | _, _, .sample _ _ _ next, count + 1, final => terminalPrefixReadout next count final
  | _, _, .commit _ _ _ _ next, count + 1, final => terminalPrefixReadout next count final
  | _, _, .reveal _ _ _ _ _ _ next, count + 1, final => terminalPrefixReadout next count final

private theorem ProtocolState.prefixReadout_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    prefixReadout program (entry program config) = ⟨Γ, config.state, config.defaults⟩ := by
  cases program <;> rfl

private theorem terminalPrefixReadout_zero
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) :
    (runFrom program profile config).map (fun final =>
      terminalPrefixReadout program 0 (final.state, final.defaults)) =
      PMF.pure ⟨Γ, config.state, config.defaults⟩ := by
  rw [map_congr_on_support _ (g := fun _ => ⟨Γ, config.state, config.defaults⟩) ?_,
    pmf_map_fun_const]
  intro final reached
  simp only [terminalPrefixReadout, initialState_runFrom _ _ _ _ reached,
    initialDefaults_runFrom _ _ _ _ reached]

/-- Reading the ordinary behavioral kernel at any finite prefix agrees with
reading the corresponding retained fields of the terminal run. -/
theorem behavioralStatePrefix_readout_eq [Fintype Player]
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (profile : BehavioralProfile program) (config : Config Player L Γ) (count : Nat) :
    ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
      (PMF.pure (ProtocolState.entry program config))).map (ProtocolState.prefixReadout program) =
      (runFrom program profile config).map (fun final =>
        terminalPrefixReadout program count (final.state, final.defaults)) := by
  induction program generalizing count with
  | ret payoffs =>
      have fixed :
          (fun law => law.bind (ProtocolState.behavioralStateStep (.ret payoffs) profile))^[count]
            (PMF.pure (ProtocolState.entry (.ret payoffs) config)) = PMF.pure config := by
        induction count with
        | zero => rfl
        | succ count ih =>
            rw [Function.iterate_succ_apply', ih, PMF.pure_bind]
            simp [ProtocolState.behavioralStateStep, ProtocolState.terminal]
      rw [fixed]
      cases count <;> rfl
  | sample name fresh law next ih =>
      cases count with
      | zero =>
          rw [Function.iterate_zero_apply, PMF.pure_map, ProtocolState.prefixReadout_entry,
            terminalPrefixReadout_zero]
      | succ count =>
          rw [ProtocolState.behavioralStatePrefix_sample, runFrom_sample]
          simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, terminalPrefixReadout,
            ProtocolState.prefixReadout, Sum.elim_inr]
          exact bind_congr_on_support _ fun value _ => ih _ _ _
  | commit name owner fresh guard next ih =>
      cases count with
      | zero =>
          rw [Function.iterate_zero_apply, PMF.pure_map, ProtocolState.prefixReadout_entry,
            terminalPrefixReadout_zero]
      | succ count =>
          rw [ProtocolState.behavioralStatePrefix_commit, runFrom_commit]
          simp only [Config.view_defaulted, PMF.map_bind, PMF.map_comp, Function.comp_def,
            terminalPrefixReadout, ProtocolState.prefixReadout, Sum.elim_inr]
          exact bind_congr_on_support _ fun choice _ => ih _ _ _
  | reveal published owner name fresh selected unresolved next ih =>
      cases count with
      | zero =>
          rw [Function.iterate_zero_apply, PMF.pure_map, ProtocolState.prefixReadout_entry,
            terminalPrefixReadout_zero]
      | succ count =>
          rw [ProtocolState.behavioralStatePrefix_reveal, runFrom_reveal]
          simp only [Config.view_defaulted, PMF.map_bind, PMF.map_comp, Function.comp_def,
            terminalPrefixReadout, ProtocolState.prefixReadout, Sum.elim_inr]
          exact bind_congr_on_support _ fun disclose _ => ih _ _ _

/-- Prefix readout is a projection of the terminal law for a distributed initialization. -/
theorem Setup.behavioralStatePrefix_readout_eq [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) (profile : BehavioralProfile setup.program)
    (count : Nat) :
    (setup.initialDistribution.bind fun initial =>
      (fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[count]
        (PMF.pure (ProtocolState.entry setup.program (Config.initial initial)))).map
          (ProtocolState.prefixReadout setup.program) =
      (setup.run profile).map (fun final =>
        terminalPrefixReadout setup.program count (final.state, final.defaults)) := by
  simp only [Setup.run, SourceProgram.run, PMF.map_bind]
  exact bind_congr_on_support _ fun initial _ =>
    SourceProgram.behavioralStatePrefix_readout_eq setup.program profile (Config.initial initial)
      count

end Vegas.SourceProgram
