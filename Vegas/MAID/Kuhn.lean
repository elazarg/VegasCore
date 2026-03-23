import GameTheory.Languages.MAID.Kuhn
import Vegas.StrategicPMF
import Vegas.MAID.Correctness
import Vegas.MAID.PureBridge
import Vegas.MAID.PerfectRecall
import Vegas.MAID.Reflection

/-!
# Vegas Kuhn Theorem via MAID

The Vegas Kuhn theorem: for a well-formed Vegas program with perfect recall,
every product mixed strategy over pure Vegas strategies is outcome-equivalent
to some behavioral Vegas profile (PMF-valued).

## Proof outline

1. Compile to MAID: `st := MAIDCompileState.ofProg B p ...`
2. Perfect recall: `compiledStruct_perfectRecall` establishes `S.PerfectRecall`
3. Compile pure strategies: `compilePureProfile st π` for each pure profile `π`
4. Apply `kuhn_mixed_to_behavioral` from the MAID library
5. Use `frontierEval_eq_evalAssignDist` to work with `evalAssignDist`
6. Reflect the MAID behavioral witness: `reflectPolicy st pol`
7. Chain `reflectPolicy_outcomeDistBehavioralPMF_eq` with `maid_pure_bridge`

## Known limitation

The witness is a `ProgramBehavioralProfilePMF` (real-valued PMF), not a
`ProgramBehavioralProfile` (rational FDist-valued). This is because the MAID
Kuhn construction works over PMF throughout. A future strengthening of MAID
Kuhn to preserve rationality would eliminate this gap.
-/

namespace Vegas

open MAID Math.PMFProduct

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Bridge sub-lemmas for the Kuhn proof -/

/-- Compile a single player's pure strategy to a MAID pure strategy.
This is the per-player version of `compilePureProfile`: given player `who`'s
strategy and a default strategy for all other players, produce a MAID pure
strategy for `who`. -/
noncomputable def compilePureStrategyOfPlayer
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hl : Legal p) (ha : DistinctActs p) (hd : NormalizedDists p)
    (env : VEnv (Player := P) L Γ)
    (who : P)
    (s : ProgramPureStrategy (P := P) (L := L) who p)
    (default_others : ∀ i, i ≠ who → ProgramPureStrategy (P := P) (L := L) i p) :
    let _ : Fintype P := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    @MAID.PureStrategy P _ B.fintypePlayer st.nextId st.toStruct who := by
  intro _inst st
  -- Build a full profile using s for `who` and defaults for others
  let π : ProgramPureProfile (P := P) (L := L) p := fun i =>
    if h : i = who then h ▸ s else default_others i h
  exact compilePureProfile B p hl ha hd env π who

/-- The RHS of the MAID Kuhn theorem, expressed through Vegas pure outcome
distributions via the pure bridge. -/
theorem maid_kuhn_rhs_eq_vegas_mixed
    (B : MAIDBackend P L)
    (LF : FiniteValuation L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hl : Legal p) (ha : DistinctActs p)
    (hd : NormalizedDists p) (hwf : WF p)
    (μ : ∀ who, PMF (ProgramPureStrategy (P := P) (L := L) who p)) :
    let _ : Fintype P := B.fintypePlayer
    let _ : ∀ who, Fintype (ProgramPureStrategy (P := P) (L := L) who p) :=
      fun who => ProgramPureStrategy.instFintype LF who p
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let extract : @TAssign P _ B.fintypePlayer st.nextId S → Outcome P :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    -- For any product of compiled MAID pure strategies that commutes with
    -- the Vegas pure profiles, the mixed MAID outcome = mixed Vegas outcome
    ∀ (μ_maid : ∀ who, PMF (@PureStrategy P _ B.fintypePlayer st.nextId S who))
      (hcomm : ∀ π : ProgramPureProfile (P := P) (L := L) p,
        PMF.map extract
          (frontierEval S sem (pureToPolicy (compilePureProfile B p hl ha hd env π))) =
        (outcomeDistPure p π env).toPMF (outcomeDistPure_totalWeight_eq_one hd)),
      (pmfPi μ_maid).bind (fun π_maid =>
        PMF.map extract (frontierEval S sem (pureToPolicy π_maid))) =
      (pmfPi μ).bind (fun π =>
        (outcomeDistPure p π env).toPMF (outcomeDistPure_totalWeight_eq_one hd)) := by
  sorry

/-! ## Main theorem -/

/-- **Vegas Kuhn theorem (mixed → behavioral)**: under well-formedness (which
implies perfect recall after MAID compilation), every product mixed strategy
over fixed-program pure strategies is outcome-equivalent to some PMF-valued
behavioral profile.

The LHS is the expected outcome under the product mixed strategy (each player
independently samples a pure strategy, then all play their sampled strategies
simultaneously). The RHS is the outcome under a single behavioral profile
that achieves the same distribution. -/
theorem vegas_kuhn_mixed_to_behavioral
    (B : MAIDBackend P L)
    (LF : FiniteValuation L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hl : Legal p) (ha : DistinctActs p)
    (hd : NormalizedDists p) (hwf : WF p)
    (μ : ∀ who, PMF (ProgramPureStrategy (P := P) (L := L) who p)) :
    let _ : Fintype P := B.fintypePlayer
    let _ : ∀ who, Fintype (ProgramPureStrategy (P := P) (L := L) who p) :=
      fun who => ProgramPureStrategy.instFintype LF who p
    ∃ σ : ProgramBehavioralProfilePMF (P := P) (L := L) p,
      outcomeDistBehavioralPMF p hd σ env =
        (pmfPi μ).bind (fun π =>
          (outcomeDistPure p π env).toPMF
            (outcomeDistPure_totalWeight_eq_one hd)) := by
  intro _instFin _instFinStrat
  -- Step 1: Compile to MAID
  let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
  let S := st.toStruct
  let sem := MAIDCompileState.toSem st
  -- Step 2: Establish perfect recall
  have hPR : S.PerfectRecall := compiledStruct_perfectRecall B p env hl ha hd hwf
  -- Step 3: Compile pure strategies to MAID
  -- (For each pure profile π, compilePureProfile gives a MAID PurePolicy.
  -- We need per-player PMFs over MAID PureStrategies.)
  -- Step 4: Apply MAID Kuhn to get behavioral witness
  -- kuhn_mixed_to_behavioral : S.PerfectRecall → (∀ p, PMF (PureStrategy S p)) →
  --   ∃ pol, frontierEval S sem pol = mixed
  -- Step 5: Reflect the MAID behavioral policy to Vegas PMF behavioral
  -- Step 6: Chain the bridges
  sorry

end Vegas
