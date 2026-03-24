import Vegas.MAID.CompileV
import Vegas.StrategicPMF
import GameTheory.Languages.MAID.FoldEval

/-!
# Definitions for VegasMAID Bridge Proofs

**Status: top-down development — interfaces first, proofs later.**

Import policy: only CompileV.lean + Compile.lean + GameTheory MAID.
Do NOT reference theorems from Correctness.lean or Reflection.lean.
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] {L : IExpr} {B : MAIDBackend Player L}

/-- Abbreviation for the compiled VegasMAID and its derived MAID structure. -/
noncomputable abbrev compiledStruct
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False) :=
  letI := B.fintypePlayer
  (compileVegasMAID B p hl hd hfresh hpub env).toStruct

/-- The underlying compile state, for definitions that need it. -/
noncomputable abbrev compiledState
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p) :=
  MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty

/-! ## Semantics -/

/-- MAID semantics for the compiled VegasMAID structure. -/
noncomputable def vegasMAIDSem
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False) :
    Sem (fp := B.fintypePlayer) (compiledStruct B p env hl hd hfresh hpub) := by
  haveI : Fintype Player := B.fintypePlayer
  exact (compiledState B p env hl hd).toSem

/-! ## Raw environment conversion -/

/-- Convert a MAID total assignment to a raw node environment. -/
noncomputable def rawOfTAssignV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (a : TAssign (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub)) :
    RawNodeEnv L :=
  haveI : Fintype Player := B.fintypePlayer
  let st := compiledState B p env hl hd
  fun i =>
    if hi : i < st.nextId then
      MAIDCompileState.taggedOfVal (st.descAt ⟨i, hi⟩) (a ⟨i, hi⟩)
    else
      none

/-! ## Outcome extraction -/

/-- Deterministic outcome extraction: replay the program reading node values
from a raw environment. Redefined here (independent of Correctness.lean). -/
noncomputable def extractOutcomeAux
    (B : MAIDBackend Player L) :
    {Γ : VCtx Player L} →
    VegasCore Player L Γ →
    (RawNodeEnv L → VEnv (Player := Player) L Γ) →
    Nat → (RawNodeEnv L → Outcome Player)
  | _, .ret u, ρ, _ =>
      fun raw => evalPayoffs u (ρ raw)
  | _, .letExpr _x e k, ρ, nextId =>
      extractOutcomeAux B k
        (fun raw => VEnv.cons (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        nextId
  | _, .sample _x τ _m _D' k, ρ, nextId =>
      extractOutcomeAux B k
        (fun raw => VEnv.cons
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
        (nextId + 1)
  | _, .commit (b := b) _x _who _R k, ρ, nextId =>
      extractOutcomeAux B k
        (fun raw => VEnv.cons
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
        (nextId + 1)
  | _, .reveal (b := b) y _who _x hx k, ρ, nextId =>
      extractOutcomeAux B k
        (fun raw =>
          let v : L.Val b := VEnv.get (L := L) (ρ raw) hx
          VEnv.cons (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId

/-- Extract Vegas outcomes from a MAID total assignment. -/
noncomputable def extractOutcomeV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False) :
    TAssign (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub) → Outcome Player :=
  fun a => extractOutcomeAux B p (fun _ => env) 0
    (rawOfTAssignV B p env hl hd hfresh hpub a)

/-! ## Policy translation (sorry'd) -/

/-- Translate a Vegas behavioral profile to a MAID policy. -/
noncomputable def compiledPolicyV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (β : ProgramBehavioralProfile p) :
    Policy (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub) := by
  sorry

/-- Reflect a MAID policy to a Vegas PMF behavioral profile. -/
noncomputable def reflectPolicyV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (pol : Policy (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub)) :
    ProgramBehavioralProfilePMF p := by
  sorry

/-- Compile a Vegas pure profile to a MAID pure policy. -/
noncomputable def compilePureProfileV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (π : ProgramPureProfile (P := Player) (L := L) p) :
    PurePolicy (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub) := by
  sorry

end Vegas
