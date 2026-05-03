import GameTheory.Languages.FOSG.Strategy
import Vegas.Config
import Vegas.WFProgram

/-!
# Vegas FOSG runtime surface

This file contains the game-theoretic view over neutral Vegas runtime
configurations: active players, broad action availability, and basic
joint-action legality facts. The neutral configuration type itself lives in
`Vegas.Config`.
-/

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A static FOSG action alphabet for Vegas: a player action is a typed value.

The player argument is intentionally unused. FOSG requires a per-player static
action type, while a Vegas commit node chooses the active player and the type
of value expected at that node. Node-local availability below filters this
static alphabet down to the values of the demanded type satisfying the guard.

This broad alphabet is used only for the suffix-based checked transition
semantics. The executable FOSG target uses the finite `ProgramAction` alphabet:
otherwise `Fintype (Action L who)` would require finiteness of `L.Ty`, not just
finiteness of values that actually occur in `g`.
-/
abbrev Action (L : IExpr) (_who : P) : Type :=
  Sigma L.Val

/-- Compatibility alias for the neutral runtime configuration type. The
canonical definition lives in `Vegas.Config`. -/
abbrev World (P : Type) [DecidableEq P] (L : IExpr) :=
  Vegas.World P L

/-- Compatibility alias for neutral Vegas terminality. The canonical definition
lives in `Vegas.Config`. -/
abbrev terminal (w : World P L) : Prop :=
  Vegas.terminal w

/-- Compatibility alias for neutral syntax-step counting. The canonical
definition lives in `Vegas.Config`. -/
abbrev syntaxSteps :
    {Γ : VCtx P L} → VegasCore P L Γ → Nat :=
  Vegas.syntaxSteps

/-- The only strategic FOSG states are Vegas `commit` nodes. -/
def active (w : World P L) : Finset P :=
  match w.prog with
  | .commit _ who _ _ => {who}
  | _ => ∅

/-- A world known, up to context transport, to be an owned commit has that
owner active. -/
theorem active_mem_of_eq_commit
    {Γc Γ : VCtx P L} {p : VegasCore P L Γc}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (hΓ : Γc = Γ) (hp : hΓ ▸ p = VegasCore.commit x who R k)
    (env : VEnv L Γc) :
    who ∈ active ({ Γ := Γc, prog := p, env := env } : World P L) := by
  cases p with
  | ret payoffs =>
      cases hΓ
      simp at hp
  | letExpr y e k =>
      cases hΓ
      simp at hp
  | sample y D k =>
      cases hΓ
      simp at hp
  | reveal y owner z hz k =>
      cases hΓ
      simp at hp
  | commit y owner R' k' =>
      cases hΓ
      simp only [VegasCore.commit.injEq] at hp
      rcases hp with ⟨_hxy, howner, _hb, _hR, _hk⟩
      subst howner
      simp [active]

/-- Node-local action availability.

At a commit node, the owner may choose exactly values of the committed type
that satisfy the guard in the current erased environment. Every other player,
and every non-commit node, has no available concrete action.
-/
def availableActions (w : World P L) (who : P) : Set (Action (P := P) L who) :=
  match w.prog with
  | .commit _ owner (b := b) R _ =>
      if owner = who then
        {a | ∃ v : L.Val b,
          a = Sigma.mk b v ∧
            evalGuard (Player := P) (L := L) R v (VEnv.eraseEnv w.env) = true}
      else
        ∅
  | _ => ∅

/-- Broad-alphabet availability at a world known, up to context transport, to
be a particular owned commit site. -/
theorem availableActions_of_eq_commit
    {Γc Γ : VCtx P L} {p : VegasCore P L Γc}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (hΓ : Γc = Γ) (hp : hΓ ▸ p = VegasCore.commit x who R k)
    (env : VEnv L Γc) {ai : Action (P := P) L who}
    (hact : ai ∈
      availableActions ({ Γ := Γc, prog := p, env := env } : World P L)
        who) :
    ∃ v : L.Val b,
      ai = Sigma.mk b v ∧
        evalGuard (Player := P) (L := L) R v
          (VEnv.eraseEnv (hΓ ▸ env)) = true := by
  cases p with
  | ret payoffs =>
      cases hΓ
      simp at hp
  | letExpr y e k =>
      cases hΓ
      simp at hp
  | sample y D k =>
      cases hΓ
      simp at hp
  | reveal y owner z hz k =>
      cases hΓ
      simp at hp
  | commit y owner R' k' =>
      cases hΓ
      simp only [VegasCore.commit.injEq] at hp
      rcases hp with ⟨hxy, howner, hb, hR, _hk⟩
      subst hxy
      subst howner
      subst hb
      cases hR
      simpa [availableActions] using hact

abbrev JointAction (P : Type) [DecidableEq P] (L : IExpr) : Type :=
  GameTheory.JointAction (fun who : P => Action (P := P) L who)

/-- FOSG joint-action legality for the structural Vegas/FOSG layer. -/
abbrev JointActionLegal (w : World P L) (a : JointAction P L) : Prop :=
  GameTheory.JointActionLegal
    (fun who : P => Action (P := P) L who)
    active
    terminal
    availableActions
    w
    a

/-- A joint action where exactly `who` commits to `v`. -/
def commitJointAction (who : P) {b : L.Ty} (v : L.Val b) : JointAction P L :=
  fun i => if i = who then some (Sigma.mk b v) else none

@[simp] theorem terminal_ret
    {Γ : VCtx P L} {env : VEnv L Γ}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    terminal ({ Γ := Γ, prog := VegasCore.ret payoffs, env := env } : World P L) := by
  simp [terminal]

@[simp] theorem active_ret
    {Γ : VCtx P L} {env : VEnv L Γ}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    active ({ Γ := Γ, prog := VegasCore.ret payoffs, env := env } : World P L) = ∅ := by
  simp [active]

theorem terminal_active_eq_empty {w : World P L} :
    terminal w → active w = ∅ := by
  cases w with
  | mk Γ prog env =>
      cases prog <;> simp [terminal, active]

theorem terminal_no_legal {w : World P L} {a : JointAction P L} :
    terminal w → ¬ JointActionLegal w a := by
  intro hterm hlegal
  exact hlegal.1 hterm

/-- Internal Vegas states have a legal FOSG no-op joint action. -/
theorem noop_legal_of_active_empty {w : World P L}
    (hterm : ¬ terminal w) (hactive : active w = ∅) :
    JointActionLegal w
      (GameTheory.FOSG.noopAction (fun who : P => Action (P := P) L who)) := by
  refine ⟨hterm, ?_⟩
  intro i
  simp [GameTheory.FOSG.noopAction, hactive]

/-- Program-level `Legal` is exactly what is needed to avoid FOSG deadlock:
every nonterminal Vegas configuration admits at least one legal joint action.

For commit states this witness is the guard-satisfying value promised by
`Legal`; for administrative and nature/reveal states it is the all-`none`
joint action.
-/
theorem exists_jointActionLegal_of_legal
    (w : World P L) (hlegal : Legal w.prog) (hterm : ¬ terminal w) :
    ∃ a : JointAction P L, JointActionLegal w a := by
  cases w with
  | mk Γ prog env =>
      cases prog with
      | ret payoffs =>
          simp [terminal] at hterm
      | letExpr x e k =>
          refine ⟨GameTheory.FOSG.noopAction (fun who : P => Action (P := P) L who), ?_⟩
          refine ⟨by simp [terminal], ?_⟩
          intro i
          simp [GameTheory.FOSG.noopAction, active]
      | sample x D k =>
          refine ⟨GameTheory.FOSG.noopAction (fun who : P => Action (P := P) L who), ?_⟩
          refine ⟨by simp [terminal], ?_⟩
          intro i
          simp [GameTheory.FOSG.noopAction, active]
      | commit x who R k =>
          rcases hlegal.1 (VEnv.eraseEnv env) with ⟨v, hv⟩
          refine ⟨commitJointAction (L := L) who v, ?_⟩
          refine ⟨by simp [terminal], ?_⟩
          intro i
          by_cases hi : i = who
          · subst i
            simp [commitJointAction, active, availableActions, hv]
          · simp [commitJointAction, active, hi]
      | reveal y who x hx k =>
          refine ⟨GameTheory.FOSG.noopAction (fun who : P => Action (P := P) L who), ?_⟩
          refine ⟨by simp [terminal], ?_⟩
          intro i
          simp [GameTheory.FOSG.noopAction, active]

/-- The initial checked program has a legal FOSG joint action whenever it is
not already terminal. -/
theorem initial_exists_jointActionLegal
    (g : WFProgram P L) (hterm : ¬ terminal (World.initial g)) :
    ∃ a : JointAction P L, JointActionLegal (World.initial g) a :=
  exists_jointActionLegal_of_legal (World.initial g) g.legal hterm

end FOSGBridge
end Vegas
