import GameTheory.Languages.FOSG.Information
import GameTheory.Languages.FOSG.Strategy
import GameTheory.Languages.FOSG.Compile
import GameTheory.Languages.FOSG.Kuhn
import Vegas.Strategic
import Vegas.PureStrategic
import Vegas.LegalNonempty
import Vegas.Finite
import Vegas.ViewKernel
import Vegas.WFProgram

/-!
# Vegas to FOSG bridge

This file compiles a checked Vegas program to an observation-preserving FOSG
whose commit guards are state-dependent action-availability constraints. The
executable target uses a finite program-local action alphabet and reachable
cursor worlds carrying the inherited proof obligations needed by Vegas'
suffix-based semantics.
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

/-- A Vegas runtime configuration, before restricting to reachable states. -/
structure World (P : Type) [DecidableEq P] (L : IExpr) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L Γ

namespace World

/-- The initial world associated with a checked Vegas program. -/
def initial (g : WFProgram P L) : World P L where
  Γ := g.Γ
  prog := g.prog
  env := g.env

end World

/-- Vegas terminal states are exactly `ret` configurations. -/
def terminal (w : World P L) : Prop :=
  match w.prog with
  | .ret _ => True
  | _ => False

/-- The only strategic FOSG states are Vegas `commit` nodes. -/
def active (w : World P L) : Finset P :=
  match w.prog with
  | .commit _ who _ _ => {who}
  | _ => ∅

/-- Number of operational syntax nodes remaining before a Vegas program reaches
`ret`, ignoring probabilistic branching because branching changes only
environments, not the continuation shape. -/
def syntaxSteps :
    {Γ : VCtx P L} → VegasCore P L Γ → Nat
  | _, .ret _ => 0
  | _, .letExpr _ _ k => syntaxSteps k + 1
  | _, .sample _ _ k => syntaxSteps k + 1
  | _, .commit _ _ _ k => syntaxSteps k + 1
  | _, .reveal _ _ _ _ k => syntaxSteps k + 1

@[simp] theorem syntaxSteps_ret
    {Γ : VCtx P L}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    syntaxSteps (.ret payoffs) = 0 := rfl

@[simp] theorem syntaxSteps_letExpr
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} :
    syntaxSteps (.letExpr x e k) = syntaxSteps k + 1 := rfl

@[simp] theorem syntaxSteps_sample
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} :
    syntaxSteps (.sample x D k) = syntaxSteps k + 1 := rfl

@[simp] theorem syntaxSteps_commit
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
    syntaxSteps (.commit x who R k) = syntaxSteps k + 1 := rfl

@[simp] theorem syntaxSteps_reveal
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)} :
    syntaxSteps (.reveal y who x hx k) = syntaxSteps k + 1 := rfl

/-- A program has no remaining syntax steps exactly at `ret`. -/
theorem terminal_iff_syntaxSteps_eq_zero {w : World P L} :
    terminal w ↔ syntaxSteps w.prog = 0 := by
  cases w with
  | mk Γ prog env =>
      cases prog <;> simp [terminal, syntaxSteps]

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

namespace ProgramBehavioralProfile

/-- Dropping the head commit site preserves behavioral guard-legality. -/
theorem tail_isLegal
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {σ : ProgramBehavioralProfile (.commit x who R k)}
    (hσ : σ.IsLegal) :
    (ProgramBehavioralProfile.tail σ).IsLegal := by
  intro j
  by_cases hj : who = j
  · subst hj
    have hσ_who : (σ who).IsLegal (.commit x who R k) := hσ who
    dsimp [ProgramBehavioralStrategy.IsLegal] at hσ_who
    dsimp [ProgramBehavioralProfile.tail]
    split at hσ_who
    · split
      · exact hσ_who.2
      · exact absurd rfl ‹_›
    · exact absurd rfl ‹_›
  · have hσ_j : (σ j).IsLegal (.commit x who R k) := hσ j
    dsimp [ProgramBehavioralStrategy.IsLegal] at hσ_j
    dsimp [ProgramBehavioralProfile.tail]
    split at hσ_j
    · rename_i h
      exact absurd h hj
    · split
      · rename_i h
        exact absurd h hj
      · exact hσ_j

end ProgramBehavioralProfile

/-! ## Program-local action cursors

The broad `Action L who` alphabet above is useful for the first structural
bridge, but finite FOSG execution should not quantify over every type in `L`.
The following cursor describes exactly the commit sites of one program owned by
one player; `ProgramAction` is the corresponding finite-by-construction target
alphabet once value types are finite.
-/

/-- A cursor to a commit site owned by `who` inside a fixed Vegas program. -/
inductive CommitCursor (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | here
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
      CommitCursor who (.commit x who R k)
  | letExpr
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.letExpr x e k)
  | sample
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.sample x D k)
  | commit
      {Γ : VCtx P L} {x : VarId} {owner : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.commit x owner R k)
  | reveal
      {Γ : VCtx P L} {y : VarId} {owner : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden owner b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.reveal y owner x hx k)

namespace CommitCursor

/-- The value type chosen at the pointed commit site. -/
def ty {who : P} :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      CommitCursor who p → L.Ty
  | _, .commit _ _ (b := b) _ _, .here => b
  | _, .letExpr _ _ _, .letExpr c => ty c
  | _, .sample _ _ _, .sample c => ty c
  | _, .commit _ _ _ _, .commit c => ty c
  | _, .reveal _ _ _ _ _, .reveal c => ty c

/-- Enumerate the commit sites owned by `who` in a fixed program. -/
def enumerate (who : P) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      List (CommitCursor who p)
  | _, .ret _ => []
  | _, .letExpr _ _ k => (enumerate who k).map .letExpr
  | _, .sample _ _ k => (enumerate who k).map .sample
  | Γ, .commit x owner (b := b) R k =>
      if h : owner = who then
        by
          have head :
              CommitCursor who
                (.commit x owner (b := b) R k) := by
            cases h
            exact .here
          exact head :: (enumerate who k).map .commit
      else
        (enumerate who k).map .commit
  | _, .reveal _ _ _ _ k => (enumerate who k).map .reveal

/-- `enumerate` is complete: every cursor appears in the generated list. -/
theorem mem_enumerate {who : P} :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (c : CommitCursor who p) →
        c ∈ enumerate who p
  | _, _, .here => by
      simp [enumerate]
  | _, _, .letExpr c => by
      simp [enumerate, mem_enumerate c]
  | _, _, .sample c => by
      simp [enumerate, mem_enumerate c]
  | _, _, .commit c => by
      simp only [enumerate]
      split
      · right
        exact List.mem_map.mpr ⟨c, mem_enumerate c, rfl⟩
      · exact List.mem_map.mpr ⟨c, mem_enumerate c, rfl⟩
  | _, _, .reveal c => by
      simp [enumerate, mem_enumerate c]

/-- The set of owned commit cursors is finite without assuming all language
types are finite. -/
@[reducible] noncomputable def instFintype
    (who : P) {Γ : VCtx P L} (p : VegasCore P L Γ) :
    Fintype (CommitCursor who p) := by
  classical
  exact Fintype.ofList (enumerate who p)
    (fun c => mem_enumerate c)

end CommitCursor

/-- Program-local action alphabet: choose one owned commit site and a value of
that site's type. This is the intended replacement alphabet for finite FOSG
execution, avoiding any global finiteness assumption on `L.Ty`. -/
structure ProgramAction {Γ : VCtx P L} (p : VegasCore P L Γ) (who : P) where
  cursor : CommitCursor who p
  value : L.Val (CommitCursor.ty cursor)

namespace ProgramAction

/-- Erase a program-local action to the broad structural action alphabet. -/
def toAction {Γ : VCtx P L} {p : VegasCore P L Γ} {who : P}
    (a : ProgramAction p who) : Action (P := P) L who :=
  Sigma.mk (CommitCursor.ty a.cursor) a.value

/-- Local decidable equality helper for program actions. Kept as an explicit
definition rather than a global instance because it is classical over the
dependent cursor proof shape. -/
@[reducible] noncomputable def instDecidableEq
    {Γ : VCtx P L} (p : VegasCore P L Γ) (who : P) :
    DecidableEq (ProgramAction p who) :=
  Classical.decEq _

/-- Program-local actions are finite when the value types that occur in the
language are finite. This avoids the stronger and usually wrong requirement
that the global sigma alphabet `Action L who` be finite. -/
@[reducible] noncomputable def instFintype
    (LF : FiniteValuation L) {Γ : VCtx P L}
    (p : VegasCore P L Γ) (who : P) :
    Fintype (ProgramAction p who) := by
  classical
  let _ : Fintype (CommitCursor who p) :=
    CommitCursor.instFintype who p
  have hVal : ∀ c : CommitCursor who p,
      Fintype (L.Val (CommitCursor.ty c)) :=
    fun c => LF.fintypeVal (CommitCursor.ty c)
  let e :
      ProgramAction p who ≃
        Sigma (fun c : CommitCursor who p =>
          L.Val (CommitCursor.ty c)) :=
    { toFun := fun a => ⟨a.cursor, a.value⟩
      invFun := fun a => { cursor := a.1, value := a.2 }
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro a
        cases a
        rfl }
  let _ : ∀ c : CommitCursor who p,
      Fintype (L.Val (CommitCursor.ty c)) := hVal
  exact Fintype.ofEquiv
    (Sigma (fun c : CommitCursor who p =>
      L.Val (CommitCursor.ty c))) e.symm

end ProgramAction

/-! ## Program cursors

The FOSG state must remember not only the current subprogram but also where
that subprogram sits inside the original Vegas program. This is what lets a
fixed Vegas strategy profile be projected to the current continuation without
putting strategy data into the game state.
-/

/-- `ProgramSuffix root p` means `p` is the current continuation reached by
stepping forward from `root`. It is a typed cursor into the original program. -/
inductive ProgramSuffix {Γ₀ : VCtx P L} (root : VegasCore P L Γ₀) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | here : ProgramSuffix root root
  | letExpr
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (s : ProgramSuffix root (.letExpr x e k)) :
      ProgramSuffix root k
  | sample
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (s : ProgramSuffix root (.sample x D k)) :
      ProgramSuffix root k
  | commit
      {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      (s : ProgramSuffix root (.commit x who R k)) :
      ProgramSuffix root k
  | reveal
      {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (s : ProgramSuffix root (.reveal y who x hx k)) :
      ProgramSuffix root k

namespace ProgramSuffix

def fresh
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    FreshBindings root → FreshBindings p := by
  induction s with
  | here => intro h; exact h
  | letExpr s ih => intro h; exact ih h |>.2
  | sample s ih => intro h; exact ih h |>.2
  | commit s ih => intro h; exact ih h |>.2
  | reveal s ih => intro h; exact ih h |>.2

def viewScoped
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    ViewScoped root → ViewScoped p := by
  induction s with
  | here => intro h; exact h
  | letExpr s ih => intro h; exact ih h
  | sample s ih => intro h; exact ih h
  | commit s ih => intro h; exact (ih h).2
  | reveal s ih => intro h; exact ih h

def normalized
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    NormalizedDists root → NormalizedDists p := by
  induction s with
  | here => intro h; exact h
  | letExpr s ih => intro h; exact ih h
  | sample s ih => intro h; exact (ih h).2
  | commit s ih => intro h; exact ih h
  | reveal s ih => intro h; exact ih h

def legal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    Legal root → Legal p := by
  induction s with
  | here => intro h; exact h
  | letExpr s ih => intro h; exact ih h
  | sample s ih => intro h; exact ih h
  | commit s ih => intro h; exact (ih h).2
  | reveal s ih => intro h; exact ih h

noncomputable def pureProfile
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    ProgramPureProfile root →
      ProgramPureProfile p := by
  induction s with
  | here => intro σ; exact σ
  | letExpr s ih => intro σ; exact ih σ
  | sample s ih => intro σ; exact ih σ
  | commit s ih =>
      intro σ
      exact ProgramPureProfile.tail (ih σ)
  | reveal s ih => intro σ; exact ih σ

@[simp] theorem pureProfile_letExpr
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (s : ProgramSuffix root (.letExpr x e k))
    (σ : ProgramPureProfile root) :
    (ProgramSuffix.letExpr s).pureProfile σ =
      s.pureProfile σ := rfl

@[simp] theorem pureProfile_sample
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (s : ProgramSuffix root (.sample x D k))
    (σ : ProgramPureProfile root) :
    (ProgramSuffix.sample s).pureProfile σ =
      s.pureProfile σ := rfl

@[simp] theorem pureProfile_commit
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (s : ProgramSuffix root (.commit x who R k))
    (σ : ProgramPureProfile root) :
    (ProgramSuffix.commit s).pureProfile σ =
      ProgramPureProfile.tail (P := P) (L := L)
        (s.pureProfile σ) := rfl

@[simp] theorem pureProfile_reveal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    (s : ProgramSuffix root (.reveal y who x hx k))
    (σ : ProgramPureProfile root) :
    (ProgramSuffix.reveal s).pureProfile σ =
      s.pureProfile σ := rfl

theorem pureProfile_isLegal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    {σ : ProgramPureProfile root}
    (hσ : σ.IsLegal) :
    (s.pureProfile σ).IsLegal := by
  induction s generalizing σ with
  | here => exact hσ
  | letExpr s ih => exact ih hσ
  | sample s ih => exact ih hσ
  | commit s ih =>
      exact ProgramPureProfile.tail_isLegal (ih hσ)
  | reveal s ih => exact ih hσ

noncomputable def behavioralProfile
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    ProgramBehavioralProfile root →
      ProgramBehavioralProfile p := by
  induction s with
  | here => intro σ; exact σ
  | letExpr s ih => intro σ; exact ih σ
  | sample s ih => intro σ; exact ih σ
  | commit s ih =>
      intro σ
      exact ProgramBehavioralProfile.tail (ih σ)
  | reveal s ih => intro σ; exact ih σ

@[simp] theorem behavioralProfile_letExpr
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (s : ProgramSuffix root (.letExpr x e k))
    (σ : ProgramBehavioralProfile root) :
    (ProgramSuffix.letExpr s).behavioralProfile σ =
      s.behavioralProfile σ := rfl

@[simp] theorem behavioralProfile_sample
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (s : ProgramSuffix root (.sample x D k))
    (σ : ProgramBehavioralProfile root) :
    (ProgramSuffix.sample s).behavioralProfile σ =
      s.behavioralProfile σ := rfl

@[simp] theorem behavioralProfile_commit
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (s : ProgramSuffix root (.commit x who R k))
    (σ : ProgramBehavioralProfile root) :
    (ProgramSuffix.commit s).behavioralProfile σ =
      ProgramBehavioralProfile.tail (P := P) (L := L)
        (s.behavioralProfile σ) := rfl

@[simp] theorem behavioralProfile_reveal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    (s : ProgramSuffix root (.reveal y who x hx k))
    (σ : ProgramBehavioralProfile root) :
    (ProgramSuffix.reveal s).behavioralProfile σ =
      s.behavioralProfile σ := rfl

theorem behavioralProfile_isLegal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    {σ : ProgramBehavioralProfile root}
    (hσ : σ.IsLegal) :
    (s.behavioralProfile σ).IsLegal := by
  induction s generalizing σ with
  | here => exact hσ
  | letExpr s ih => exact ih hσ
  | sample s ih => exact ih hσ
  | commit s ih =>
      exact ProgramBehavioralProfile.tail_isLegal (ih hσ)
  | reveal s ih => exact ih hσ

theorem behavioralProfile_toBehavioral
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    (σ : ProgramPureProfile root) :
    s.behavioralProfile
        (ProgramPureProfile.toBehavioral root σ) =
      ProgramPureProfile.toBehavioral p (s.pureProfile σ) := by
  induction s generalizing σ with
  | here => rfl
  | letExpr s ih => exact ih σ
  | sample s ih => exact ih σ
  | commit s ih =>
      rw [behavioralProfile_commit, pureProfile_commit, ih,
        ProgramPureProfile.tail_toBehavioral]
  | reveal s ih => exact ih σ

/-- Lift a program-local commit cursor at the current suffix back to a cursor
for the original root program. -/
noncomputable def liftCommitCursor
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) {who : P} :
    CommitCursor who p →
      CommitCursor who root := by
  induction s with
  | here =>
      intro c
      exact c
  | letExpr s ih =>
      intro c
      exact ih (.letExpr c)
  | sample s ih =>
      intro c
      exact ih (.sample c)
  | commit s ih =>
      intro c
      exact ih (.commit c)
  | reveal s ih =>
      intro c
      exact ih (.reveal c)

/-- Convert a suffix proof whose endpoint is an owned commit node into the
program-local commit cursor for that site. -/
noncomputable def commitCursor
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (s : ProgramSuffix root (.commit x who R k)) :
    CommitCursor who root :=
  s.liftCommitCursor .here

/-- Lifting a commit cursor through a suffix preserves the commit site's value
type. -/
theorem ty_liftCommitCursor
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) {who : P}
    (c : CommitCursor who p) :
    CommitCursor.ty (s.liftCommitCursor c) = CommitCursor.ty c := by
  induction s with
  | here =>
      rfl
  | letExpr s ih =>
      simpa [liftCommitCursor, CommitCursor.ty] using ih (.letExpr c)
  | sample s ih =>
      simpa [liftCommitCursor, CommitCursor.ty] using ih (.sample c)
  | commit s ih =>
      simpa [liftCommitCursor, CommitCursor.ty] using ih (.commit c)
  | reveal s ih =>
      simpa [liftCommitCursor, CommitCursor.ty] using ih (.reveal c)

/-- The cursor extracted from a suffix ending at a commit has the type of that
commit. -/
theorem ty_commitCursor
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (s : ProgramSuffix root (.commit x who R k)) :
    CommitCursor.ty (commitCursor s) = b := by
  simpa [commitCursor, CommitCursor.ty] using
    ty_liftCommitCursor (s := s)
      (c := (.here :
        CommitCursor who (.commit x who (b := b) R k)))

end ProgramSuffix

namespace ProgramAction

/-- Program-local action at a concrete commit suffix. The dependent cast is
centralized here so downstream semantic proofs can use the round-trip lemma
instead of depending on elaborator-generated proof terms. -/
noncomputable def commitAt
    {g : WFProgram P L} {Γ : VCtx P L}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (v : L.Val b) : ProgramAction g.prog who where
  cursor := ProgramSuffix.commitCursor suffix
  value := cast
    (congrArg L.Val
      (ProgramSuffix.ty_commitCursor suffix)).symm v

@[simp] theorem commitAt_cursor
    {g : WFProgram P L} {Γ : VCtx P L}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (v : L.Val b) :
    (commitAt suffix v).cursor =
      ProgramSuffix.commitCursor suffix := rfl

private theorem cast_val_roundtrip {cty b : L.Ty}
    (h h' : cty = b) (v : L.Val b) :
    h' ▸ (cast (congrArg L.Val h).symm v : L.Val cty) = v := by
  cases h
  simp [cast_eq]

@[simp] theorem commitAt_value_cast
    {g : WFProgram P L} {Γ : VCtx P L}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (v : L.Val b)
    (hty : CommitCursor.ty
      (commitAt suffix v).cursor = b) :
    hty ▸ (commitAt suffix v).value = v := by
  exact cast_val_roundtrip
    (ProgramSuffix.ty_commitCursor suffix) hty v

end ProgramAction

/-! ## Canonical program cursors

`ProgramSuffix` is useful for proof transport, but it is not the right finite
state key: it is a proof-shaped path. `ProgramCursor` is the canonical data
representation of a position in the linear Vegas syntax.
-/

/-- A canonical cursor to one syntactic continuation of a Vegas program. -/
inductive ProgramCursor :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | here {Γ : VCtx P L} {p : VegasCore P L Γ} :
      ProgramCursor p
  | letExpr
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (c : ProgramCursor k) :
      ProgramCursor (.letExpr x e k)
  | sample
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (c : ProgramCursor k) :
      ProgramCursor (.sample x D k)
  | commit
      {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      (c : ProgramCursor k) :
      ProgramCursor (.commit x who R k)
  | reveal
      {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (c : ProgramCursor k) :
      ProgramCursor (.reveal y who x hx k)

namespace ProgramCursor

/-- Context at the cursor target. -/
def Γ :
    {Γ₀ : VCtx P L} → {root : VegasCore P L Γ₀} →
      ProgramCursor root → VCtx P L
  | Γ₀, _, .here => Γ₀
  | _, _, .letExpr c => Γ c
  | _, _, .sample c => Γ c
  | _, _, .commit c => Γ c
  | _, _, .reveal c => Γ c

/-- Program continuation at the cursor target. -/
def prog :
    {Γ₀ : VCtx P L} → {root : VegasCore P L Γ₀} →
      (c : ProgramCursor root) → VegasCore P L (Γ c)
  | _, root, .here => root
  | _, _, .letExpr c => prog c
  | _, _, .sample c => prog c
  | _, _, .commit c => prog c
  | _, _, .reveal c => prog c

/-- Local proof obligations attached to a program cursor endpoint. -/
def EndpointValid
    {Γ₀ : VCtx P L} {root : VegasCore P L Γ₀}
    (c : ProgramCursor root) : Prop :=
  WFCtx c.Γ ∧ FreshBindings c.prog ∧ ViewScoped c.prog ∧
    NormalizedDists c.prog ∧ Legal c.prog

/-- Extend an existing suffix by a canonical cursor rooted at its endpoint. -/
def toSuffixFrom
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    (c : ProgramCursor p) →
      ProgramSuffix root (prog c)
  | .here => s
  | .letExpr c => toSuffixFrom (.letExpr s) c
  | .sample c => toSuffixFrom (.sample s) c
  | .commit c => toSuffixFrom (.commit s) c
  | .reveal c => toSuffixFrom (.reveal s) c

/-- Convert a canonical cursor to the existing proof-shaped suffix. -/
def toSuffix
    {Γ₀ : VCtx P L} {root : VegasCore P L Γ₀}
    (c : ProgramCursor root) :
    ProgramSuffix root (prog c) :=
  toSuffixFrom .here c

/-- Compose a cursor from `root` to `p` with a cursor from `p` to a deeper
continuation. -/
def extend :
    {Γ₀ : VCtx P L} → {root : VegasCore P L Γ₀} →
      (c : ProgramCursor root) →
      ProgramCursor (prog c) →
        ProgramCursor root
  | _, _, .here, d => d
  | _, _, .letExpr c, d => .letExpr (extend c d)
  | _, _, .sample c, d => .sample (extend c d)
  | _, _, .commit c, d => .commit (extend c d)
  | _, _, .reveal c, d => .reveal (extend c d)

@[simp] theorem extend_here_left
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (d : ProgramCursor root) :
    extend (.here : ProgramCursor root) d = d := rfl

/-- Canonical cursors are finite because Vegas syntax is linear. -/
@[reducible] noncomputable def instFintype :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      Fintype (ProgramCursor p)
  | _, .ret _ =>
      let e : ProgramCursor (.ret _) ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => .here
          left_inv := by
            intro c
            cases c
            rfl
          right_inv := by
            intro u
            cases u
            rfl }
      Fintype.ofEquiv Unit e.symm
  | Γ, .letExpr x (b := b) e k =>
      let _ : Fintype (ProgramCursor k) := instFintype k
      let e : ProgramCursor (.letExpr x (b := b) e k) ≃
          Unit ⊕ ProgramCursor k :=
        { toFun := fun c =>
            match c with
            | .here => Sum.inl ()
            | .letExpr c => Sum.inr c
          invFun := fun s =>
            match s with
            | Sum.inl _ => .here
            | Sum.inr c => .letExpr c
          left_inv := by
            intro c
            cases c <;> rfl
          right_inv := by
            intro s
            cases s <;> rfl }
      Fintype.ofEquiv (Unit ⊕ ProgramCursor k) e.symm
  | Γ, .sample x (b := b) D k =>
      let _ : Fintype (ProgramCursor k) := instFintype k
      let e : ProgramCursor (.sample x (b := b) D k) ≃
          Unit ⊕ ProgramCursor k :=
        { toFun := fun c =>
            match c with
            | .here => Sum.inl ()
            | .sample c => Sum.inr c
          invFun := fun s =>
            match s with
            | Sum.inl _ => .here
            | Sum.inr c => .sample c
          left_inv := by
            intro c
            cases c <;> rfl
          right_inv := by
            intro s
            cases s <;> rfl }
      Fintype.ofEquiv (Unit ⊕ ProgramCursor k) e.symm
  | Γ, .commit x who (b := b) R k =>
      let _ : Fintype (ProgramCursor k) := instFintype k
      let e : ProgramCursor (.commit x who (b := b) R k) ≃
          Unit ⊕ ProgramCursor k :=
        { toFun := fun c =>
            match c with
            | .here => Sum.inl ()
            | .commit c => Sum.inr c
          invFun := fun s =>
            match s with
            | Sum.inl _ => .here
            | Sum.inr c => .commit c
          left_inv := by
            intro c
            cases c <;> rfl
          right_inv := by
            intro s
            cases s <;> rfl }
      Fintype.ofEquiv (Unit ⊕ ProgramCursor k) e.symm
  | Γ, .reveal y who x (b := b) hx k =>
      let _ : Fintype (ProgramCursor k) := instFintype k
      let e : ProgramCursor (.reveal y who x (b := b) hx k) ≃
          Unit ⊕ ProgramCursor k :=
        { toFun := fun c =>
            match c with
            | .here => Sum.inl ()
            | .reveal c => Sum.inr c
          invFun := fun s =>
            match s with
            | Sum.inl _ => .here
            | Sum.inr c => .reveal c
          left_inv := by
            intro c
            cases c <;> rfl
          right_inv := by
            intro s
            cases s <;> rfl }
      Fintype.ofEquiv (Unit ⊕ ProgramCursor k) e.symm

end ProgramCursor

/-! ## Cursor-based world data -/

/-- Data-bearing world state keyed by a canonical finite program cursor. This
is the finite-state carrier that should replace the older suffix-based
`CheckedWorldData` once the FOSG target is migrated. -/
structure CursorWorldData (g : WFProgram P L) where
  cursor : ProgramCursor g.prog
  env : VEnv L cursor.Γ

namespace CursorWorldData

def prog {g : WFProgram P L} (d : CursorWorldData g) :
    VegasCore P L d.cursor.Γ :=
  d.cursor.prog

def suffix {g : WFProgram P L} (d : CursorWorldData g) :
    ProgramSuffix g.prog d.prog :=
  d.cursor.toSuffix

/-- Local proof obligations for a cursor-keyed checked world. -/
def Valid {g : WFProgram P L} (d : CursorWorldData g) : Prop :=
  WFCtx d.cursor.Γ ∧ FreshBindings d.prog ∧ ViewScoped d.prog ∧
    NormalizedDists d.prog ∧ Legal d.prog

/-- Cursor-keyed world data is finite under finite value types. -/
@[reducible] noncomputable def instFintype
    (g : WFProgram P L) (LF : FiniteValuation L) :
    Fintype (CursorWorldData g) := by
  let _ : Fintype (ProgramCursor g.prog) :=
    ProgramCursor.instFintype g.prog
  have hEnv : ∀ c : ProgramCursor g.prog,
      Fintype (VEnv L c.Γ) := fun c => VEnv.instFintype LF
  let e :
      CursorWorldData g ≃
        Sigma (fun c : ProgramCursor g.prog =>
          VEnv L c.Γ) :=
    { toFun := fun d => ⟨d.cursor, d.env⟩
      invFun := fun d => { cursor := d.1, env := d.2 }
      left_inv := by
        intro d
        cases d
        rfl
      right_inv := by
        intro d
        cases d
        rfl }
  let _ : ∀ c : ProgramCursor g.prog,
      Fintype (VEnv L c.Γ) := hEnv
  exact Fintype.ofEquiv
    (Sigma (fun c : ProgramCursor g.prog => VEnv L c.Γ))
    e.symm

end CursorWorldData

/-- Checked worlds over the finite cursor-keyed carrier. This is the intended
finite world type for the final executable FOSG target. -/
abbrev CursorCheckedWorld (g : WFProgram P L) : Type :=
  {d : CursorWorldData g // d.Valid}

namespace CursorCheckedWorld

/-- Forget the cursor-keyed checked obligations to the raw runtime world. -/
def toWorld {g : WFProgram P L}
    (w : CursorCheckedWorld g) : World P L where
  Γ := w.1.cursor.Γ
  prog := w.1.prog
  env := w.1.env

/-- Terminality for the finite cursor-keyed checked-world carrier. -/
def terminal {g : WFProgram P L}
    (w : CursorCheckedWorld g) : Prop :=
  Vegas.FOSGBridge.terminal w.toWorld

/-- Active players for the finite cursor-keyed checked-world carrier. -/
def active {g : WFProgram P L}
    (w : CursorCheckedWorld g) : Finset P :=
  Vegas.FOSGBridge.active w.toWorld

/-- Broad-alphabet action availability for the finite cursor-keyed carrier. -/
def availableActions {g : WFProgram P L}
    (w : CursorCheckedWorld g) (who : P) :
    Set (Action (P := P) L who) :=
  Vegas.FOSGBridge.availableActions w.toWorld who

/-- Remaining operational syntax nodes at a finite cursor-keyed checked world. -/
def remainingSyntaxSteps {g : WFProgram P L}
    (w : CursorCheckedWorld g) : Nat :=
  syntaxSteps w.1.prog

theorem terminal_iff_remainingSyntaxSteps_eq_zero
    {g : WFProgram P L} {w : CursorCheckedWorld g} :
    w.terminal ↔ w.remainingSyntaxSteps = 0 := by
  cases w with
  | mk data valid =>
      cases data
      simp [terminal, remainingSyntaxSteps, toWorld, terminal_iff_syntaxSteps_eq_zero]

/-- The finite cursor-keyed checked-world carrier is finite under finite value
types. `Fintype.ofFinite` avoids requiring decidability of the proof-bearing
`Valid` predicate. -/
@[reducible] noncomputable def instFintype
    (g : WFProgram P L) (LF : FiniteValuation L) :
    Fintype (CursorCheckedWorld g) := by
  let _ : Fintype (CursorWorldData g) :=
    CursorWorldData.instFintype g LF
  exact Fintype.ofFinite (CursorCheckedWorld g)

/-- Initial state for the finite cursor-keyed checked-world carrier. -/
def initial (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    CursorCheckedWorld g :=
  ⟨{ cursor := .here
     env := g.env },
    by
      exact ⟨hctx, g.wf.1, g.wf.2.2, g.normalized, g.legal⟩⟩

end CursorCheckedWorld

/-- Result carrier for cursor-recursive execution before reattaching the
`WFProgram` wrapper. -/
structure CursorRuntimeState {Γ₀ : VCtx P L} (root : VegasCore P L Γ₀) where
  cursor : ProgramCursor root
  env : VEnv L cursor.Γ
  valid : cursor.EndpointValid

namespace CursorRuntimeState

/-- Reattach a cursor runtime state to a fixed checked program. -/
def toChecked {g : WFProgram P L}
    (s : CursorRuntimeState g.prog) :
    CursorCheckedWorld g :=
  ⟨{ cursor := s.cursor, env := s.env },
    by
      simpa [CursorWorldData.Valid, CursorWorldData.prog,
        ProgramCursor.EndpointValid] using s.valid⟩

end CursorRuntimeState

/-! ## Program points

`CheckedWorld` carries proof fields needed by the FOSG structure. For
finiteness, the data-bearing part is smaller: a syntactic point in the fixed
program plus an environment for that point's context.
-/

/-- A typed syntactic continuation of a fixed root program. -/
structure ProgramPoint {Γ₀ : VCtx P L} (root : VegasCore P L Γ₀) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  suffix : ProgramSuffix root prog

/-- The data-bearing part of a checked world, before attaching local proof
obligations. -/
structure CheckedWorldData (g : WFProgram P L) where
  point : ProgramPoint g.prog
  env : VEnv L point.Γ

namespace CheckedWorldData

def prog {g : WFProgram P L} (d : CheckedWorldData g) :
    VegasCore P L d.point.Γ :=
  d.point.prog

def suffix {g : WFProgram P L} (d : CheckedWorldData g) :
    ProgramSuffix g.prog d.prog :=
  d.point.suffix

/-- Local proof obligations attached to a checked world. This predicate is
separated from `CheckedWorldData` so finiteness can be proved on the data
carrier first and then restricted to valid states. -/
def Valid {g : WFProgram P L} (d : CheckedWorldData g) : Prop :=
  WFCtx d.point.Γ ∧ FreshBindings d.prog ∧ ViewScoped d.prog ∧
    NormalizedDists d.prog ∧ Legal d.prog

end CheckedWorldData

/-! ## A checked-world FOSG skeleton

The next layer uses worlds that carry the local obligations needed by the FOSG
structure itself. This avoids totalizing the game over malformed, deadlocking
Vegas configurations. We carry `FreshBindings` and `ViewScoped` separately
rather than `WF`: after a `commit`, the continuation is reveal-complete only
relative to a nonempty pending stack, so the raw continuation need not satisfy
`WF` with an empty pending stack.
-/

/-- A Vegas runtime configuration carrying the local obligations needed by
FOSG's total transition, non-deadlock, and observation-soundness fields.

This is intentionally not named `WFWorld`: `WF` includes
`RevealComplete []`, which is not stable under stepping through a `commit`.
-/
structure CheckedWorld (g : WFProgram P L) (hctx : WFCtx g.Γ) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L Γ
  suffix : ProgramSuffix g.prog prog
  wctx : WFCtx Γ
  fresh : FreshBindings prog
  viewScoped : ViewScoped prog
  normalized : NormalizedDists prog
  legal : Legal prog

namespace CheckedWorld

/-- Embed the finite cursor-keyed carrier into the current suffix-based
`CheckedWorld` presentation. -/
def ofCursorChecked {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CursorCheckedWorld g) :
    CheckedWorld g hctx where
  Γ := w.1.cursor.Γ
  prog := w.1.prog
  env := w.1.env
  suffix := w.1.suffix
  wctx := w.2.1
  fresh := w.2.2.1
  viewScoped := w.2.2.2.1
  normalized := w.2.2.2.2.1
  legal := w.2.2.2.2.2

/-- Forget the proof obligations on a checked world. -/
def toData {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : CheckedWorldData g where
  point :=
    { Γ := w.Γ
      prog := w.prog
      suffix := w.suffix }
  env := w.env

/-- Reattach checked-world proof obligations to data. -/
def ofValid {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (d : CheckedWorldData g)
    (h : d.Valid) : CheckedWorld g hctx where
  Γ := d.point.Γ
  prog := d.prog
  env := d.env
  suffix := d.suffix
  wctx := h.1
  fresh := h.2.1
  viewScoped := h.2.2.1
  normalized := h.2.2.2.1
  legal := h.2.2.2.2

/-- Checked worlds are exactly valid checked-world data. -/
def equivValidData {g : WFProgram P L} {hctx : WFCtx g.Γ} :
    CheckedWorld g hctx ≃
      {d : CheckedWorldData g // d.Valid} where
  toFun := fun w =>
    ⟨w.toData, by
      exact ⟨w.wctx, w.fresh, w.viewScoped, w.normalized, w.legal⟩⟩
  invFun := fun d => ofValid d.1 d.2
  left_inv := by
    intro w
    cases w
    rfl
  right_inv := by
    intro d
    cases d with
    | mk data valid =>
        apply Subtype.ext
        cases data
        rfl

def toWorld {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : World P L where
  Γ := w.Γ
  prog := w.prog
  env := w.env

def initial (g : WFProgram P L) (hctx : WFCtx g.Γ) : CheckedWorld g hctx where
  Γ := g.Γ
  prog := g.prog
  env := g.env
  suffix := .here
  wctx := hctx
  fresh := g.wf.1
  viewScoped := g.wf.2.2
  normalized := g.normalized
  legal := g.legal

end CheckedWorld

namespace ProgramCursor

/-- Forget a finite cursor endpoint to the suffix-based checked-world
presentation. This is the projection used by adapter lemmas: cursors are the
finite implementation, while `CheckedWorld` is the semantic machine. -/
def toCheckedWorld {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (c : ProgramCursor g.prog)
    (env : VEnv L c.Γ) (valid : c.EndpointValid) :
    CheckedWorld g hctx where
  Γ := c.Γ
  prog := c.prog
  env := env
  suffix := c.toSuffix
  wctx := valid.1
  fresh := valid.2.1
  viewScoped := valid.2.2.1
  normalized := valid.2.2.2.1
  legal := valid.2.2.2.2

end ProgramCursor

namespace CursorRuntimeState

/-- Project a local cursor runtime state under a global cursor prefix into the
suffix-based checked-world presentation. This is the implementation adapter:
the finite cursor representation is forgotten before semantic reasoning. -/
def toCheckedWorldFrom
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (pref : ProgramCursor g.prog)
    (s : CursorRuntimeState pref.prog) :
    CheckedWorld g hctx where
  Γ := s.cursor.Γ
  prog := s.cursor.prog
  env := s.env
  suffix := ProgramCursor.toSuffixFrom
    pref.toSuffix s.cursor
  wctx := s.valid.1
  fresh := s.valid.2.1
  viewScoped := s.valid.2.2.1
  normalized := s.valid.2.2.2.1
  legal := s.valid.2.2.2.2

/-- Project a local cursor runtime state under an explicit global suffix into
the suffix-based checked-world presentation. This is the proof-friendly form of
`toCheckedWorldFrom`: recursive cursor proofs frame suffixes directly, avoiding
extra transport through prefix-cursor equality. -/
def toCheckedWorldFromSuffix
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog root)
    (s : CursorRuntimeState root) :
    CheckedWorld g hctx where
  Γ := s.cursor.Γ
  prog := s.cursor.prog
  env := s.env
  suffix := ProgramCursor.toSuffixFrom
    suffix s.cursor
  wctx := s.valid.1
  fresh := s.valid.2.1
  viewScoped := s.valid.2.2.1
  normalized := s.valid.2.2.2.1
  legal := s.valid.2.2.2.2

end CursorRuntimeState

namespace ProgramCursor

/-- Project a cursor endpoint under an explicit global suffix into the
suffix-based checked-world presentation. -/
def toCheckedWorldFromSuffix
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog root)
    (c : ProgramCursor root)
    (env : VEnv L c.Γ) (valid : c.EndpointValid) :
    CheckedWorld g hctx where
  Γ := c.Γ
  prog := c.prog
  env := env
  suffix := ProgramCursor.toSuffixFrom
    suffix c
  wctx := valid.1
  fresh := valid.2.1
  viewScoped := valid.2.2.1
  normalized := valid.2.2.2.1
  legal := valid.2.2.2.2

end ProgramCursor

def checkedTerminal {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : Prop :=
  terminal w.toWorld

/-- Remaining operational syntax nodes at a checked world. -/
def CheckedWorld.remainingSyntaxSteps {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : Nat :=
  syntaxSteps w.prog

theorem checkedTerminal_iff_remainingSyntaxSteps_eq_zero
    {g : WFProgram P L} {hctx : WFCtx g.Γ} {w : CheckedWorld g hctx} :
    checkedTerminal w ↔ w.remainingSyntaxSteps = 0 := by
  cases w
  simp [checkedTerminal, CheckedWorld.remainingSyntaxSteps, CheckedWorld.toWorld,
    terminal_iff_syntaxSteps_eq_zero]

def checkedActive {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : Finset P :=
  active w.toWorld

def checkedAvailableActions
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) (who : P) : Set (Action (P := P) L who) :=
  availableActions w.toWorld who

abbrev CheckedJointActionLegal
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) (a : JointAction P L) : Prop :=
  GameTheory.JointActionLegal
    (fun who : P => Action (P := P) L who)
    checkedActive
    checkedTerminal
    checkedAvailableActions
    w
    a

/-- Joint actions over the program-local action alphabet. -/
abbrev ProgramJointAction (g : WFProgram P L) : Type :=
  GameTheory.JointAction
    (fun who : P => ProgramAction g.prog who)

/-- Erase a program-local joint action to the broad structural alphabet. -/
def ProgramJointAction.toAction {g : WFProgram P L}
    (a : ProgramJointAction g) : JointAction P L :=
  fun who => (a who).map ProgramAction.toAction

namespace CursorCheckedWorld

/-- Program-local availability at a specific suffix endpoint. This is the
transport-free version of `availableProgramActions`; the cursor-world wrapper is
just its instantiation at the current cursor endpoint. -/
def availableProgramActionsAt {g : WFProgram P L} {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (suffix : ProgramSuffix g.prog p) (who : P) :
    Set (ProgramAction g.prog who) :=
  {a | ProgramAction.toAction a ∈
      Vegas.FOSGBridge.availableActions
        ({ Γ := Γ, prog := p, env := env } : World P L) who ∧
    ∃ (x : VarId) (owner : P) (b : L.Ty)
      (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
      (k : VegasCore P L ((x, .hidden owner b) :: Γ)),
      ∃ hprog : p = VegasCore.commit x owner R k,
      ∃ howner : owner = who,
        by
          cases howner
          exact a.cursor =
            ProgramSuffix.commitCursor (P := P) (L := L)
              (by
                rw [← hprog]
                exact suffix)}

/-- Optional program-local moves available at a suffix endpoint. This mirrors
FOSG's `availableMovesAtState` without packaging the endpoint as a cursor
world. -/
def availableProgramMovesAt {g : WFProgram P L} {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (suffix : ProgramSuffix g.prog p) (who : P) :
    Set (Option (ProgramAction g.prog who)) :=
  {oi | match oi with
    | some a =>
        who ∈ Vegas.FOSGBridge.active
          ({ Γ := Γ, prog := p, env := env } : World P L) ∧
        a ∈ availableProgramActionsAt p env suffix who
    | none =>
        who ∉ Vegas.FOSGBridge.active
          ({ Γ := Γ, prog := p, env := env } : World P L)}

/-- Program-local action availability for the finite cursor-keyed carrier. At
a commit node, only the active owner may choose the current commit cursor paired
with a guard-legal value. -/
def availableProgramActions {g : WFProgram P L}
    (w : CursorCheckedWorld g) (who : P) :
    Set (ProgramAction g.prog who) :=
  {a | ProgramAction.toAction a ∈ w.availableActions who ∧
    ∃ (x : VarId) (owner : P) (b : L.Ty)
      (R : L.Expr ((x, b) :: eraseVCtx w.1.cursor.Γ) L.bool)
      (k : VegasCore P L ((x, .hidden owner b) :: w.1.cursor.Γ)),
      ∃ hprog : w.1.prog = VegasCore.commit x owner R k,
      ∃ howner : owner = who,
        by
          cases howner
          exact a.cursor =
            ProgramSuffix.commitCursor (P := P) (L := L)
              (by
                rw [← hprog]
                exact w.1.suffix)}

end CursorCheckedWorld

theorem availableProgramMovesAt_eq_of_projectViewEnv_eq
    (g : WFProgram P L) (who : P)
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (suffix : ProgramSuffix g.prog p)
    (env₁ env₂ : VEnv L Γ)
    (hctx : WFCtx (L := L) Γ)
    (hfresh : FreshBindings p)
    (hsc : ViewScoped p)
    (hview : projectViewEnv who (VEnv.eraseEnv env₁) =
      projectViewEnv who (VEnv.eraseEnv env₂)) :
    CursorCheckedWorld.availableProgramMovesAt
        p env₁ suffix who =
      CursorCheckedWorld.availableProgramMovesAt
        p env₂ suffix who := by
  ext oi
  cases oi with
  | none =>
      cases p <;> simp [CursorCheckedWorld.availableProgramMovesAt, active]
  | some a =>
      cases p with
      | ret payoffs =>
          simp [CursorCheckedWorld.availableProgramMovesAt,
            CursorCheckedWorld.availableProgramActionsAt, active]
      | letExpr x e k =>
          simp [CursorCheckedWorld.availableProgramMovesAt,
            CursorCheckedWorld.availableProgramActionsAt, active]
      | sample x D k =>
          simp [CursorCheckedWorld.availableProgramMovesAt,
            CursorCheckedWorld.availableProgramActionsAt, active]
      | reveal y owner x hx k =>
          simp [CursorCheckedWorld.availableProgramMovesAt,
            CursorCheckedWorld.availableProgramActionsAt, active]
      | commit x owner R k =>
          by_cases howner : owner = who
          · cases howner
            have hguard : ∀ v : L.Val _,
                evalGuard (Player := P) (L := L) R v (VEnv.eraseEnv env₁) =
                  evalGuard (Player := P) (L := L) R v (VEnv.eraseEnv env₂) := by
              intro v
              exact evalGuard_eq_of_projectViewEnv_eq hctx hfresh.1
                (ViewScoped.commit_guard_usesOnly hsc) hview
            simp [CursorCheckedWorld.availableProgramMovesAt,
              CursorCheckedWorld.availableProgramActionsAt,
              active, availableActions, ProgramAction.toAction, hguard]
          · simp [CursorCheckedWorld.availableProgramMovesAt,
              CursorCheckedWorld.availableProgramActionsAt,
              active, availableActions, ProgramAction.toAction, howner]

/-- FOSG joint-action legality for the cursor-keyed program-local alphabet. -/
abbrev CursorProgramJointActionLegal
    {g : WFProgram P L}
    (w : CursorCheckedWorld g)
    (a : ProgramJointAction g) : Prop :=
  GameTheory.JointActionLegal
    (fun who : P => ProgramAction g.prog who)
    CursorCheckedWorld.active
    CursorCheckedWorld.terminal
    CursorCheckedWorld.availableProgramActions
    w
    a

/-- Cursor-world program-local legality implies legality after erasing to the
broad structural action alphabet. -/
theorem CursorProgramJointActionLegal.toAction
    {g : WFProgram P L}
    {w : CursorCheckedWorld g}
    {a : ProgramJointAction g}
    (ha : CursorProgramJointActionLegal w a) :
    JointActionLegal w.toWorld (ProgramJointAction.toAction a) := by
  refine ⟨ha.1, ?_⟩
  intro i
  have hlocal := ha.2 i
  cases hai : a i with
  | none =>
      simpa [ProgramJointAction.toAction, hai, CursorProgramJointActionLegal,
        CursorCheckedWorld.active, CursorCheckedWorld.terminal] using hlocal
  | some ai =>
      have hpair : i ∈ w.active ∧ ai ∈ w.availableProgramActions i := by
        simpa [ProgramJointAction.toAction, hai, CursorProgramJointActionLegal] using hlocal
      have hbroad : i ∈ active w.toWorld ∧
          ProgramAction.toAction ai ∈ availableActions w.toWorld i := by
        refine ⟨?_, hpair.2.1⟩
        simpa [CursorCheckedWorld.active] using hpair.1
      simpa [ProgramJointAction.toAction, hai] using hbroad

/-- A program-local joint action where exactly `who` commits to `v` at the
current suffix endpoint. -/
noncomputable def commitProgramJointAction
    {g : WFProgram P L} {Γ : VCtx P L}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (v : L.Val b) : ProgramJointAction g :=
  fun i =>
    if h : i = who then
      by
        cases h
        exact some
          ({ cursor := ProgramSuffix.commitCursor suffix
             value := by
               rw [ProgramSuffix.ty_commitCursor suffix]
               exact v } :
            ProgramAction g.prog who)
    else
      none

private theorem commit_value_of_legal
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : JointAction P L}
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) a) :
    ∃ v : L.Val b,
      a who = some (Sigma.mk b v) ∧
        evalGuard (Player := P) (L := L) R v (VEnv.eraseEnv env) = true := by
  have hlocal := ha.2 who
  cases hact : a who with
  | none =>
      have hnot : who ∉ ({who} : Finset P) := by
        simp [active, hact] at hlocal
      exact False.elim (hnot (by simp))
  | some ai =>
      have havail : ai ∈
          availableActions
            ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
            who := by
        have hpair : who ∈ ({who} : Finset P) ∧
            ai ∈ availableActions
              ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
              who := by
          simpa [JointActionLegal, GameTheory.JointActionLegal, active, hact] using hlocal
        exact hpair.2
      rcases (by
        simpa [availableActions] using havail) with ⟨v, hai, hv⟩
      exact ⟨v, by simp [hai], hv⟩

/-- The committed value carried by a legal joint action at a Vegas commit node. -/
noncomputable def commitValueOfLegal
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : JointAction P L}
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) a) :
    L.Val b :=
  Classical.choose (commit_value_of_legal (L := L) ha)

theorem commitValueOfLegal_proof_irrel
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : JointAction P L}
    (ha₁ ha₂ : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) a) :
    commitValueOfLegal ha₁ =
      commitValueOfLegal ha₂ := by
  have hproof : ha₁ = ha₂ := Subsingleton.elim ha₁ ha₂
  cases hproof
  rfl

theorem commitValueOfLegal_action
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : JointAction P L}
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) a) :
    a who = some (Sigma.mk b (commitValueOfLegal (L := L) ha)) :=
  (Classical.choose_spec (commit_value_of_legal (L := L) ha)).1

theorem commitValueOfLegal_guard
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : JointAction P L}
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) a) :
    evalGuard (Player := P) (L := L) R
      (commitValueOfLegal (L := L) ha) (VEnv.eraseEnv env) = true :=
  (Classical.choose_spec (commit_value_of_legal (L := L) ha)).2

/-- If a legal broad joint action names the active commit action explicitly,
the value extracted by `commitValueOfLegal` is that action's value. -/
theorem commitValueOfLegal_eq_action_value
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : JointAction P L}
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) a)
    {ai : Action (P := P) L who}
    (hai : a who = some ai)
    (hty : ai.1 = b) :
    hty ▸ ai.2 = commitValueOfLegal ha := by
  have hact := commitValueOfLegal_action ha
  rw [hai] at hact
  cases ai with
  | mk cty val =>
      simp only [Option.some.injEq, Sigma.mk.injEq] at hact
      rcases hact with ⟨_hcty, hval⟩
      cases hty
      exact eq_of_heq hval

/-- Program-local variant of `commitValueOfLegal_eq_action_value`. -/
theorem commitValueOfLegal_eq_programAction_value
    {g : WFProgram P L} {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {env : VEnv L Γ} {a : ProgramJointAction g}
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
      (ProgramJointAction.toAction a))
    {ai : ProgramAction g.prog who}
    (hai : a who = some ai)
    (hty : CommitCursor.ty ai.cursor = b) :
    hty ▸ ai.value = commitValueOfLegal ha := by
  apply commitValueOfLegal_eq_action_value
    (ai := ProgramAction.toAction ai) ha
  · simp [ProgramJointAction.toAction, ProgramAction.toAction, hai]

theorem checked_terminal_active_eq_empty
    {g : WFProgram P L} {hctx : WFCtx g.Γ} {w : CheckedWorld g hctx} :
    checkedTerminal w → checkedActive w = ∅ :=
  terminal_active_eq_empty

theorem checked_terminal_no_legal
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    {w : CheckedWorld g hctx} {a : JointAction P L} :
    checkedTerminal w → ¬ CheckedJointActionLegal w a := by
  intro hterm hlegal
  exact hlegal.1 hterm

theorem checked_nonterminal_exists_legal
    {g : WFProgram P L} {hctx : WFCtx g.Γ} {w : CheckedWorld g hctx} :
    ¬ checkedTerminal w →
      ∃ a : JointAction P L, CheckedJointActionLegal w a := by
  intro hterm
  exact exists_jointActionLegal_of_legal w.toWorld w.legal hterm

/-- Terminal cursor worlds have no active players. -/
theorem cursor_terminal_active_eq_empty
    {g : WFProgram P L}
    {w : CursorCheckedWorld g} :
    w.terminal → w.active = ∅ :=
  terminal_active_eq_empty

/-- Terminal cursor worlds admit no legal program-local joint action. -/
theorem cursor_terminal_no_program_legal
    {g : WFProgram P L}
    {w : CursorCheckedWorld g}
    {a : ProgramJointAction g} :
    w.terminal → ¬ CursorProgramJointActionLegal w a := by
  intro hterm hlegal
  exact hlegal.1 hterm

theorem cursor_active_eq_empty_of_letExpr
    {g : WFProgram P L}
    {w : CursorCheckedWorld g}
    {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx w.1.cursor.Γ) b}
    {k : VegasCore P L ((x, .pub b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.letExpr x e k) :
    w.active = ∅ := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          have hprog' : cursor.prog = VegasCore.letExpr x e k := by
            simpa [CursorWorldData.prog] using hprog
          simp [CursorCheckedWorld.active, CursorCheckedWorld.toWorld,
            CursorWorldData.prog, active, hprog']

theorem cursor_not_terminal_of_letExpr
    {g : WFProgram P L}
    {w : CursorCheckedWorld g}
    {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx w.1.cursor.Γ) b}
    {k : VegasCore P L ((x, .pub b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.letExpr x e k) :
    ¬ w.terminal := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          have hprog' : cursor.prog = VegasCore.letExpr x e k := by
            simpa [CursorWorldData.prog] using hprog
          simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
            CursorWorldData.prog, terminal, hprog']

theorem cursor_active_eq_empty_of_sample
    {g : WFProgram P L}
    {w : CursorCheckedWorld g}
    {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx w.1.cursor.Γ) b}
    {k : VegasCore P L ((x, .pub b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.sample x D k) :
    w.active = ∅ := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          have hprog' : cursor.prog = VegasCore.sample x D k := by
            simpa [CursorWorldData.prog] using hprog
          simp [CursorCheckedWorld.active, CursorCheckedWorld.toWorld,
            CursorWorldData.prog, active, hprog']

theorem cursor_not_terminal_of_sample
    {g : WFProgram P L}
    {w : CursorCheckedWorld g}
    {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx w.1.cursor.Γ) b}
    {k : VegasCore P L ((x, .pub b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.sample x D k) :
    ¬ w.terminal := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          have hprog' : cursor.prog = VegasCore.sample x D k := by
            simpa [CursorWorldData.prog] using hprog
          simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
            CursorWorldData.prog, terminal, hprog']

theorem cursor_active_eq_singleton_of_commit
    {g : WFProgram P L}
    {w : CursorCheckedWorld g}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx w.1.cursor.Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.commit x who R k) :
    w.active = {who} := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          have hprog' : cursor.prog = VegasCore.commit x who R k := by
            simpa [CursorWorldData.prog] using hprog
          simp [CursorCheckedWorld.active, CursorCheckedWorld.toWorld,
            CursorWorldData.prog, active, hprog']

theorem cursor_not_terminal_of_commit
    {g : WFProgram P L}
    {w : CursorCheckedWorld g}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx w.1.cursor.Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.commit x who R k) :
    ¬ w.terminal := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          have hprog' : cursor.prog = VegasCore.commit x who R k := by
            simpa [CursorWorldData.prog] using hprog
          simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
            CursorWorldData.prog, terminal, hprog']

theorem cursor_active_eq_empty_of_reveal
    {g : WFProgram P L}
    {w : CursorCheckedWorld g}
    {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar w.1.cursor.Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.reveal y who x hx k) :
    w.active = ∅ := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          have hprog' : cursor.prog = VegasCore.reveal y who x hx k := by
            simpa [CursorWorldData.prog] using hprog
          simp [CursorCheckedWorld.active, CursorCheckedWorld.toWorld,
            CursorWorldData.prog, active, hprog']

theorem cursor_not_terminal_of_reveal
    {g : WFProgram P L}
    {w : CursorCheckedWorld g}
    {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar w.1.cursor.Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.reveal y who x hx k) :
    ¬ w.terminal := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          have hprog' : cursor.prog = VegasCore.reveal y who x hx k := by
            simpa [CursorWorldData.prog] using hprog
          simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
            CursorWorldData.prog, terminal, hprog']

set_option linter.flexible false in
/-- Program-level `Legal` prevents deadlock for the cursor-keyed program-local
action alphabet. -/
theorem cursor_nonterminal_exists_program_legal
    {g : WFProgram P L}
    {w : CursorCheckedWorld g} :
    ¬ w.terminal →
      ∃ a : ProgramJointAction g,
        CursorProgramJointActionLegal w a := by
  intro hterm
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          rcases valid with ⟨wctx, fresh, viewScoped, normalized, legal⟩
          cases hprog : cursor.prog with
          | ret payoffs =>
              simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog] at hterm
          | letExpr x e k =>
              refine ⟨GameTheory.FOSG.noopAction
                (fun who : P => ProgramAction g.prog who), ?_⟩
              refine ⟨by simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog], ?_⟩
              intro i
              simp [GameTheory.FOSG.noopAction, CursorCheckedWorld.active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active, hprog]
          | sample x D k =>
              refine ⟨GameTheory.FOSG.noopAction
                (fun who : P => ProgramAction g.prog who), ?_⟩
              refine ⟨by simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog], ?_⟩
              intro i
              simp [GameTheory.FOSG.noopAction, CursorCheckedWorld.active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active, hprog]
          | commit x who R k =>
              change Legal cursor.prog at legal
              rw [hprog] at legal
              rcases legal.1 (VEnv.eraseEnv env) with ⟨v, hv⟩
              let suffix : ProgramSuffix g.prog
                  (VegasCore.commit x who R k) := by
                rw [← hprog]
                exact cursor.toSuffix
              refine ⟨commitProgramJointAction suffix v, ?_⟩
              refine ⟨by simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog], ?_⟩
              intro i
              by_cases hi : i = who
              · subst i
                simp [commitProgramJointAction, CursorCheckedWorld.active,
                  CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                  CursorCheckedWorld.availableProgramActions,
                  CursorCheckedWorld.availableActions, availableActions,
                  ProgramAction.toAction, ProgramSuffix.ty_commitCursor, hprog, hv]
                refine ⟨x, who, _, R, k, ?_, rfl, ?_⟩
                · exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩
                · rfl
              · have hnone : commitProgramJointAction suffix v i = none := by
                    simp [commitProgramJointAction, hi]
                rw [hnone]
                simp [CursorCheckedWorld.active, CursorCheckedWorld.toWorld,
                  CursorWorldData.prog, active, hprog, hi]
          | reveal y who x hx k =>
              refine ⟨GameTheory.FOSG.noopAction
                (fun who : P => ProgramAction g.prog who), ?_⟩
              refine ⟨by simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog], ?_⟩
              intro i
              simp [GameTheory.FOSG.noopAction, CursorCheckedWorld.active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active, hprog]

/-- The one-step transition kernel of the checked-world FOSG skeleton. -/
noncomputable def checkedTransition
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx)
    (a : {a : JointAction P L // CheckedJointActionLegal w a}) :
    PMF (CheckedWorld g hctx) := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          exact False.elim (a.2.1 (by simp [checkedTerminal, CheckedWorld.toWorld, terminal]))
      | letExpr x e k =>
          exact PMF.pure
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                (L.eval e (VEnv.erasePubEnv env)) env
              suffix := .letExpr suffix
              wctx := WFCtx.cons fresh.1 wctx
              fresh := fresh.2
              viewScoped := viewScoped
              normalized := normalized
              legal := legal }
      | sample x D k =>
          exact PMF.map
            (fun v =>
              { Γ := _
                prog := k
                env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                  v env
                suffix := .sample suffix
                wctx := WFCtx.cons fresh.1 wctx
                fresh := fresh.2
                viewScoped := viewScoped
                normalized := normalized.2
                legal := legal })
            ((L.evalDist D (VEnv.eraseSampleEnv env)).toPMF (normalized.1 env))
      | commit x who R k =>
          have ha : JointActionLegal
              ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
              a.1 := by
            simpa [CheckedJointActionLegal, checkedActive, checkedTerminal,
              checkedAvailableActions, CheckedWorld.toWorld] using a.2
          let v := commitValueOfLegal (L := L) ha
          exact PMF.pure
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _)
                v env
              suffix := .commit suffix
              wctx := WFCtx.cons fresh.1 wctx
              fresh := fresh.2
              viewScoped := viewScoped.2
              normalized := normalized
              legal := legal.2 }
      | reveal y who x hx k =>
          exact PMF.pure
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub _)
                (env x (.hidden who _) hx) env
              suffix := .reveal suffix
              wctx := WFCtx.cons fresh.1 wctx
              fresh := fresh.2
              viewScoped := viewScoped
              normalized := normalized
              legal := legal }

/-- At a concrete commit checked world, `checkedTransition` depends on the
program-local joint action only through the active player's selected program
action. This is the commit-side counterpart of the active-empty transition
lemma. -/
theorem checkedTransition_commit_eq_programActionContinuation
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (env : VEnv L Γ)
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (wctx : WFCtx Γ) (fresh : FreshBindings (.commit x who R k))
    (viewScoped : ViewScoped (.commit x who R k))
    (normalized : NormalizedDists (.commit x who R k))
    (legal : Legal (.commit x who R k))
    (a : ProgramJointAction g)
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
      (ProgramJointAction.toAction a)) :
    checkedTransition (P := P) (L := L)
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env, suffix := suffix,
         wctx := wctx, fresh := fresh, viewScoped := viewScoped,
         normalized := normalized, legal := legal } : CheckedWorld g hctx)
      ⟨ProgramJointAction.toAction a, by
        simpa [CheckedJointActionLegal, checkedActive, checkedTerminal,
          checkedAvailableActions, CheckedWorld.toWorld] using ha⟩ =
    match a who with
    | some ai =>
        if hty : CommitCursor.ty ai.cursor = b then
          PMF.pure
            ({ Γ := _
               prog := k
               env := VEnv.cons (Player := P) (L := L) (x := x)
                 (τ := .hidden who _) (hty ▸ ai.value) env
               suffix := .commit suffix
               wctx := WFCtx.cons fresh.1 wctx
               fresh := fresh.2
               viewScoped := viewScoped.2
               normalized := normalized
               legal := legal.2 } : CheckedWorld g hctx)
        else
          PMF.pure
            ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env, suffix := suffix,
               wctx := wctx, fresh := fresh, viewScoped := viewScoped,
               normalized := normalized, legal := legal } : CheckedWorld g hctx)
    | none =>
        PMF.pure
          ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env, suffix := suffix,
             wctx := wctx, fresh := fresh, viewScoped := viewScoped,
             normalized := normalized, legal := legal } : CheckedWorld g hctx) := by
  cases hai : a who with
  | none =>
      have hlocal := ha.2 who
      have hnone : ProgramJointAction.toAction a who = none := by
        simp [ProgramJointAction.toAction, hai]
      rw [hnone] at hlocal
      have hmem :
          who ∈ active
            ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } :
              World P L) := by
        simp [active]
      exact False.elim (hlocal hmem)
  | some ai =>
      dsimp only
      by_cases hty : CommitCursor.ty ai.cursor = b
      · rw [dif_pos hty]
        simp only [checkedTransition]
        rw [commitValueOfLegal_proof_irrel (ha₂ := ha)]
        have hv := commitValueOfLegal_eq_programAction_value
          (g := g) (Γ := Γ) (x := x) (who := who)
          (b := b) (R := R) (k := k) (env := env) (a := a) ha hai hty
        have henv :
            VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _)
                (commitValueOfLegal ha) env =
              VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _)
                (hty ▸ ai.value) env :=
          VEnv.cons_ext hv.symm rfl
        apply congrArg PMF.pure
        congr
        exact hv.symm
      · rw [dif_neg hty]
        simp only [checkedTransition]
        exact False.elim (hty (by
          -- The selected program action at `who` is the commit cursor.
          have hlocal := ha.2 who
          have hsome :
              ProgramJointAction.toAction a who =
                some (ProgramAction.toAction ai) := by
            simp [ProgramJointAction.toAction, hai]
          rw [hsome] at hlocal
          have havail := hlocal.2
          rcases (by
              simpa [availableActions, ProgramAction.toAction] using havail) with
            ⟨_v, htyv, _hguard⟩
          exact htyv.1))

/-- `checkedTransition` respects equality of checked worlds; the legal-action
proof component is proof-irrelevant. -/
theorem checkedTransition_congr_checkedWorld
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    {w₁ w₂ : CheckedWorld g hctx}
    (hw : w₁ = w₂)
    (a : JointAction P L)
    (ha₁ : CheckedJointActionLegal w₁ a)
    (ha₂ : CheckedJointActionLegal w₂ a) :
    checkedTransition w₁ ⟨a, ha₁⟩ =
      checkedTransition w₂ ⟨a, ha₂⟩ := by
  cases hw
  have hsub :
      (⟨a, ha₁⟩ : {a : JointAction P L // CheckedJointActionLegal w₁ a}) =
        ⟨a, ha₂⟩ := Subtype.ext rfl
  cases hsub
  rfl

/-- Cursor-recursive transition over the erased broad action alphabet.

The recursion follows the cursor frames until the endpoint is definitionally at
the current syntax node. This is the transport-avoiding core used by the
cursor-keyed FOSG target. -/
noncomputable def cursorTransitionState
    {Γ₀ : VCtx P L} :
    {root : VegasCore P L Γ₀} →
    (c : ProgramCursor root) →
    (env : VEnv L c.Γ) →
    (valid : c.EndpointValid) →
    (a : JointAction P L) →
    (ha : JointActionLegal
      ({ Γ := c.Γ, prog := c.prog, env := env } : World P L) a) →
    PMF (CursorRuntimeState root)
  | .ret payoffs, .here, env, valid, a, ha =>
      False.elim (ha.1 (by simp [ProgramCursor.prog, terminal]))
  | .letExpr x e k, .here, env, valid, _a, _ha =>
      let wctx := valid.1
      let fresh := valid.2.1
      let viewScoped := valid.2.2.1
      let normalized := valid.2.2.2.1
      let legal := valid.2.2.2.2
      PMF.pure
        { cursor := ProgramCursor.letExpr ProgramCursor.here
          env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
            (L.eval e (VEnv.erasePubEnv env)) env
          valid := ⟨WFCtx.cons fresh.1 wctx, fresh.2, viewScoped, normalized, legal⟩ }
  | .sample x D k, .here, env, valid, _a, _ha =>
      let wctx := valid.1
      let fresh := valid.2.1
      let viewScoped := valid.2.2.1
      let normalized := valid.2.2.2.1
      let legal := valid.2.2.2.2
      PMF.map
        (fun v =>
          { cursor := ProgramCursor.sample ProgramCursor.here
            env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
              v env
            valid := ⟨WFCtx.cons fresh.1 wctx, fresh.2, viewScoped,
              normalized.2, legal⟩ })
        ((L.evalDist D (VEnv.eraseSampleEnv env)).toPMF (normalized.1 env))
  | .commit x who R k, .here, env, valid, a, ha =>
      let wctx := valid.1
      let fresh := valid.2.1
      let viewScoped := valid.2.2.1
      let normalized := valid.2.2.2.1
      let legal := valid.2.2.2.2
      let v := commitValueOfLegal (L := L) ha
      PMF.pure
        { cursor := ProgramCursor.commit ProgramCursor.here
          env := VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who _) v env
          valid := ⟨WFCtx.cons fresh.1 wctx, fresh.2, viewScoped.2,
            normalized, legal.2⟩ }
  | .reveal y who x hx k, .here, env, valid, _a, _ha =>
      let wctx := valid.1
      let fresh := valid.2.1
      let viewScoped := valid.2.2.1
      let normalized := valid.2.2.2.1
      let legal := valid.2.2.2.2
      PMF.pure
        { cursor := ProgramCursor.reveal ProgramCursor.here
          env := VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub _)
            (env x (.hidden who _) hx) env
          valid := ⟨WFCtx.cons fresh.1 wctx, fresh.2, viewScoped,
            normalized, legal⟩ }
  | .letExpr x e k, .letExpr c, env, valid, a, ha =>
      PMF.map
        (fun (s : CursorRuntimeState k) =>
          { cursor := ProgramCursor.letExpr s.cursor
            env := s.env
            valid := by simpa [ProgramCursor.EndpointValid] using s.valid })
        (cursorTransitionState c env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))
  | .sample x D k, .sample c, env, valid, a, ha =>
      PMF.map
        (fun (s : CursorRuntimeState k) =>
          { cursor := ProgramCursor.sample s.cursor
            env := s.env
            valid := by simpa [ProgramCursor.EndpointValid] using s.valid })
        (cursorTransitionState c env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))
  | .commit x who R k, .commit c, env, valid, a, ha =>
      PMF.map
        (fun (s : CursorRuntimeState k) =>
          { cursor := ProgramCursor.commit s.cursor
            env := s.env
            valid := by simpa [ProgramCursor.EndpointValid] using s.valid })
        (cursorTransitionState c env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))
  | .reveal y who x hx k, .reveal c, env, valid, a, ha =>
      PMF.map
        (fun (s : CursorRuntimeState k) =>
          { cursor := ProgramCursor.reveal s.cursor
            env := s.env
            valid := by simpa [ProgramCursor.EndpointValid] using s.valid })
        (cursorTransitionState c env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))

/-- Cursor-keyed transition over program-local actions. -/
noncomputable def cursorProgramTransition
    {g : WFProgram P L}
    (w : CursorCheckedWorld g)
    (a : {a : ProgramJointAction g //
      CursorProgramJointActionLegal w a}) :
    PMF (CursorCheckedWorld g) :=
  PMF.map CursorRuntimeState.toChecked
    (cursorTransitionState w.1.cursor w.1.env
      (by
        simpa [CursorWorldData.Valid, CursorWorldData.prog,
          ProgramCursor.EndpointValid] using w.2)
      (ProgramJointAction.toAction a.1)
      (CursorProgramJointActionLegal.toAction a.2))


theorem cursorTransitionState_map_toCheckedWorldFromSuffix
    {g : WFProgram P L} {hctx : WFCtx g.Γ} :
    {Γ : VCtx P L} → {root : VegasCore P L Γ} →
    (suffix : ProgramSuffix g.prog root) →
    (c : ProgramCursor root) →
    (env : VEnv L c.Γ) →
    (valid : c.EndpointValid) →
    (a : JointAction P L) →
    (ha : JointActionLegal
      ({ Γ := c.Γ, prog := c.prog, env := env } : World P L) a) →
    PMF.map (CursorRuntimeState.toCheckedWorldFromSuffix
        (hctx := hctx) suffix)
      (cursorTransitionState c env valid a ha) =
    checkedTransition (P := P) (L := L)
      (ProgramCursor.toCheckedWorldFromSuffix
        (hctx := hctx) suffix c env valid)
      ⟨a, by
        simpa [CheckedJointActionLegal, ProgramCursor.toCheckedWorldFromSuffix,
          checkedActive, checkedTerminal, checkedAvailableActions,
          CheckedWorld.toWorld] using ha⟩ := by
  intro Γ root suffix c
  revert suffix
  exact ProgramCursor.rec
    (motive := fun {Γ} root c =>
      (suffix : ProgramSuffix g.prog root) →
      (env : VEnv L c.Γ) →
      (valid : c.EndpointValid) →
      (a : JointAction P L) →
      (ha : JointActionLegal
        ({ Γ := c.Γ, prog := c.prog, env := env } : World P L) a) →
      PMF.map (CursorRuntimeState.toCheckedWorldFromSuffix
          (hctx := hctx) suffix)
        (cursorTransitionState c env valid a ha) =
      checkedTransition (P := P) (L := L)
        (ProgramCursor.toCheckedWorldFromSuffix
          (hctx := hctx) suffix c env valid)
        ⟨a, by
          simpa [CheckedJointActionLegal, ProgramCursor.toCheckedWorldFromSuffix,
            checkedActive, checkedTerminal, checkedAvailableActions,
            CheckedWorld.toWorld] using ha⟩)
    (fun {Γ} {p} suffix env valid a ha => by
      cases p
      · exact False.elim (ha.1 (by simp [ProgramCursor.prog, terminal]))
      · simp [cursorTransitionState, checkedTransition,
          CursorRuntimeState.toCheckedWorldFromSuffix,
          ProgramCursor.toCheckedWorldFromSuffix, ProgramCursor.prog,
          ProgramCursor.Γ, ProgramCursor.toSuffixFrom, PMF.pure_map]
      · simp [cursorTransitionState, checkedTransition,
          CursorRuntimeState.toCheckedWorldFromSuffix,
          ProgramCursor.toCheckedWorldFromSuffix, ProgramCursor.prog,
          ProgramCursor.Γ, ProgramCursor.toSuffixFrom, PMF.map, Function.comp_def]
      · simp [cursorTransitionState, checkedTransition,
          CursorRuntimeState.toCheckedWorldFromSuffix,
          ProgramCursor.toCheckedWorldFromSuffix, ProgramCursor.prog,
          ProgramCursor.Γ, ProgramCursor.toSuffixFrom, PMF.pure_map]
      · simp [cursorTransitionState, checkedTransition,
          CursorRuntimeState.toCheckedWorldFromSuffix,
          ProgramCursor.toCheckedWorldFromSuffix, ProgramCursor.prog,
          ProgramCursor.Γ, ProgramCursor.toSuffixFrom, PMF.pure_map])
    (fun c ih suffix env valid a ha => by
      simpa [cursorTransitionState,
        CursorRuntimeState.toCheckedWorldFromSuffix,
        ProgramCursor.toCheckedWorldFromSuffix, ProgramCursor.prog,
        ProgramCursor.Γ, ProgramCursor.toSuffixFrom, PMF.map, PMF.pure_map,
        bind_assoc, Function.comp_def] using
        ih (ProgramSuffix.letExpr suffix) env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))
    (fun c ih suffix env valid a ha => by
      simpa [cursorTransitionState,
        CursorRuntimeState.toCheckedWorldFromSuffix,
        ProgramCursor.toCheckedWorldFromSuffix, ProgramCursor.prog,
        ProgramCursor.Γ, ProgramCursor.toSuffixFrom, PMF.map, PMF.pure_map,
        bind_assoc, Function.comp_def] using
        ih (ProgramSuffix.sample suffix) env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))
    (fun c ih suffix env valid a ha => by
      simpa [cursorTransitionState,
        CursorRuntimeState.toCheckedWorldFromSuffix,
        ProgramCursor.toCheckedWorldFromSuffix, ProgramCursor.prog,
        ProgramCursor.Γ, ProgramCursor.toSuffixFrom, PMF.map, PMF.pure_map,
        bind_assoc, Function.comp_def] using
        ih (ProgramSuffix.commit suffix) env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))
    (fun c ih suffix env valid a ha => by
      simpa [cursorTransitionState,
        CursorRuntimeState.toCheckedWorldFromSuffix,
        ProgramCursor.toCheckedWorldFromSuffix, ProgramCursor.prog,
        ProgramCursor.Γ, ProgramCursor.toSuffixFrom, PMF.map, PMF.pure_map,
        bind_assoc, Function.comp_def] using
        ih (ProgramSuffix.reveal suffix) env
          (by simpa [ProgramCursor.EndpointValid] using valid) a
          (by simpa [ProgramCursor.EndpointValid] using ha))
    c

/-- The program-local finite FOSG transition agrees with the checked-world
transition after erasing program actions and forgetting cursor keys. -/
theorem cursorProgramTransition_map_checkedWorld
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CursorCheckedWorld g)
    (a : {a : ProgramJointAction g //
      CursorProgramJointActionLegal w a}) :
    PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
        (cursorProgramTransition w a) =
      checkedTransition (P := P) (L := L)
        (CheckedWorld.ofCursorChecked (hctx := hctx) w)
        ⟨ProgramJointAction.toAction a.1,
          CursorProgramJointActionLegal.toAction a.2⟩ := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          let hv : cursor.EndpointValid := by
            simpa [CursorWorldData.Valid, CursorWorldData.prog,
              ProgramCursor.EndpointValid] using valid
          rw [cursorProgramTransition]
          change PMF.map
              (CheckedWorld.ofCursorChecked (hctx := hctx))
              (PMF.map CursorRuntimeState.toChecked
                (cursorTransitionState cursor env hv
                  (ProgramJointAction.toAction a.1)
                  (CursorProgramJointActionLegal.toAction a.2))) = _
          rw [show PMF.map
              (CheckedWorld.ofCursorChecked (hctx := hctx))
              (PMF.map CursorRuntimeState.toChecked
                (cursorTransitionState cursor env hv
                  (ProgramJointAction.toAction a.1)
                  (CursorProgramJointActionLegal.toAction a.2))) =
            PMF.map (CursorRuntimeState.toCheckedWorldFromSuffix
                (hctx := hctx) ProgramSuffix.here)
              (cursorTransitionState cursor env hv
                (ProgramJointAction.toAction a.1)
                (CursorProgramJointActionLegal.toAction a.2)) by
            simp [PMF.map, Function.comp_def,
              CursorRuntimeState.toChecked, CheckedWorld.ofCursorChecked,
              CursorRuntimeState.toCheckedWorldFromSuffix,
              ProgramCursor.toSuffix, CursorWorldData.Valid,
              CursorWorldData.prog, CursorWorldData.suffix]]
          simpa [ProgramCursor.toCheckedWorldFromSuffix,
            CheckedWorld.ofCursorChecked, ProgramCursor.toSuffix,
            ProgramCursor.toSuffixFrom, CursorWorldData.Valid,
            CursorWorldData.prog, CursorWorldData.suffix, hv] using
          cursorTransitionState_map_toCheckedWorldFromSuffix
              (hctx := hctx)
              (g := g) (suffix := ProgramSuffix.here) (c := cursor)
              (env := env) (valid := hv)
              (a := ProgramJointAction.toAction a.1)
              (ha := CursorProgramJointActionLegal.toAction a.2)

set_option linter.flexible false in
/-- Every supported cursor-recursive transition consumes exactly one
operational syntax node. -/
theorem cursorTransitionState_remainingSyntaxSteps
    {Γ₀ : VCtx P L} :
    {root : VegasCore P L Γ₀} →
    (c : ProgramCursor root) →
    (env : VEnv L c.Γ) →
    (valid : c.EndpointValid) →
    (a : JointAction P L) →
    (ha : JointActionLegal
      ({ Γ := c.Γ, prog := c.prog, env := env } : World P L) a) →
    (dst : CursorRuntimeState root) →
    cursorTransitionState c env valid a ha dst ≠ 0 →
      syntaxSteps dst.cursor.prog + 1 = syntaxSteps c.prog
  | .ret payoffs, .here, env, valid, a, ha, dst, _hsupp =>
      False.elim (ha.1 (by simp [ProgramCursor.prog, terminal]))
  | .letExpr x e k, .here, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog, syntaxSteps] at hsupp ⊢
      subst dst
      rfl
  | .sample x D k, .here, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog, syntaxSteps] at hsupp ⊢
      rcases hsupp with ⟨v, hdst, _hv⟩
      subst dst
      rfl
  | .commit x who R k, .here, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog, syntaxSteps] at hsupp ⊢
      subst dst
      rfl
  | .reveal y who x hx k, .here, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog, syntaxSteps] at hsupp ⊢
      subst dst
      rfl
  | .letExpr x e k, .letExpr c, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog] at hsupp ⊢
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      have hrec := cursorTransitionState_remainingSyntaxSteps c env
        (by simpa [ProgramCursor.EndpointValid] using valid) a
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      subst dst
      exact hrec
  | .sample x D k, .sample c, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog] at hsupp ⊢
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      have hrec := cursorTransitionState_remainingSyntaxSteps c env
        (by simpa [ProgramCursor.EndpointValid] using valid) a
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      subst dst
      exact hrec
  | .commit x who R k, .commit c, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog] at hsupp ⊢
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      have hrec := cursorTransitionState_remainingSyntaxSteps c env
        (by simpa [ProgramCursor.EndpointValid] using valid) a
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      subst dst
      exact hrec
  | .reveal y who x hx k, .reveal c, env, valid, a, ha, dst, hsupp => by
      simp [cursorTransitionState, ProgramCursor.prog] at hsupp ⊢
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      have hrec := cursorTransitionState_remainingSyntaxSteps c env
        (by simpa [ProgramCursor.EndpointValid] using valid) a
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      subst dst
      exact hrec

set_option linter.flexible false in
/-- The cursor-keyed program transition consumes exactly one operational syntax
node on every supported transition. -/
theorem cursorProgramTransition_remainingSyntaxSteps
    {g : WFProgram P L}
    (w : CursorCheckedWorld g)
    (a : {a : ProgramJointAction g //
      CursorProgramJointActionLegal w a})
    (dst : CursorCheckedWorld g)
    (hsupp : cursorProgramTransition w a dst ≠ 0) :
    dst.remainingSyntaxSteps + 1 = w.remainingSyntaxSteps := by
  rw [cursorProgramTransition] at hsupp
  rcases (PMF.mem_support_map_iff _ _ _).mp (by
      rw [PMF.mem_support_iff]
      exact hsupp) with ⟨s, hsuppS, hdst⟩
  subst dst
  have hstep :=
    cursorTransitionState_remainingSyntaxSteps
      w.1.cursor w.1.env
      (by
        simpa [CursorWorldData.Valid, CursorWorldData.prog,
          ProgramCursor.EndpointValid] using w.2)
      (ProgramJointAction.toAction a.1)
      (CursorProgramJointActionLegal.toAction a.2) s
      (by
        rw [PMF.mem_support_iff] at hsuppS
        exact hsuppS)
  simpa [CursorCheckedWorld.remainingSyntaxSteps, CursorRuntimeState.toChecked,
    CursorWorldData.prog] using hstep

set_option linter.flexible false in
/-- Every supported checked transition consumes exactly one operational syntax
node. -/
theorem checkedTransition_remainingSyntaxSteps
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx)
    (a : {a : JointAction P L // CheckedJointActionLegal w a})
    (dst : CheckedWorld g hctx)
    (hsupp : checkedTransition w a dst ≠ 0) :
    dst.remainingSyntaxSteps + 1 = w.remainingSyntaxSteps := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          exact False.elim (a.2.1 (by simp [checkedTerminal, CheckedWorld.toWorld, terminal]))
      | letExpr x e k =>
          simp [checkedTransition, CheckedWorld.remainingSyntaxSteps, syntaxSteps] at hsupp ⊢
          subst dst
          rfl
      | sample x D k =>
          simp [checkedTransition, CheckedWorld.remainingSyntaxSteps, syntaxSteps] at hsupp ⊢
          rcases hsupp with ⟨v, hdst, _hv⟩
          subst dst
          rfl
      | commit x who R k =>
          simp [checkedTransition, CheckedWorld.remainingSyntaxSteps, syntaxSteps] at hsupp ⊢
          subst dst
          rfl
      | reveal y who x hx k =>
          simp [checkedTransition, CheckedWorld.remainingSyntaxSteps, syntaxSteps] at hsupp ⊢
          subst dst
          rfl

def rewardOnEnteringRet
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (_w : CheckedWorld g hctx)
    (_a : {a : JointAction P L // CheckedJointActionLegal _w a})
    (w' : CheckedWorld g hctx) (who : P) : ℝ :=
  match w'.prog with
  | .ret payoffs => (evalPayoffs payoffs w'.env who : ℝ)
  | _ => 0

/-- Reward over cursor-keyed program-local actions. Rewards are paid when a
transition enters a `ret` continuation. -/
def rewardOnEnteringRetCursor
    {g : WFProgram P L}
    (_w : CursorCheckedWorld g)
    (_a : {a : ProgramJointAction g //
      CursorProgramJointActionLegal _w a})
    (w' : CursorCheckedWorld g) (who : P) : ℝ :=
  match w'.1.prog with
  | .ret payoffs => (evalPayoffs payoffs w'.1.env who : ℝ)
  | _ => 0

end FOSGBridge
end Vegas
