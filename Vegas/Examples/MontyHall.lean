import Vegas.StrategicPMF

/-!
# Monty Hall

A checked Vegas encoding of the Monty Hall switching decision. Doors are the
bounded concrete type `range 0 2`.
-/

namespace Vegas
namespace Examples
namespace MontyHall

inductive Player where
  | guest
  | host
deriving DecidableEq, Repr, Fintype

abbrev DoorTy : BaseTy := .range 0 2
abbrev Door : Type := Val DoorTy

def door0 : Door := ⟨0, by decide⟩
def door1 : Door := ⟨1, by decide⟩
def door2 : Door := ⟨2, by decide⟩

lemma door_cases (d : Door) :
    d = door0 ∨ d = door1 ∨ d = door2 := by
  obtain ⟨i, hi⟩ := d
  have hlo : 0 ≤ i := hi.1
  have hhi : i ≤ 2 := hi.2
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
    omega
  rcases hcases with h | h | h <;> subst h
  · left
    rfl
  · right
    left
    rfl
  · right
    right
    rfl

lemma existsDoor_ne_two (a b : Door) :
    ∃ c : Door, c ≠ a ∧ c ≠ b := by
  rcases door_cases a with rfl | rfl | rfl <;>
    rcases door_cases b with rfl | rfl | rfl
  · exact ⟨door1, by decide, by decide⟩
  · exact ⟨door2, by decide, by decide⟩
  · exact ⟨door1, by decide, by decide⟩
  · exact ⟨door2, by decide, by decide⟩
  · exact ⟨door0, by decide, by decide⟩
  · exact ⟨door0, by decide, by decide⟩
  · exact ⟨door1, by decide, by decide⟩
  · exact ⟨door0, by decide, by decide⟩
  · exact ⟨door0, by decide, by decide⟩

abbrev Ctx := VCtx Player simpleExpr
abbrev Prog (Γ : Ctx) := VegasCore Player simpleExpr Γ

def carSecret : VarId := 0
def firstSecret : VarId := 1
def firstPublic : VarId := 2
def openedSecret : VarId := 3
def openedPublic : VarId := 4
def switchSecret : VarId := 5
def switchPublic : VarId := 6
def carPublic : VarId := 7

abbrev Γ0 : Ctx := []
abbrev Γ1 : Ctx :=
  [(carSecret, ⟨DoorTy, .hidden Player.host⟩)]
abbrev Γ2 : Ctx :=
  [(firstSecret, ⟨DoorTy, .hidden Player.guest⟩),
   (carSecret, ⟨DoorTy, .hidden Player.host⟩)]
abbrev Γ3 : Ctx :=
  [(firstPublic, ⟨DoorTy, .pub⟩),
   (firstSecret, ⟨DoorTy, .hidden Player.guest⟩),
   (carSecret, ⟨DoorTy, .hidden Player.host⟩)]
abbrev Γ4 : Ctx :=
  [(openedSecret, ⟨DoorTy, .hidden Player.host⟩),
   (firstPublic, ⟨DoorTy, .pub⟩),
   (firstSecret, ⟨DoorTy, .hidden Player.guest⟩),
   (carSecret, ⟨DoorTy, .hidden Player.host⟩)]
abbrev Γ5 : Ctx :=
  [(openedPublic, ⟨DoorTy, .pub⟩),
   (openedSecret, ⟨DoorTy, .hidden Player.host⟩),
   (firstPublic, ⟨DoorTy, .pub⟩),
   (firstSecret, ⟨DoorTy, .hidden Player.guest⟩),
   (carSecret, ⟨DoorTy, .hidden Player.host⟩)]
abbrev Γ6 : Ctx :=
  [(switchSecret, ⟨.bool, .hidden Player.guest⟩),
   (openedPublic, ⟨DoorTy, .pub⟩),
   (openedSecret, ⟨DoorTy, .hidden Player.host⟩),
   (firstPublic, ⟨DoorTy, .pub⟩),
   (firstSecret, ⟨DoorTy, .hidden Player.guest⟩),
   (carSecret, ⟨DoorTy, .hidden Player.host⟩)]
abbrev Γ7 : Ctx :=
  [(switchPublic, ⟨.bool, .pub⟩),
   (switchSecret, ⟨.bool, .hidden Player.guest⟩),
   (openedPublic, ⟨DoorTy, .pub⟩),
   (openedSecret, ⟨DoorTy, .hidden Player.host⟩),
   (firstPublic, ⟨DoorTy, .pub⟩),
   (firstSecret, ⟨DoorTy, .hidden Player.guest⟩),
   (carSecret, ⟨DoorTy, .hidden Player.host⟩)]
abbrev Γ8 : Ctx :=
  [(carPublic, ⟨DoorTy, .pub⟩),
   (switchPublic, ⟨.bool, .pub⟩),
   (switchSecret, ⟨.bool, .hidden Player.guest⟩),
   (openedPublic, ⟨DoorTy, .pub⟩),
   (openedSecret, ⟨DoorTy, .hidden Player.host⟩),
   (firstPublic, ⟨DoorTy, .pub⟩),
   (firstSecret, ⟨DoorTy, .hidden Player.guest⟩),
   (carSecret, ⟨DoorTy, .hidden Player.host⟩)]

def hFirstSecretΓ2 :
    VHasVar Γ2 firstSecret ⟨DoorTy, .hidden Player.guest⟩ :=
  .here

def hOpenedSecretΓ4 :
    VHasVar Γ4 openedSecret ⟨DoorTy, .hidden Player.host⟩ :=
  .here

def hSwitchSecretΓ6 :
    VHasVar Γ6 switchSecret ⟨.bool, .hidden Player.guest⟩ :=
  .here

def hCarSecretΓ7 :
    VHasVar Γ7 carSecret ⟨DoorTy, .hidden Player.host⟩ :=
  .there (.there (.there (.there (.there (.there .here)))))

def hOpenedCandidateGuard :
    HasVar ((openedSecret, DoorTy) :: eraseVCtx Γ3) openedSecret DoorTy :=
  .here

def hFirstPublicGuard :
    HasVar ((openedSecret, DoorTy) :: eraseVCtx Γ3) firstPublic DoorTy :=
  .there .here

def hCarSecretGuard :
    HasVar ((openedSecret, DoorTy) :: eraseVCtx Γ3) carSecret DoorTy :=
  .there (.there (.there .here))

def openedCandidate : Expr ((openedSecret, DoorTy) :: eraseVCtx Γ3) DoorTy :=
  .var openedSecret hOpenedCandidateGuard

def firstPublicAtHost : Expr ((openedSecret, DoorTy) :: eraseVCtx Γ3) DoorTy :=
  .var firstPublic hFirstPublicGuard

def carSecretAtHost : Expr ((openedSecret, DoorTy) :: eraseVCtx Γ3) DoorTy :=
  .var carSecret hCarSecretGuard

/-- The host must open a door that is neither the guest's first door nor the
car door. -/
def hostOpenGuard : Expr ((openedSecret, DoorTy) :: eraseVCtx Γ3) .bool :=
  .andBool
    (.notBool (.eq openedCandidate firstPublicAtHost))
    (.notBool (.eq openedCandidate carSecretAtHost))

def hFirstPublicΓ3 :
    HasVar (eraseVCtx Γ3) firstPublic DoorTy :=
  .here

def hCarSecretΓ3 :
    HasVar (eraseVCtx Γ3) carSecret DoorTy :=
  .there (.there .here)

def hCarPublicPayoff :
    HasVar (erasePubVCtx Γ8) carPublic DoorTy :=
  .here

def hSwitchPublicPayoff :
    HasVar (erasePubVCtx Γ8) switchPublic .bool :=
  .there .here

def hOpenedPublicPayoff :
    HasVar (erasePubVCtx Γ8) openedPublic DoorTy :=
  .there (.there .here)

def hFirstPublicPayoff :
    HasVar (erasePubVCtx Γ8) firstPublic DoorTy :=
  .there (.there (.there .here))

def carChoice : Expr (erasePubVCtx Γ8) DoorTy :=
  .var carPublic hCarPublicPayoff

def switchChoice : Expr (erasePubVCtx Γ8) .bool :=
  .var switchPublic hSwitchPublicPayoff

def openedChoice : Expr (erasePubVCtx Γ8) DoorTy :=
  .var openedPublic hOpenedPublicPayoff

def firstChoice : Expr (erasePubVCtx Γ8) DoorTy :=
  .var firstPublic hFirstPublicPayoff

def firstEqualsCar : Expr (erasePubVCtx Γ8) .bool :=
  .eq firstChoice carChoice

def guestWins : Expr (erasePubVCtx Γ8) .bool :=
  .ite switchChoice (.notBool firstEqualsCar) firstEqualsCar

def guestPayoff : Expr (erasePubVCtx Γ8) .int :=
  .ite guestWins (.constInt 1) (.constInt 0)

def hostPayoff : Expr (erasePubVCtx Γ8) .int :=
  .ite guestWins (.constInt 0) (.constInt 1)

def hostGuardEnv (first firstHidden car : Door) :
    Env simpleExpr.Val (eraseVCtx Γ3) :=
  Env.cons (x := firstPublic) first
    (Env.cons (x := firstSecret) firstHidden
      (Env.cons (x := carSecret) car (Env.empty simpleExpr.Val)))

theorem hostOpenGuard_iff (opened first firstHidden car : Door) :
    evalGuard (Player := Player) (L := simpleExpr)
        hostOpenGuard opened (hostGuardEnv first firstHidden car) = true ↔
      opened ≠ first ∧ opened ≠ car := by
  change ((!decide (opened = first)) && (!decide (opened = car))) = true ↔
    opened ≠ first ∧ opened ≠ car
  by_cases hfirst : opened = first <;> by_cases hcar : opened = car <;>
    simp [hfirst, hcar]

def payoffEnv (first opened car : Door) (switch : Bool) :
    Env simpleExpr.Val (erasePubVCtx Γ8) :=
  Env.cons (x := carPublic) car
    (Env.cons (x := switchPublic) switch
      (Env.cons (x := openedPublic) opened
        (Env.cons (x := firstPublic) first (Env.empty simpleExpr.Val))))

theorem switching_wins_iff_first_guess_wrong
    (first opened car : Door) :
    evalExpr guestPayoff (payoffEnv first opened car true) =
      if first = car then 0 else 1 := by
  by_cases h : first = car <;>
    simp [guestPayoff, guestWins, firstEqualsCar, firstChoice, carChoice,
      switchChoice, payoffEnv, hFirstPublicPayoff, hCarPublicPayoff,
      hSwitchPublicPayoff, h, Env.get, Env.cons, evalExpr]

theorem staying_wins_iff_first_guess_right
    (first opened car : Door) :
    evalExpr guestPayoff (payoffEnv first opened car false) =
      if first = car then 1 else 0 := by
  by_cases h : first = car <;>
    simp [guestPayoff, guestWins, firstEqualsCar, firstChoice, carChoice,
      switchChoice, payoffEnv, hFirstPublicPayoff, hCarPublicPayoff,
      hSwitchPublicPayoff, h, Env.get, Env.cons, evalExpr]

noncomputable abbrev program : Prog Γ0 :=
  .commit carSecret Player.host (b := DoorTy) (.constBool true)
    (.commit firstSecret Player.guest (b := DoorTy) (.constBool true)
      (.reveal firstPublic Player.guest firstSecret hFirstSecretΓ2
        (.commit openedSecret Player.host (b := DoorTy) hostOpenGuard
          (.reveal openedPublic Player.host openedSecret hOpenedSecretΓ4
            (.commit switchSecret Player.guest (b := .bool) (.constBool true)
              (.reveal switchPublic Player.guest switchSecret hSwitchSecretΓ6
                (.reveal carPublic Player.host carSecret hCarSecretΓ7
                  (.ret [(Player.guest, guestPayoff),
                    (Player.host, hostPayoff)]))))))))

def viewScoped : ViewScoped program := by
  dsimp [program, ViewScoped]
  constructor
  · intro z hz
    simp [simpleExpr, exprDeps] at hz
  · constructor
    · intro z hz
      simp [simpleExpr, exprDeps] at hz
    · constructor
      · intro z hz
        simp [hostOpenGuard, openedCandidate, firstPublicAtHost,
          carSecretAtHost, simpleExpr, exprDeps, visibleVars] at hz ⊢
        aesop
      · constructor
        · intro z hz
          simp [simpleExpr, exprDeps] at hz
        · trivial

def legal : Legal program := by
  dsimp [program, Legal]
  constructor
  · intro _env
    exact ⟨door0, rfl⟩
  · constructor
    · intro _env
      exact ⟨door0, rfl⟩
    · constructor
      · intro env
        let first : Door := env.get hFirstPublicΓ3
        let car : Door := env.get hCarSecretΓ3
        obtain ⟨opened, hneFirst, hneCar⟩ := existsDoor_ne_two first car
        refine ⟨opened, ?_⟩
        change ((!decide (opened = env.get hFirstPublicΓ3)) &&
          (!decide (opened = env.get hCarSecretΓ3))) = true
        simp [first, car, hneFirst, hneCar]
      · constructor
        · intro _env
          exact ⟨true, rfl⟩
        · trivial

def wf : WF program :=
  ⟨by decide, by decide, viewScoped⟩

def normalized : NormalizedDists program := by
  simp [NormalizedDists]

noncomputable def game : WFProgram Player simpleExpr where
  Γ := Γ0
  prog := program
  env := VEnv.empty simpleExpr
  wctx := WFCtx_nil
  wf := wf
  normalized := normalized
  legal := legal

noncomputable instance instFiniteDomains : FiniteDomains game where
  context := inferInstanceAs (FiniteVCtx Γ0)
  program := inferInstanceAs (FiniteProgram program)

noncomputable def pureGame : GameTheory.KernelGame Player :=
  pureKernelGame game

noncomputable def behavioralGame : GameTheory.KernelGame Player :=
  pmfBehavioralKernelGame game

theorem pureGame_outcomeKernel
    (σ : pureGame.Profile) :
    pureGame.outcomeKernel σ = pureOutcomeKernelAt game σ := rfl

theorem behavioralGame_outcomeKernel
    (σ : behavioralGame.Profile) :
    behavioralGame.outcomeKernel σ = behavioralOutcomeKernelPMFAt game σ := rfl

end MontyHall
end Examples
end Vegas
