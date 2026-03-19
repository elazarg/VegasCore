import Vegas.Protocol.WF

namespace Examples

def va : VarId := 0
def vb : VarId := 1
def va' : VarId := 2
def vb' : VarId := 3

def Γ0 : Ctx := []
def Γ1 : Ctx := [(va, .hidden 0 .bool)]
def Γ2 : Ctx := [(vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
def Γ3 : Ctx := [(va', .pub .bool), (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
def Γ4 : Ctx :=
  [(vb', .pub .bool), (va', .pub .bool),
   (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]

def hva_in_Γ2 : HasVar Γ2 va (.hidden 0 .bool) := .there .here
def hvb_in_Γ3 : HasVar Γ3 vb (.hidden 1 .bool) := .there .here
def hva'_in_Γ4 : HasVar Γ4 va' (.pub .bool) := .there .here
def hvb'_in_Γ4 : HasVar Γ4 vb' (.pub .bool) := .here

def mpPayoff : PayoffMap Γ4 :=
  ⟨[ (0, .ite
        (.eqBool (.var va' hva'_in_Γ4) (.var vb' hvb'_in_Γ4))
        (.constInt 1) (.constInt (-1))),
     (1, .ite
        (.eqBool (.var va' hva'_in_Γ4) (.var vb' hvb'_in_Γ4))
        (.constInt (-1)) (.constInt 1))
   ], by decide⟩

def matchingPennies : Prog Γ0 :=
  .commit va 0 (b := .bool) [true, false] (.constBool true)
    (.commit vb 1 (b := .bool) [true, false] (.constBool true)
      (.reveal va' 0 va hva_in_Γ2
        (.reveal vb' 1 vb hvb_in_Γ3
          (.ret mpPayoff))))

noncomputable def mpProfile : Profile where
  commit := fun {_Γ} {b} _who x _acts _R _view =>
    match x with
    | 0 =>
      match b with
      | .bool => FDist.pure true
      | .int => FDist.zero
    | 1 =>
      match b with
      | .bool => FDist.pure false
      | .int => FDist.zero
    | _ => FDist.zero

def conditionedGame : Prog Γ0 :=
  .commit va 0 (b := .bool) [true, false] (.constBool true)
    (.reveal va' 0 va .here
      (.commit vb 1 (b := .bool) [true, false]
        (.var va' (.there .here))
        (.reveal vb' 1 vb .here
          (.ret ⟨[(0, .constInt 1), (1, .constInt 0)], by decide⟩))))

-- Verify well-formedness predicates on examples
#eval! decide (WF matchingPennies)          -- true
#eval! decide (RevealComplete [] matchingPennies)  -- true
#eval! decide (WF conditionedGame)          -- true
#eval! decide (RevealComplete [] conditionedGame)  -- true

end Examples
