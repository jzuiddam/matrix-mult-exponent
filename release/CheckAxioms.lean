import OmegaBound.FinalBound
import PLATFORM.Statements.«T8.1»
import PLATFORM.Statements.«T8_F.1»

/-! Trust check of the release (run by `release/reproduce.sh check`; expected output in
`release/CheckAxioms.expected`). The two `example`s fail to elaborate unless the theorems have
exactly the frozen statement types of `PLATFORM/Statements/T8.1.lean` and
`PLATFORM/Statements/T8_F.1.lean`. -/

universe u

#print axioms OmegaBound.omegaMM_lt_2371339
#print axioms OmegaBound.omegaMM_lt_2371339_allFields
#print axioms OmegaBound.ADVXXZFinal.omegaMM_lt_target114
#print axioms OmegaBound.ADVXXZGeneral.omegaMM_lt_target_allFields

example : S_T8_1 := OmegaBound.omegaMM_lt_2371339
example : OmegaBound.ADVXXZGeneral.S_T8_F_1.{u} := OmegaBound.omegaMM_lt_2371339_allFields.{u}

#check (OmegaBound.omegaMM_lt_2371339 : S_T8_1)
#check (OmegaBound.omegaMM_lt_2371339_allFields.{0} : OmegaBound.ADVXXZGeneral.S_T8_F_1.{0})
