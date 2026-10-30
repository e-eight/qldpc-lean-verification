import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Fin

/-! Generated from 82-2-9.json. Input SHA256: a6b8dfb0ac6006f44ef565e96764b9fbd59f924dd3237b1c4f3b31b4590d6bc1 -/

namespace QldpcVerification.Bicycle82Data

def nq : Nat := 82
def cyclicLength : Nat := 41
def target : Nat := 9

def hx : List (Finset (Fin 82)) := [
  {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨41, by decide⟩, ⟨50, by decide⟩},
  {⟨1, by decide⟩, ⟨2, by decide⟩, ⟨42, by decide⟩, ⟨51, by decide⟩},
  {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨43, by decide⟩, ⟨52, by decide⟩},
  {⟨3, by decide⟩, ⟨4, by decide⟩, ⟨44, by decide⟩, ⟨53, by decide⟩},
  {⟨4, by decide⟩, ⟨5, by decide⟩, ⟨45, by decide⟩, ⟨54, by decide⟩},
  {⟨5, by decide⟩, ⟨6, by decide⟩, ⟨46, by decide⟩, ⟨55, by decide⟩},
  {⟨6, by decide⟩, ⟨7, by decide⟩, ⟨47, by decide⟩, ⟨56, by decide⟩},
  {⟨7, by decide⟩, ⟨8, by decide⟩, ⟨48, by decide⟩, ⟨57, by decide⟩},
  {⟨8, by decide⟩, ⟨9, by decide⟩, ⟨49, by decide⟩, ⟨58, by decide⟩},
  {⟨9, by decide⟩, ⟨10, by decide⟩, ⟨50, by decide⟩, ⟨59, by decide⟩},
  {⟨10, by decide⟩, ⟨11, by decide⟩, ⟨51, by decide⟩, ⟨60, by decide⟩},
  {⟨11, by decide⟩, ⟨12, by decide⟩, ⟨52, by decide⟩, ⟨61, by decide⟩},
  {⟨12, by decide⟩, ⟨13, by decide⟩, ⟨53, by decide⟩, ⟨62, by decide⟩},
  {⟨13, by decide⟩, ⟨14, by decide⟩, ⟨54, by decide⟩, ⟨63, by decide⟩},
  {⟨14, by decide⟩, ⟨15, by decide⟩, ⟨55, by decide⟩, ⟨64, by decide⟩},
  {⟨15, by decide⟩, ⟨16, by decide⟩, ⟨56, by decide⟩, ⟨65, by decide⟩},
  {⟨16, by decide⟩, ⟨17, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩},
  {⟨17, by decide⟩, ⟨18, by decide⟩, ⟨58, by decide⟩, ⟨67, by decide⟩},
  {⟨18, by decide⟩, ⟨19, by decide⟩, ⟨59, by decide⟩, ⟨68, by decide⟩},
  {⟨19, by decide⟩, ⟨20, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩},
  {⟨20, by decide⟩, ⟨21, by decide⟩, ⟨61, by decide⟩, ⟨70, by decide⟩},
  {⟨21, by decide⟩, ⟨22, by decide⟩, ⟨62, by decide⟩, ⟨71, by decide⟩},
  {⟨22, by decide⟩, ⟨23, by decide⟩, ⟨63, by decide⟩, ⟨72, by decide⟩},
  {⟨23, by decide⟩, ⟨24, by decide⟩, ⟨64, by decide⟩, ⟨73, by decide⟩},
  {⟨24, by decide⟩, ⟨25, by decide⟩, ⟨65, by decide⟩, ⟨74, by decide⟩},
  {⟨25, by decide⟩, ⟨26, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩},
  {⟨26, by decide⟩, ⟨27, by decide⟩, ⟨67, by decide⟩, ⟨76, by decide⟩},
  {⟨27, by decide⟩, ⟨28, by decide⟩, ⟨68, by decide⟩, ⟨77, by decide⟩},
  {⟨28, by decide⟩, ⟨29, by decide⟩, ⟨69, by decide⟩, ⟨78, by decide⟩},
  {⟨29, by decide⟩, ⟨30, by decide⟩, ⟨70, by decide⟩, ⟨79, by decide⟩},
  {⟨30, by decide⟩, ⟨31, by decide⟩, ⟨71, by decide⟩, ⟨80, by decide⟩},
  {⟨31, by decide⟩, ⟨32, by decide⟩, ⟨72, by decide⟩, ⟨81, by decide⟩},
  {⟨32, by decide⟩, ⟨33, by decide⟩, ⟨41, by decide⟩, ⟨73, by decide⟩},
  {⟨33, by decide⟩, ⟨34, by decide⟩, ⟨42, by decide⟩, ⟨74, by decide⟩},
  {⟨34, by decide⟩, ⟨35, by decide⟩, ⟨43, by decide⟩, ⟨75, by decide⟩},
  {⟨35, by decide⟩, ⟨36, by decide⟩, ⟨44, by decide⟩, ⟨76, by decide⟩},
  {⟨36, by decide⟩, ⟨37, by decide⟩, ⟨45, by decide⟩, ⟨77, by decide⟩},
  {⟨37, by decide⟩, ⟨38, by decide⟩, ⟨46, by decide⟩, ⟨78, by decide⟩},
  {⟨38, by decide⟩, ⟨39, by decide⟩, ⟨47, by decide⟩, ⟨79, by decide⟩},
  {⟨39, by decide⟩, ⟨40, by decide⟩, ⟨48, by decide⟩, ⟨80, by decide⟩},
  {⟨0, by decide⟩, ⟨40, by decide⟩, ⟨49, by decide⟩, ⟨81, by decide⟩}]

def wx : Nat := 4363137554843648

def detx : Nat := 2251799813687292

def hz : List (Finset (Fin 82)) := [
  {⟨0, by decide⟩, ⟨32, by decide⟩, ⟨41, by decide⟩, ⟨81, by decide⟩},
  {⟨1, by decide⟩, ⟨33, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩},
  {⟨2, by decide⟩, ⟨34, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩},
  {⟨3, by decide⟩, ⟨35, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩},
  {⟨4, by decide⟩, ⟨36, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩},
  {⟨5, by decide⟩, ⟨37, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩},
  {⟨6, by decide⟩, ⟨38, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩},
  {⟨7, by decide⟩, ⟨39, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩},
  {⟨8, by decide⟩, ⟨40, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩},
  {⟨0, by decide⟩, ⟨9, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩},
  {⟨1, by decide⟩, ⟨10, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩},
  {⟨2, by decide⟩, ⟨11, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩},
  {⟨3, by decide⟩, ⟨12, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩},
  {⟨4, by decide⟩, ⟨13, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩},
  {⟨5, by decide⟩, ⟨14, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩},
  {⟨6, by decide⟩, ⟨15, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩},
  {⟨7, by decide⟩, ⟨16, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩},
  {⟨8, by decide⟩, ⟨17, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩},
  {⟨9, by decide⟩, ⟨18, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩},
  {⟨10, by decide⟩, ⟨19, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩},
  {⟨11, by decide⟩, ⟨20, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩},
  {⟨12, by decide⟩, ⟨21, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩},
  {⟨13, by decide⟩, ⟨22, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩},
  {⟨14, by decide⟩, ⟨23, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩},
  {⟨15, by decide⟩, ⟨24, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩},
  {⟨16, by decide⟩, ⟨25, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩},
  {⟨17, by decide⟩, ⟨26, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩},
  {⟨18, by decide⟩, ⟨27, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩},
  {⟨19, by decide⟩, ⟨28, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩},
  {⟨20, by decide⟩, ⟨29, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩},
  {⟨21, by decide⟩, ⟨30, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩},
  {⟨22, by decide⟩, ⟨31, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩},
  {⟨23, by decide⟩, ⟨32, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩},
  {⟨24, by decide⟩, ⟨33, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩},
  {⟨25, by decide⟩, ⟨34, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩},
  {⟨26, by decide⟩, ⟨35, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩},
  {⟨27, by decide⟩, ⟨36, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩},
  {⟨28, by decide⟩, ⟨37, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩},
  {⟨29, by decide⟩, ⟨38, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩},
  {⟨30, by decide⟩, ⟨39, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩},
  {⟨31, by decide⟩, ⟨40, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩}]

def wz : Nat := 2422583301424333375717504

def detz : Nat := 1123700883587073

end QldpcVerification.Bicycle82Data
