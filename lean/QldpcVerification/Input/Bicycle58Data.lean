import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Fin

/-! Generated from 58-2-7.json. Input SHA256: 59411384eff3dc48df922f5f3674d9cbaaa4f0844688722170c0679f1f30ca91 -/

namespace QldpcVerification.Bicycle58Data

def nq : Nat := 58
def cyclicLength : Nat := 29
def target : Nat := 7

def hx : List (Finset (Fin 58)) := [
  {⟨0, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨50, by decide⟩},
  {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨30, by decide⟩, ⟨51, by decide⟩},
  {⟨1, by decide⟩, ⟨2, by decide⟩, ⟨31, by decide⟩, ⟨52, by decide⟩},
  {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨32, by decide⟩, ⟨53, by decide⟩},
  {⟨3, by decide⟩, ⟨4, by decide⟩, ⟨33, by decide⟩, ⟨54, by decide⟩},
  {⟨4, by decide⟩, ⟨5, by decide⟩, ⟨34, by decide⟩, ⟨55, by decide⟩},
  {⟨5, by decide⟩, ⟨6, by decide⟩, ⟨35, by decide⟩, ⟨56, by decide⟩},
  {⟨6, by decide⟩, ⟨7, by decide⟩, ⟨36, by decide⟩, ⟨57, by decide⟩},
  {⟨7, by decide⟩, ⟨8, by decide⟩, ⟨29, by decide⟩, ⟨37, by decide⟩},
  {⟨8, by decide⟩, ⟨9, by decide⟩, ⟨30, by decide⟩, ⟨38, by decide⟩},
  {⟨9, by decide⟩, ⟨10, by decide⟩, ⟨31, by decide⟩, ⟨39, by decide⟩},
  {⟨10, by decide⟩, ⟨11, by decide⟩, ⟨32, by decide⟩, ⟨40, by decide⟩},
  {⟨11, by decide⟩, ⟨12, by decide⟩, ⟨33, by decide⟩, ⟨41, by decide⟩},
  {⟨12, by decide⟩, ⟨13, by decide⟩, ⟨34, by decide⟩, ⟨42, by decide⟩},
  {⟨13, by decide⟩, ⟨14, by decide⟩, ⟨35, by decide⟩, ⟨43, by decide⟩},
  {⟨14, by decide⟩, ⟨15, by decide⟩, ⟨36, by decide⟩, ⟨44, by decide⟩},
  {⟨15, by decide⟩, ⟨16, by decide⟩, ⟨37, by decide⟩, ⟨45, by decide⟩},
  {⟨16, by decide⟩, ⟨17, by decide⟩, ⟨38, by decide⟩, ⟨46, by decide⟩},
  {⟨17, by decide⟩, ⟨18, by decide⟩, ⟨39, by decide⟩, ⟨47, by decide⟩},
  {⟨18, by decide⟩, ⟨19, by decide⟩, ⟨40, by decide⟩, ⟨48, by decide⟩},
  {⟨19, by decide⟩, ⟨20, by decide⟩, ⟨41, by decide⟩, ⟨49, by decide⟩},
  {⟨20, by decide⟩, ⟨21, by decide⟩, ⟨42, by decide⟩, ⟨50, by decide⟩},
  {⟨21, by decide⟩, ⟨22, by decide⟩, ⟨43, by decide⟩, ⟨51, by decide⟩},
  {⟨22, by decide⟩, ⟨23, by decide⟩, ⟨44, by decide⟩, ⟨52, by decide⟩},
  {⟨23, by decide⟩, ⟨24, by decide⟩, ⟨45, by decide⟩, ⟨53, by decide⟩},
  {⟨24, by decide⟩, ⟨25, by decide⟩, ⟨46, by decide⟩, ⟨54, by decide⟩},
  {⟨25, by decide⟩, ⟨26, by decide⟩, ⟨47, by decide⟩, ⟨55, by decide⟩},
  {⟨26, by decide⟩, ⟨27, by decide⟩, ⟨48, by decide⟩, ⟨56, by decide⟩},
  {⟨27, by decide⟩, ⟨28, by decide⟩, ⟨49, by decide⟩, ⟨57, by decide⟩}]

def wx : Nat := 70375203537416

def detx : Nat := 562950220808192

def hz : List (Finset (Fin 58)) := [
  {⟨0, by decide⟩, ⟨8, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩},
  {⟨1, by decide⟩, ⟨9, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩},
  {⟨2, by decide⟩, ⟨10, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩},
  {⟨3, by decide⟩, ⟨11, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩},
  {⟨4, by decide⟩, ⟨12, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩},
  {⟨5, by decide⟩, ⟨13, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩},
  {⟨6, by decide⟩, ⟨14, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩},
  {⟨7, by decide⟩, ⟨15, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩},
  {⟨8, by decide⟩, ⟨16, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩},
  {⟨9, by decide⟩, ⟨17, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩},
  {⟨10, by decide⟩, ⟨18, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩},
  {⟨11, by decide⟩, ⟨19, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩},
  {⟨12, by decide⟩, ⟨20, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩},
  {⟨13, by decide⟩, ⟨21, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩},
  {⟨14, by decide⟩, ⟨22, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩},
  {⟨15, by decide⟩, ⟨23, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩},
  {⟨16, by decide⟩, ⟨24, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩},
  {⟨17, by decide⟩, ⟨25, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩},
  {⟨18, by decide⟩, ⟨26, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩},
  {⟨19, by decide⟩, ⟨27, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩},
  {⟨20, by decide⟩, ⟨28, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩},
  {⟨0, by decide⟩, ⟨21, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩},
  {⟨1, by decide⟩, ⟨22, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩},
  {⟨2, by decide⟩, ⟨23, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩},
  {⟨3, by decide⟩, ⟨24, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩},
  {⟨4, by decide⟩, ⟨25, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩},
  {⟨5, by decide⟩, ⟨26, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩},
  {⟨6, by decide⟩, ⟨27, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩},
  {⟨7, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨57, by decide⟩}]

def wz : Nat := 4521329789272067

def detz : Nat := 285978576874897409

end QldpcVerification.Bicycle58Data
