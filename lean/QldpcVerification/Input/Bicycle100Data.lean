import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Fin

/-! Generated from 100-2-10.json. Input SHA256: 341b681458b06f583b54e9559877fab899aa3522c9117b4a2bb1dfb557a0a1ac -/

namespace QldpcVerification.Bicycle100Data

def nq : Nat := 100
def cyclicLength : Nat := 50
def target : Nat := 10

def hx : List (Finset (Fin 100)) := [
  {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨50, by decide⟩, ⟨59, by decide⟩},
  {⟨1, by decide⟩, ⟨2, by decide⟩, ⟨51, by decide⟩, ⟨60, by decide⟩},
  {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨52, by decide⟩, ⟨61, by decide⟩},
  {⟨3, by decide⟩, ⟨4, by decide⟩, ⟨53, by decide⟩, ⟨62, by decide⟩},
  {⟨4, by decide⟩, ⟨5, by decide⟩, ⟨54, by decide⟩, ⟨63, by decide⟩},
  {⟨5, by decide⟩, ⟨6, by decide⟩, ⟨55, by decide⟩, ⟨64, by decide⟩},
  {⟨6, by decide⟩, ⟨7, by decide⟩, ⟨56, by decide⟩, ⟨65, by decide⟩},
  {⟨7, by decide⟩, ⟨8, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩},
  {⟨8, by decide⟩, ⟨9, by decide⟩, ⟨58, by decide⟩, ⟨67, by decide⟩},
  {⟨9, by decide⟩, ⟨10, by decide⟩, ⟨59, by decide⟩, ⟨68, by decide⟩},
  {⟨10, by decide⟩, ⟨11, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩},
  {⟨11, by decide⟩, ⟨12, by decide⟩, ⟨61, by decide⟩, ⟨70, by decide⟩},
  {⟨12, by decide⟩, ⟨13, by decide⟩, ⟨62, by decide⟩, ⟨71, by decide⟩},
  {⟨13, by decide⟩, ⟨14, by decide⟩, ⟨63, by decide⟩, ⟨72, by decide⟩},
  {⟨14, by decide⟩, ⟨15, by decide⟩, ⟨64, by decide⟩, ⟨73, by decide⟩},
  {⟨15, by decide⟩, ⟨16, by decide⟩, ⟨65, by decide⟩, ⟨74, by decide⟩},
  {⟨16, by decide⟩, ⟨17, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩},
  {⟨17, by decide⟩, ⟨18, by decide⟩, ⟨67, by decide⟩, ⟨76, by decide⟩},
  {⟨18, by decide⟩, ⟨19, by decide⟩, ⟨68, by decide⟩, ⟨77, by decide⟩},
  {⟨19, by decide⟩, ⟨20, by decide⟩, ⟨69, by decide⟩, ⟨78, by decide⟩},
  {⟨20, by decide⟩, ⟨21, by decide⟩, ⟨70, by decide⟩, ⟨79, by decide⟩},
  {⟨21, by decide⟩, ⟨22, by decide⟩, ⟨71, by decide⟩, ⟨80, by decide⟩},
  {⟨22, by decide⟩, ⟨23, by decide⟩, ⟨72, by decide⟩, ⟨81, by decide⟩},
  {⟨23, by decide⟩, ⟨24, by decide⟩, ⟨73, by decide⟩, ⟨82, by decide⟩},
  {⟨24, by decide⟩, ⟨25, by decide⟩, ⟨74, by decide⟩, ⟨83, by decide⟩},
  {⟨25, by decide⟩, ⟨26, by decide⟩, ⟨75, by decide⟩, ⟨84, by decide⟩},
  {⟨26, by decide⟩, ⟨27, by decide⟩, ⟨76, by decide⟩, ⟨85, by decide⟩},
  {⟨27, by decide⟩, ⟨28, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩},
  {⟨28, by decide⟩, ⟨29, by decide⟩, ⟨78, by decide⟩, ⟨87, by decide⟩},
  {⟨29, by decide⟩, ⟨30, by decide⟩, ⟨79, by decide⟩, ⟨88, by decide⟩},
  {⟨30, by decide⟩, ⟨31, by decide⟩, ⟨80, by decide⟩, ⟨89, by decide⟩},
  {⟨31, by decide⟩, ⟨32, by decide⟩, ⟨81, by decide⟩, ⟨90, by decide⟩},
  {⟨32, by decide⟩, ⟨33, by decide⟩, ⟨82, by decide⟩, ⟨91, by decide⟩},
  {⟨33, by decide⟩, ⟨34, by decide⟩, ⟨83, by decide⟩, ⟨92, by decide⟩},
  {⟨34, by decide⟩, ⟨35, by decide⟩, ⟨84, by decide⟩, ⟨93, by decide⟩},
  {⟨35, by decide⟩, ⟨36, by decide⟩, ⟨85, by decide⟩, ⟨94, by decide⟩},
  {⟨36, by decide⟩, ⟨37, by decide⟩, ⟨86, by decide⟩, ⟨95, by decide⟩},
  {⟨37, by decide⟩, ⟨38, by decide⟩, ⟨87, by decide⟩, ⟨96, by decide⟩},
  {⟨38, by decide⟩, ⟨39, by decide⟩, ⟨88, by decide⟩, ⟨97, by decide⟩},
  {⟨39, by decide⟩, ⟨40, by decide⟩, ⟨89, by decide⟩, ⟨98, by decide⟩},
  {⟨40, by decide⟩, ⟨41, by decide⟩, ⟨90, by decide⟩, ⟨99, by decide⟩},
  {⟨41, by decide⟩, ⟨42, by decide⟩, ⟨50, by decide⟩, ⟨91, by decide⟩},
  {⟨42, by decide⟩, ⟨43, by decide⟩, ⟨51, by decide⟩, ⟨92, by decide⟩},
  {⟨43, by decide⟩, ⟨44, by decide⟩, ⟨52, by decide⟩, ⟨93, by decide⟩},
  {⟨44, by decide⟩, ⟨45, by decide⟩, ⟨53, by decide⟩, ⟨94, by decide⟩},
  {⟨45, by decide⟩, ⟨46, by decide⟩, ⟨54, by decide⟩, ⟨95, by decide⟩},
  {⟨46, by decide⟩, ⟨47, by decide⟩, ⟨55, by decide⟩, ⟨96, by decide⟩},
  {⟨47, by decide⟩, ⟨48, by decide⟩, ⟨56, by decide⟩, ⟨97, by decide⟩},
  {⟨48, by decide⟩, ⟨49, by decide⟩, ⟨57, by decide⟩, ⟨98, by decide⟩},
  {⟨0, by decide⟩, ⟨49, by decide⟩, ⟨58, by decide⟩, ⟨99, by decide⟩}]

def wx : Nat := 154969178718164072081260800

def detx : Nat := 1152921504606849020

def hz : List (Finset (Fin 100)) := [
  {⟨0, by decide⟩, ⟨41, by decide⟩, ⟨50, by decide⟩, ⟨99, by decide⟩},
  {⟨1, by decide⟩, ⟨42, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩},
  {⟨2, by decide⟩, ⟨43, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩},
  {⟨3, by decide⟩, ⟨44, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩},
  {⟨4, by decide⟩, ⟨45, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩},
  {⟨5, by decide⟩, ⟨46, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩},
  {⟨6, by decide⟩, ⟨47, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩},
  {⟨7, by decide⟩, ⟨48, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩},
  {⟨8, by decide⟩, ⟨49, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩},
  {⟨0, by decide⟩, ⟨9, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩},
  {⟨1, by decide⟩, ⟨10, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩},
  {⟨2, by decide⟩, ⟨11, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩},
  {⟨3, by decide⟩, ⟨12, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩},
  {⟨4, by decide⟩, ⟨13, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩},
  {⟨5, by decide⟩, ⟨14, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩},
  {⟨6, by decide⟩, ⟨15, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩},
  {⟨7, by decide⟩, ⟨16, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩},
  {⟨8, by decide⟩, ⟨17, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩},
  {⟨9, by decide⟩, ⟨18, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩},
  {⟨10, by decide⟩, ⟨19, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩},
  {⟨11, by decide⟩, ⟨20, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩},
  {⟨12, by decide⟩, ⟨21, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩},
  {⟨13, by decide⟩, ⟨22, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩},
  {⟨14, by decide⟩, ⟨23, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩},
  {⟨15, by decide⟩, ⟨24, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩},
  {⟨16, by decide⟩, ⟨25, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩},
  {⟨17, by decide⟩, ⟨26, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩},
  {⟨18, by decide⟩, ⟨27, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩},
  {⟨19, by decide⟩, ⟨28, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩},
  {⟨20, by decide⟩, ⟨29, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩},
  {⟨21, by decide⟩, ⟨30, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩},
  {⟨22, by decide⟩, ⟨31, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩},
  {⟨23, by decide⟩, ⟨32, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩},
  {⟨24, by decide⟩, ⟨33, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩},
  {⟨25, by decide⟩, ⟨34, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩},
  {⟨26, by decide⟩, ⟨35, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩},
  {⟨27, by decide⟩, ⟨36, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩},
  {⟨28, by decide⟩, ⟨37, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩},
  {⟨29, by decide⟩, ⟨38, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩},
  {⟨30, by decide⟩, ⟨39, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩},
  {⟨31, by decide⟩, ⟨40, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩},
  {⟨32, by decide⟩, ⟨41, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩},
  {⟨33, by decide⟩, ⟨42, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩},
  {⟨34, by decide⟩, ⟨43, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩},
  {⟨35, by decide⟩, ⟨44, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩},
  {⟨36, by decide⟩, ⟨45, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩},
  {⟨37, by decide⟩, ⟨46, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩},
  {⟨38, by decide⟩, ⟨47, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩},
  {⟨39, by decide⟩, ⟨48, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩},
  {⟨40, by decide⟩, ⟨49, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩}]

def wz : Nat := 4961436290685640608625729536

def detz : Nat := 575334852396580865

end QldpcVerification.Bicycle100Data
