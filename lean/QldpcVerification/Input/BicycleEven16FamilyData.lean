import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Fin

/-! Generated from gb-8-3.json. Input SHA256: 17a5352ca78f300c5e521594b5f1bac9f70f0337c7d73d55ab021d82fe42c24f -/

namespace QldpcVerification.BicycleEven16FamilyData

def nq : Nat := 16
def cyclicLength : Nat := 8
def target : Nat := 4

def hx : List (Finset (Fin 16)) := [
  {⟨0, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩},
  {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨9, by decide⟩, ⟨14, by decide⟩},
  {⟨1, by decide⟩, ⟨2, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩},
  {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩},
  {⟨3, by decide⟩, ⟨4, by decide⟩, ⟨9, by decide⟩, ⟨12, by decide⟩},
  {⟨4, by decide⟩, ⟨5, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩},
  {⟨5, by decide⟩, ⟨6, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩},
  {⟨6, by decide⟩, ⟨7, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩}]

def wx : Nat := 49409

def detx : Nat := 255

def hz : List (Finset (Fin 16)) := [
  {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩},
  {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩},
  {⟨2, by decide⟩, ⟨5, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩},
  {⟨3, by decide⟩, ⟨6, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩},
  {⟨4, by decide⟩, ⟨7, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩},
  {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩},
  {⟨1, by decide⟩, ⟨6, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩},
  {⟨2, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨15, by decide⟩}]

def wz : Nat := 263

def detz : Nat := 65280

end QldpcVerification.BicycleEven16FamilyData
