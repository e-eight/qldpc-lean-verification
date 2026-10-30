import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Fin

/-! Generated from gb-8-2.json. Input SHA256: 771dd8fccfdf0a1a5175f9029a8afa1af4f91fde2d473cfdd3aeb6992ab1c72f -/

namespace QldpcVerification.BicycleEvenStep16Data

def nq : Nat := 16
def cyclicLength : Nat := 8
def target : Nat := 3

def hx : List (Finset (Fin 16)) := [
  {⟨0, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨14, by decide⟩},
  {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨9, by decide⟩, ⟨15, by decide⟩},
  {⟨1, by decide⟩, ⟨2, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩},
  {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩},
  {⟨3, by decide⟩, ⟨4, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩},
  {⟨4, by decide⟩, ⟨5, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩},
  {⟨5, by decide⟩, ⟨6, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩},
  {⟨6, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩}]

def wx : Nat := 33025

def detx : Nat := 255

def hz : List (Finset (Fin 16)) := [
  {⟨0, by decide⟩, ⟨2, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩},
  {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩},
  {⟨2, by decide⟩, ⟨4, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩},
  {⟨3, by decide⟩, ⟨5, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩},
  {⟨4, by decide⟩, ⟨6, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩},
  {⟨5, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩},
  {⟨0, by decide⟩, ⟨6, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩},
  {⟨1, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨15, by decide⟩}]

def wz : Nat := 259

def detz : Nat := 65280

end QldpcVerification.BicycleEvenStep16Data
