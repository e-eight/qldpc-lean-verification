import QldpcVerification.Lattice.Winding

/-! Walk concatenation preserves the integer lift and the binary edge chain. -/

namespace QldpcVerification.Lattice.Walk

variable {E V : Type} {source target : E → V} {u v w : V}

@[simp] theorem displacement_copy (horizontal : E → Bool) (p : Walk source target u v)
    {u' v' : V} (hu : u = u') (hv : v = v') :
    (p.copy hu hv).displacement horizontal = p.displacement horizontal := by
  subst u'; subst v'; rfl

@[simp] theorem displacement_append (horizontal : E → Bool)
    (p : Walk source target u v) (q : Walk source target v w) :
    (p.append q).displacement horizontal = p.displacement horizontal + q.displacement horizontal := by
  induction p with
  | nil => simp [append, displacement]
  | cons e r p ih =>
    simp only [append, displacement, ih]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

@[simp] theorem binaryChain_copy [Fintype E] [DecidableEq E] (p : Walk source target u v)
    {u' v' : V} (hu : u = u') (hv : v = v') :
    (p.copy hu hv).binaryChain = p.binaryChain := by
  subst u'; subst v'; rfl

@[simp] theorem binaryChain_append [Fintype E] [DecidableEq E]
    (p : Walk source target u v) (q : Walk source target v w) :
    (p.append q).binaryChain = p.binaryChain + q.binaryChain := by
  induction p with
  | nil => simp [append, binaryChain]
  | cons e r p ih => simp [append, binaryChain, ih, add_assoc]

end QldpcVerification.Lattice.Walk
