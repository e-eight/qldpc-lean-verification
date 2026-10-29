import Mathlib.Tactic

/-! Finite binary cycles contain a closed trail detected by any nonzero edge sum.
The edge-indexed formulation also permits parallel edges and loops. -/

namespace QldpcVerification.Lattice

variable {E V : Type} (source target : E → V)

def stepSource (e : E) (reverse : Bool) : V := if reverse then target e else source e
def stepTarget (e : E) (reverse : Bool) : V := if reverse then source e else target e

inductive Walk : V → V → Type
  | nil (v : V) : Walk v v
  | cons (e : E) (reverse : Bool) {v : V}
      (p : Walk (stepTarget source target e reverse) v) :
      Walk (stepSource source target e reverse) v

namespace Walk

variable {source target} {u v w : V}

def edges : {u v : V} → Walk source target u v → List E
  | _, _, .nil _ => []
  | _, _, .cons e _ p => e :: edges p

def length (p : Walk source target u v) : ℕ := p.edges.length

def append : {u v w : V} → Walk source target u v → Walk source target v w →
    Walk source target u w
  | _, _, _, .nil _, q => q
  | _, _, _, .cons e r p, q => .cons e r (append p q)

def single (e : E) (r : Bool) :
    Walk source target (stepSource source target e r) (stepTarget source target e r) :=
  .cons e r (.nil _)

def copy (p : Walk source target u v) {u' v' : V} (hu : u = u') (hv : v = v') :
    Walk source target u' v' := hu ▸ hv ▸ p

@[simp] theorem edges_copy (p : Walk source target u v) {u' v' : V}
    (hu : u = u') (hv : v = v') : (p.copy hu hv).edges = p.edges := by
  subst u'; subst v'; rfl

@[simp] theorem edges_append (p : Walk source target u v) (q : Walk source target v w) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil => rfl
  | cons e r p ih => simp [append, edges, ih]

@[simp] theorem edges_single (e : E) (r : Bool) : (single (source := source) (target := target) e r).edges = [e] := rfl

@[simp] theorem length_append (p : Walk source target u v) (q : Walk source target v w) :
    (p.append q).length = p.length + q.length := by simp [length]

@[simp] theorem length_single (e : E) (r : Bool) :
    (single (source := source) (target := target) e r).length = 1 := rfl

theorem length_le_card [DecidableEq E] (p : Walk source target u v) (S : Finset E)
    (hn : p.edges.Nodup) (hs : ∀ e ∈ p.edges, e ∈ S) : p.length ≤ S.card := by
  rw [length, ← List.toFinset_card_of_nodup hn]
  exact Finset.card_le_card (fun e he => hs e (List.mem_toFinset.mp he))

end Walk

def incidence [DecidableEq V] (e : E) (v : V) : ZMod 2 :=
  (if source e = v then 1 else 0) + (if target e = v then 1 else 0)

theorem incidence_step [DecidableEq V] (e : E) (r : Bool) (v : V) :
    incidence source target e v =
      (if stepSource source target e r = v then 1 else 0) +
      (if stepTarget source target e r = v then 1 else 0) := by
  cases r <;> simp [incidence, stepSource, stepTarget, add_comm]

theorem two_eq_zero : (2 : ZMod 2) = 0 := by decide

namespace Walk

variable {source target} {u v : V} [DecidableEq V]

theorem incidence_sum (p : Walk source target u v) (a : V) :
    (p.edges.map (fun e => incidence source target e a)).sum =
      (if u = a then 1 else 0) + (if v = a then 1 else 0) := by
  induction p with
  | nil v => by_cases h : v = a <;> simp [edges, h, ← two_mul, two_eq_zero]
  | cons e r p ih =>
    simp only [edges, List.map_cons, List.sum_cons, ih]
    rw [incidence_step source target e r a]
    split_ifs <;> decide

end Walk

def IsCycle [DecidableEq V] (S : Finset E) : Prop :=
  ∀ v, ∑ e ∈ S, incidence source target e v = 0

theorem exists_maximal_trail [DecidableEq E] [Nonempty V] (S : Finset E) :
    ∃ (u v : V) (p : Walk source target u v), p.edges.Nodup ∧ (∀ e ∈ p.edges, e ∈ S) ∧
      ∀ u' v' (q : Walk source target u' v'), q.edges.Nodup →
        (∀ e ∈ q.edges, e ∈ S) → q.length ≤ p.length := by
  classical
  let P (n : ℕ) := ∃ (u v : V) (p : Walk source target u v),
    p.edges.Nodup ∧ (∀ e ∈ p.edges, e ∈ S) ∧ p.length = n
  have h0 : P 0 := ⟨Classical.arbitrary V, Classical.arbitrary V, .nil _, by simp [Walk.edges],
    by simp [Walk.edges], rfl⟩
  obtain ⟨u, v, p, hn, hs, hl⟩ := Nat.findGreatest_spec (Nat.zero_le S.card) h0
  refine ⟨u, v, p, hn, hs, ?_⟩
  intro u' v' q hqn hqs
  rw [hl]
  exact Nat.le_findGreatest (Walk.length_le_card q S hqn hqs) ⟨u', v', q, hqn, hqs, rfl⟩

theorem maximal_trail_closed [DecidableEq E] [DecidableEq V]
    (S : Finset E) (hc : IsCycle source target S)
    {u v : V} (p : Walk source target u v)
    (hn : p.edges.Nodup) (hs : ∀ e ∈ p.edges, e ∈ S)
    (hm : ∀ u' v' (q : Walk source target u' v'), q.edges.Nodup →
      (∀ e ∈ q.edges, e ∈ S) → q.length ≤ p.length) : u = v := by
  classical
  by_contra huv
  let T := p.edges.toFinset
  have hTS : T ⊆ S := fun e he => hs e (List.mem_toFinset.mp he)
  have hp : ∑ e ∈ T, incidence source target e v = 1 := by
    rw [show T = p.edges.toFinset from rfl, List.sum_toFinset _ hn]
    simpa [huv] using p.incidence_sum v
  have hr : ∑ e ∈ S \ T, incidence source target e v ≠ 0 := by
    have hh := Finset.sum_sdiff hTS (f := fun e => incidence source target e v)
    rw [hc v, hp] at hh
    intro h
    rw [h] at hh
    norm_num at hh
  obtain ⟨e, he, hev⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  have heS := (Finset.mem_sdiff.mp he).1
  have heT : e ∉ p.edges := by simpa [T] using (Finset.mem_sdiff.mp he).2
  have hi : source e = v ∨ target e = v := by
    by_contra h
    simp only [not_or] at h
    simp [incidence, h.1, h.2] at hev
  rcases hi with h | h
  · let q := p.append ((Walk.single e false).copy (by simpa [stepSource] using h) rfl)
    have hqn : q.edges.Nodup := by
      simp [q, List.nodup_append, hn]
      intro a ha h
      exact heT (h ▸ ha)
    have hqs : ∀ a ∈ q.edges, a ∈ S := by
      intro a ha
      simp only [q, Walk.edges_append, Walk.edges_copy, Walk.edges_single, List.mem_append,
        List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hs a ha
      · exact heS
    have hh := hm _ _ q hqn hqs
    simp [q, Walk.length] at hh
  · let q := p.append ((Walk.single e true).copy (by simpa [stepSource] using h) rfl)
    have hqn : q.edges.Nodup := by
      simp [q, List.nodup_append, hn]
      intro a ha h
      exact heT (h ▸ ha)
    have hqs : ∀ a ∈ q.edges, a ∈ S := by
      intro a ha
      simp only [q, Walk.edges_append, Walk.edges_copy, Walk.edges_single, List.mem_append,
        List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hs a ha
      · exact heS
    have hh := hm _ _ q hqn hqs
    simp [q, Walk.length] at hh

theorem detected_closed_trail [DecidableEq E] [DecidableEq V] [Nonempty V]
    {A : Type} [AddCommGroup A] (label : E → A) (S : Finset E)
    (hc : IsCycle source target S) (hl : ∑ e ∈ S, label e ≠ 0) :
    ∃ (v : V) (p : Walk source target v v), p.edges.Nodup ∧
      (∀ e ∈ p.edges, e ∈ S) ∧ (p.edges.map label).sum ≠ 0 := by
  classical
  revert hc hl
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hc hl
    obtain ⟨u, v, p, hn, hs, hm⟩ := exists_maximal_trail source target S
    obtain rfl := maximal_trail_closed source target S hc p hn hs hm
    have hpos : 0 < p.length := by
      obtain ⟨e, he, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hl
      have hh := hm _ _ (Walk.single e false) (by simp [Walk.edges, Walk.single])
        (by simpa using he)
      simpa using hh
    by_cases hp : (p.edges.map label).sum ≠ 0
    · exact ⟨u, p, hn, hs, hp⟩
    · have hp0 : (p.edges.map label).sum = 0 := not_ne_iff.mp hp
      let T := p.edges.toFinset
      have hTS : T ⊆ S := fun e he => hs e (List.mem_toFinset.mp he)
      have hcT (a : V) : ∑ e ∈ T, incidence source target e a = 0 := by
        rw [show T = p.edges.toFinset from rfl, List.sum_toFinset _ hn, p.incidence_sum]
        by_cases h : u = a <;> simp [h, ← two_mul, two_eq_zero]
      have hcR : IsCycle source target (S \ T) := by
        intro a
        simpa [hc a, hcT a] using
          (Finset.sum_sdiff hTS (f := fun e => incidence source target e a))
      have hlT : ∑ e ∈ T, label e = 0 := by
        rw [show T = p.edges.toFinset from rfl, List.sum_toFinset _ hn]
        exact hp0
      have hlR : ∑ e ∈ S \ T, label e ≠ 0 := by
        have hh : (∑ e ∈ S \ T, label e) = ∑ e ∈ S, label e := by
          simpa [hlT] using (Finset.sum_sdiff hTS (f := label))
        rwa [hh]
      have hnonempty : ∃ e, e ∈ p.edges := by
        cases h : p.edges with
        | nil => simp [Walk.length, h] at hpos
        | cons e es => exact ⟨e, by simp⟩
      obtain ⟨e, he⟩ := hnonempty
      have hlt : S \ T ⊂ S := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro h
        have hmem : e ∈ S \ T := by rw [h]; exact hs e he
        exact (Finset.mem_sdiff.mp hmem).2 (List.mem_toFinset.mpr he)
      obtain ⟨w, q, hqn, hqs, hql⟩ := ih (S \ T) hlt hcR hlR
      exact ⟨w, q, hqn, fun a ha => (Finset.mem_sdiff.mp (hqs a ha)).1, hql⟩

end QldpcVerification.Lattice
