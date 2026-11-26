import Fundamental
namespace Corridors
open Finset Stationary Walks Fundamental
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : Graph V)
abbrev Arc := (i : V) × {j // j ∈ G.N i}
def pair (s : Arc G) : V×V := (s.1,s.2.val)
lemma ext_pair {x y : Arc G} (h : pair G x=pair G y) : x=y := by
  rcases x with ⟨i,j,hj⟩; rcases y with ⟨k,l,hl⟩
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj h; rfl
def turn (s : Arc G) : V :=
  if (G.N s.1).card=2 then (allowed_pos G (pair G s)).choose else s.2.val
lemma legalTurn (s : Arc G) : turn G s ∈ G.N s.1 := by
  by_cases hd : (G.N s.1).card=2
  · have p := (allowed_pos G (pair G s)).choose_spec
    let k := (allowed_pos G (pair G s)).choose
    change k ∈ allowed G (pair G s) at p
    unfold turn; rw [if_pos hd]
    simp [allowed,pair,hd] at p; exact p.2
  · simp [turn,hd,s.2.property]
lemma different (s : Arc G) (hd : (G.N s.1).card=2) : turn G s≠s.2.val := by
  have p := (allowed_pos G (pair G s)).choose_spec
  let k := (allowed_pos G (pair G s)).choose
  change k ∈ allowed G (pair G s) at p
  simp [allowed,pair,hd] at p; unfold turn; rw [if_pos hd]; exact p.1
def advance (s : Arc G) : Arc G := ⟨turn G s,s.1,G.symm.mp (legalTurn G s)⟩
lemma inject : Function.Injective (advance G) := by
  rintro ⟨i,j,hj⟩ ⟨k,l,hl⟩ h
  have eq := congrArg (pair G) h
  change (turn G ⟨i,j,hj⟩,i) = (turn G ⟨k,l,hl⟩,k) at eq
  obtain ⟨t,rfl⟩ := Prod.mk.inj eq
  suffices j=l by subst l; rfl
  by_cases hd : (G.N i).card=2
  · let v := turn G ⟨i,j,hj⟩
    have hv : v ∈ G.N i := legalTurn G _
    have hj' : j ∈ (G.N i).erase v := mem_erase.mpr ⟨(different G ⟨i,j,hj⟩ hd).symm,hj⟩
    have hl' : l ∈ (G.N i).erase v := mem_erase.mpr ⟨by rw [show v=turn G ⟨i,l,hl⟩ from t]; exact (different G ⟨i,l,hl⟩ hd).symm,hl⟩
    exact card_le_one.mp (by simp [card_erase_of_mem hv,hd]) j hj' l hl'
  · simpa [turn,hd] using t
lemma reaches (hd : Mindeg G) (hb : Branching G) (s : Arc G) :
    ∃ n : ℕ, 3 ≤ (G.N (((advance G)^[n]) s).1).card := by
  obtain ⟨a,ha⟩ := hb
  obtain ⟨b,path,hb⟩ := nbReach G a (pair G s)
  have go {p : V×V} (q : Relation.ReflTransGen (fun x y => y ∈ nbNext G x) p b) :
      ∀ r : Arc G, pair G r=p → ∃ n : ℕ, 3 ≤ (G.N (((advance G)^[n]) r).1).card := by
    induction q using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro r hr; refine ⟨0,?_⟩
      have e := congrArg Prod.fst hr
      change r.1=b.1 at e; simpa [e,hb] using ha
    | @head x y edge _ ih =>
      intro r hr
      by_cases branch : 3 ≤ (G.N r.1).card
      · exact ⟨0,branch⟩
      have deg2 : (G.N r.1).card=2 := by have := hd r.1; omega
      subst x
      obtain ⟨k,hk,rfl⟩ := mem_image.mp edge
      have p := (allowed_pos G (pair G r)).choose_spec
      have small : (allowed G (pair G r)).card ≤ 1 := by
        simp [allowed,pair,deg2,card_erase_of_mem r.2.property]
      have same := card_le_one.mp small _ p _ hk
      have next : pair G (advance G r)=(k,(pair G r).1) := by simp [pair,advance,turn,deg2] at same ⊢; exact same
      obtain ⟨n,hn⟩ := ih (advance G r) next
      exact ⟨n+1,by simpa only [Function.iterate_succ_apply] using hn⟩
  exact go path s rfl
def distance (hd : Mindeg G) (hb : Branching G) (s : Arc G) := Nat.find (reaches G hd hb s)
def lengthBound (hd : Mindeg G) (hb : Branching G) := 1+univ.sup (distance G hd hb)
def owner (hd : Mindeg G) (hb : Branching G) (s : Arc G) := (advance G)^[distance G hd hb s] s
lemma owner_high (hd : Mindeg G) (hb : Branching G) (s : Arc G) :
    3 ≤ (G.N (owner G hd hb s).1).card := Nat.find_spec (reaches G hd hb s)
lemma to_arcs (f : V → V → ℝ) : es G f = ∑ s : Arc G, f s.1 s.2.val := by
  rw [Fintype.sum_sigma]; apply sum_congr rfl; intro i _
  exact (Finset.sum_attach (G.N i) (f i)).symm

-- A centred antisymmetric flow is constant in magnitude up to the first
-- branching vertex. The pair (terminal port, distance) identifies the arc.
theorem chain_norm (hd : Mindeg G) (hb : Branching G) (c : V → V → ℝ)
    (anti : ∀ i j, c i j = -c j i) (cen : ∀ i, ∑ j ∈ G.N i,c i j=0) :
    es G (fun i j => (c i j)^2) ≤ (lengthBound G hd hb : ℝ) *
      es G (fun i j => if 3≤(G.N i).card then (c i j)^2 else 0) := by
  let val (s : Arc G) := (c s.1 s.2.val)^2
  have preserves (s : Arc G) (h : ¬3 ≤ (G.N s.1).card) : val (advance G s) = val s := by
    have d : (G.N s.1).card=2 := by have := hd s.1; omega
    have m := legalTurn G s
    have p := s.2.property
    have ne := different G s d
    have er := sum_erase_add (G.N s.1) (c s.1) p
    have sn : (G.N s.1).erase s.2.val={turn G s} :=
      eq_singleton_iff_unique_mem.mpr ⟨mem_erase.mpr ⟨ne,m⟩, fun k hk =>
        card_le_one.mp (by simp [card_erase_of_mem p,d]) k hk _ (mem_erase.mpr ⟨ne,m⟩)⟩
    rw [sn,sum_singleton,cen] at er
    change (c (turn G s) s.1)^2=_
    rw [anti,neg_sq]; dsimp [val]
    nlinarith only [congrArg (fun z : ℝ => z^2) (eq_neg_of_add_eq_zero_left er)]
  have conserved (s : Arc G) (n : ℕ) (hn : n ≤ distance G hd hb s) : val (((advance G)^[n]) s)=val s := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have h := Nat.find_min (reaches G hd hb s) (show n<distance G hd hb s by omega)
      rw [Function.iterate_succ_apply',preserves _ h,ih (by omega)]
  let L := lengthBound G hd hb
  let encode (s : Arc G) : Arc G × Fin L :=
    (owner G hd hb s,⟨distance G hd hb s, by have := le_sup (f:=distance G hd hb) (mem_univ s); dsimp [L,lengthBound]; omega⟩)
  have inj : Function.Injective encode := by
    intro s t eq
    have ed := congrArg (fun x : Arc G×Fin L => x.2.val) eq
    have eo := congrArg Prod.fst eq
    change distance G hd hb s=distance G hd hb t at ed
    change (advance G)^[distance G hd hb s] s=(advance G)^[distance G hd hb t] t at eo
    rw [ed] at eo; exact (inject G).iterate _ eo
  let weight (p : Arc G × Fin L) : ℝ := if 3 ≤ (G.N p.1.1).card then val p.1 else 0
  have equiv (s : Arc G) : weight (encode s)=val s := by
    change (if 3≤(G.N (owner G hd hb s).1).card then val (owner G hd hb s) else 0)=val s
    rw [if_pos (owner_high G hd hb s)]; exact conserved s _ le_rfl
  have le : (∑ p ∈ univ.image encode,weight p) ≤ ∑ p,weight p := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro p _ _; dsimp [weight,val]; split <;> positivity
  rw [sum_image inj.injOn] at le
  simp only [equiv] at le
  rw [to_arcs,to_arcs]
  convert le using 1
  rw [Fintype.sum_prod_type]
  simp [weight,val,Finset.mul_sum,L]
end
end Corridors
