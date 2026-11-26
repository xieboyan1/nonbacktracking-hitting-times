import Stationary
import Hitting
namespace Walks
open Finset Stationary Hitting Filter
open scoped Topology
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : Graph V) (a : V)
def ordinary : Chain V where
  N := G.N
  pos := G.nonempty
  stop i := decide (i=a)
  escape i := ⟨a,G.connected i a,by simp⟩
def allowed (s : V × V) := if (G.N s.1).card = 1 then G.N s.1 else (G.N s.1).erase s.2
def nbNext (s : V × V) := (allowed G s).image (fun j => (j,s.1))
lemma allowed_pos (s : V × V) : (allowed G s).Nonempty := by
  unfold allowed
  split
  · exact G.nonempty _
  · rename_i hd
    by_contra! he
    have le : (G.N s.1).card ≤ 1 := card_le_one.mpr (fun i hi j hj => by
      have eq (v : V) (hv : v ∈ G.N s.1) : v=s.2 := by
        apply Classical.byContradiction
        intro h
        have mem : v ∈ (G.N s.1).erase s.2 := mem_erase.mpr ⟨h,hv⟩
        exact he ⟨v,mem⟩
      exact (eq i hi).trans (eq j hj).symm)
    have pos := (G.nonempty s.1).card_pos
    omega
lemma nbReach (s : V × V) :
    ∃ t, Relation.ReflTransGen (fun x y => y ∈ nbNext G x) s t ∧ t.1 = a := by
  classical
  let R (t : V×V) := univ.filter (Relation.ReflTransGen (fun x y => y ∈ nbNext G x) t)
  have memR (x y : V×V) : y ∈ R x ↔ Relation.ReflTransGen (fun x y => y ∈ nbNext G x) x y := by
    simp [R]
  have self (x : V×V) : x ∈ R x := (memR _ _).mpr .refl
  have sub {x y : V×V} (h : y ∈ R x) : R y ⊆ R x := fun z hz =>
    (memR _ _).mpr (((memR _ _).mp h).trans ((memR _ _).mp hz))
  have step {x y : V×V} (h : y ∈ nbNext G x) : y ∈ R x := (memR _ _).mpr (.single h)
  obtain ⟨b,hb,small⟩ := exists_min_image (R s) (fun t => (R t).card) ⟨s,self _⟩
  have back {x : V×V} (hx : x ∈ R b) : R x = R b :=
    eq_of_subset_of_card_le (sub hx) (small _ (sub hb hx))
  let P (i : V) := ∃ j, (i,j) ∈ R b
  have prev {x : V×V} (hx : x ∈ R b) : P x.2 := by
    obtain ⟨k,hk⟩ := allowed_pos G x
    have edge : (k,x.1) ∈ nbNext G x := mem_image.mpr ⟨k,hk,rfl⟩
    have hy := sub hx (step edge)
    have hr : x ∈ R (k,x.1) := by rw [back hy]; exact hx
    have path := (memR _ _).mp hr
    have lift {t : V×V} (p : Relation.ReflTransGen (fun x y => y ∈ nbNext G x) (k,x.1) t) :
        t ∈ R b ∧ P t.2 := by
      induction p with
      | refl => exact ⟨hy,⟨x.2,hx⟩⟩
      | tail _ h ih =>
        refine ⟨sub ih.1 (step h),?_⟩
        obtain ⟨v,_,rfl⟩ := mem_image.mp h
        exact ⟨_,ih.1⟩
    exact (lift path).2
  have across {i j : V} (p : P i) (hj : j ∈ G.N i) : P j := by
    obtain ⟨k,hk⟩ := p
    by_cases h : j=k
    · subst j; exact prev hk
    · have al : j ∈ allowed G (i,k) := by unfold allowed; split <;> simp [hj, h]
      exact ⟨i,sub hk (step (mem_image.mpr ⟨j,al,rfl⟩))⟩
  have pa : P a := by
    induction G.connected b.1 a with
    | refl => exact ⟨_,self _⟩
    | tail _ h ih => exact across ih h
  obtain ⟨j,hj⟩ := pa
  exact ⟨(a,j),(memR _ _).mp (sub hb hj),rfl⟩
def remembered : Chain (V×V) where
  N := nbNext G
  pos s := (allowed_pos G s).image _
  stop s := decide (s.1=a)
  escape s := by simpa using nbReach G a s
def h := green (ordinary G a)
def w (i j : V) := green (remembered G a) (i,j)
lemma raw : Bellman G a (h G a) (w G a) := by
  have sr (i : V) := first (ordinary G a) i
  have nb (i j : V) := first (remembered G a) (i,j)
  have rows (i j : V) (hi : i≠a) :
      w G a i j = 1 + (∑ k ∈ allowed G (i,j), w G a k i) / (allowed G (i,j)).card := by
    have inj : Function.Injective (fun k : V => (k,i)) := fun _ _ e => congrArg Prod.fst e
    simpa [w, K,alive,remembered,hi,nbNext,Finset.sum_image inj.injOn,
      Finset.card_image_of_injective _ inj] using nb i j
  refine ⟨?_,?_,green_nonneg _,?_,?_⟩
  · simpa [h,K,alive,ordinary] using sr a
  · intro j _; simpa [w,K,alive,remembered] using nb a j
  · intro i hi
    have e := sr i
    change h G a i = _ at e
    simp only [K,alive,ordinary,LinearMap.coe_mk,AddHom.coe_mk,decide_eq_true_eq,hi,if_false] at e
    have d := degree_pos (ordinary G a) i
    change 0 < deg G i at d
    change h G a i = 1 + (∑ j ∈ G.N i,h G a j) / deg G i at e
    field_simp at e
    nlinarith
  · intro i hi j hj
    have r := rows i j hi
    by_cases hd : (G.N i).card=1
    · have sn := eq_singleton_iff_unique_mem.mpr ⟨hj,fun k hk => card_le_one.mp hd.le k hk j hj⟩
      simp [allowed,hd,sn] at r ⊢
      exact r
    · simp only [hd,if_false]
      have r' : w G a i j = 1 + (∑ k ∈ (G.N i).erase j, w G a k i) /
        ((G.N i).erase j).card := by simpa [allowed, hd] using r
      have c := (G.nonempty i).card_pos
      have d : (((G.N i).erase j).card : ℝ) = deg G i-1 := by
        rw [Finset.card_erase_of_mem hj, Nat.cast_sub (by omega)]; simp [deg]
      rw [d] at r'
      have den : deg G i-1 ≠ 0 := by
        have : (2:ℝ) ≤ deg G i := by unfold deg; exact_mod_cast (by omega : 2 ≤ (G.N i).card)
        linarith
      rw [mul_comm]
      apply (eq_div_iff den).mp
      linarith only [r']

-- The entries of h and w are defined by the Green operator. green_mean
-- identifies both with the limits of the finite survival sums.
theorem fixed_target_comparison :
    avg G (fresh G a (w G a)) ≤ avg G (h G a) ∧
    (avg G (fresh G a (w G a)) = avg G (h G a) ↔ ∀ i ∈ G.N a, G.N i={a}) :=
  fixed_target (raw G a)

#print axioms fixed_target_comparison
def truncated {S : Type*} [Fintype S] [DecidableEq S] (C : Chain S) (n : ℕ) (i : S) :=
  ∑ k ∈ range n, survival C k i
def freshTrunc (n : ℕ) (i : V) : ℝ :=
  if i=a then 0 else 1 + (∑ j ∈ G.N i, truncated (remembered G a) n (j,i)) / deg G i
lemma fresh_limit (i : V) : Tendsto (fun n => freshTrunc G a n i) atTop
    (𝓝 (fresh G a (w G a) i)) := by
  by_cases hi : i=a
  · simp [freshTrunc, fresh, hi, tendsto_const_nhds]
  · simp only [freshTrunc, fresh, hi, if_false]
    apply Tendsto.const_add
    apply Tendsto.div_const
    exact tendsto_finset_sum _ (fun j _ => green_mean (remembered G a) (j,i))
lemma average_limit {f : ℕ → V → ℝ} {l : V → ℝ}
    (hf : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (l i))) :
    Tendsto (fun n => avg G (f n)) atTop (𝓝 (avg G l)) := by
  apply Tendsto.div_const
  exact tendsto_finset_sum _ (fun i _ => tendsto_finset_sum _ (fun _ _ => hf i))
theorem stationary_limits :
    Tendsto (fun n => avg G (freshTrunc G a n)) atTop (𝓝 (avg G (fresh G a (w G a)))) ∧
    Tendsto (fun n => avg G (truncated (ordinary G a) n)) atTop (𝓝 (avg G (h G a))) :=
  ⟨average_limit G (fresh_limit G a),average_limit G (green_mean (ordinary G a))⟩
#print axioms stationary_limits
end
end Walks
