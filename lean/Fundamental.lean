import Walks
namespace Fundamental
open Finset Stationary Walks
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : Graph V)
abbrev Port (V : Type*) := V × V → ℝ
def tot (f : Port V) := es G (fun i j => f (i,j))
def bar (f : Port V) (i : V) := (∑ j ∈ G.N i, f (i,j))/deg G i
def mass (f : Port V) := tot G f / vol G
def F : Port V →ₗ[ℝ] Port V where
  toFun f s := (∑ j ∈ allowed G s, f (j,s.1))/(allowed G s).card
  map_add' f g := by ext s; simp [sum_add_distrib, add_div]
  map_smul' c f := by ext s; simp [←mul_sum, mul_div_assoc]
def W : Port V →ₗ[ℝ] Port V where
  toFun f _ := mass G f
  map_add' f g := by ext s; simp [mass,tot,es,sum_add_distrib,add_div]
  map_smul' c f := by ext s; simp [mass,tot,es,←mul_sum,mul_div_assoc]
def system : Port V →ₗ[ℝ] Port V := LinearMap.id-F G+W G
def Mindeg := ∀ i, 2 ≤ (G.N i).card
def Branching := ∃ i, 3 ≤ (G.N i).card
lemma dp (i : V) : 0< deg G i := by unfold deg; exact_mod_cast (G.nonempty i).card_pos
lemma at_port (hd : Mindeg G) (f : Port V) {i j : V} (hj : j ∈ G.N i) :
    (deg G i-1)*F G f (i,j)+f (j,i) = ∑ k ∈ G.N i, f (k,i) := by
  have d := hd i
  have neq : (G.N i).card ≠ 1 := by omega
  have nonz : (((G.N i).erase j).card : ℝ) ≠ 0 := by rw [card_erase_of_mem hj]; exact_mod_cast (by omega : (G.N i).card-1 ≠ 0)
  have len : ((G.N i).erase j).card = (G.N i).card-1 := card_erase_of_mem hj
  have realLen : (((G.N i).erase j).card : ℝ) = deg G i-1 := by rw [len,Nat.cast_sub (by omega)]; simp [deg]
  change _*( (∑ k ∈ allowed G (i,j),f (k,i))/(allowed G (i,j)).card) + _ = _
  simp only [allowed,neq,if_false,←realLen,mul_comm (((G.N i).erase j).card : ℝ),div_mul_cancel₀ _ nonz]
  exact sum_erase_add _ _ hj
lemma balance (hd : Mindeg G) (f : Port V) (i : V) :
    ∑ j ∈ G.N i, F G f (i,j) = ∑ j ∈ G.N i, f (j,i) := by
  have e := sum_congr rfl (fun j (hj : j ∈ G.N i) => at_port G hd f hj)
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul] at e
  have d : 2 ≤ deg G i := by unfold deg; exact_mod_cast hd i
  change (deg G i-1)*_ +_ = deg G i*_ at e
  exact (mul_left_cancel₀ (show deg G i-1 ≠ 0 by linarith)) (by linarith only [e] : (deg G i-1)*_ = (deg G i-1)*_)
lemma invariant (hd : Mindeg G) (f : Port V) : tot G (F G f) = tot G f := by
  calc
    _ = es G (fun i j => f (j,i)) := sum_congr rfl fun i _ => balance G hd f i
    _ = _ := flip G (fun i j => f (i,j))
lemma tot_const (c : ℝ) : tot G (fun _ => c) = vol G*c := by
  simp [tot,es,vol,deg,sum_mul]
lemma common (hb : Branching G) : ∃ i, ∀ j k : V, ∃ t ∈ G.N i, t≠j ∧ t≠k := by
  obtain ⟨i,d⟩ := hb
  refine ⟨i,fun j k => ?_⟩
  by_contra! hn
  have sub : G.N i ⊆ {j,k} := by
    intro t ht; by_cases h : t=j
    · simp [h]
    · simp [hn t ht h]
  have le := card_le_card sub
  have aux := card_insert_le j ({k} : Finset V)
  simp only [card_singleton] at aux; omega
lemma harmonic_const (hb : Branching G) (f : Port V) (harm : F G f = f) :
    ∃ c, ∀ s, f s = c := by
  obtain ⟨i,join⟩ := common G hb
  obtain ⟨lo,_,low⟩ := exists_min_image univ f ⟨(i,i),mem_univ _⟩
  obtain ⟨hi,_,high⟩ := exists_max_image univ f ⟨(i,i),mem_univ _⟩
  have prop (g : Port V) (t : V×V) (he : F G g = g) (minim : ∀ s, g t ≤ g s) :
      ∀ x ∈ nbNext G t, g x=g t := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    have eq := congrFun he t
    change (∑ j ∈ allowed G t,g (j,t.1))/(allowed G t).card = g t at eq
    have den : ((allowed G t).card:ℝ) ≠ 0 := by exact_mod_cast (allowed_pos G t).card_pos.ne'
    have z : ∑ j ∈ allowed G t,(g (j,t.1)-g t) = 0 := by
      rw [sum_sub_distrib,sum_const,nsmul_eq_mul,(div_eq_iff den).mp eq,mul_comm]; ring
    exact sub_eq_zero.mp ((sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (minim _))).mp z v hv)
  have att (g : Port V) (t : V×V) (he : F G g = g) (mn : ∀ s, g t ≤ g s) :
      ∃ j, g (i,j)=g t := by
    obtain ⟨⟨v,j⟩,p,rfl⟩ := nbReach G i t
    refine ⟨j,?_⟩
    have go {r : V×V} (path : Relation.ReflTransGen (fun x y => y ∈ nbNext G x) t r) : g r=g t := by
      induction path with
      | refl => rfl
      | tail _ step ih => exact (prop g _ he (fun s => ih ▸ mn s) _ step).trans ih
    exact go p
  have mn (s) := low s (mem_univ s)
  have mx (s) := high s (mem_univ s)
  have negH : F G (-f) = -f := by rw [map_neg,harm]
  have negMin (s : V×V) : (-f) hi ≤ (-f) s := neg_le_neg (mx s)
  obtain ⟨j,ej⟩ := att f lo harm mn
  obtain ⟨k,ek⟩ := att (-f) hi negH negMin
  obtain ⟨v,hv,hj,hk⟩ := join j k
  have nxt (r : V) (hr : v≠r) : (v,i) ∈ nbNext G (i,r) := by
    apply mem_image.mpr; refine ⟨v,?_,rfl⟩
    unfold allowed; split <;> simp [hr,hv]
  have low' := prop f (i,j) harm (fun s => ej ▸ mn s) _ (nxt j hj)
  have high' := prop (-f) (i,k) negH (fun s => ek ▸ negMin s) _ (nxt k hk)
  simp only [Pi.neg_apply] at high' ek
  exact ⟨f lo,fun s => by linarith only [low',high',ej,ek,mn s,mx s]⟩
theorem invertible (hd : Mindeg G) (hb : Branching G) : Function.Bijective (system G) := by
  obtain ⟨a,ha⟩ := hb
  have inject : Function.Injective (system G) := by
    apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
    intro f hf
    have eq (s) := congrFun hf s
    have form (s) : f s-F G f s+mass G f=0 := eq s
    have z := congrArg (tot G) (funext form)
    have lin : tot G (fun s => f s-F G f s+mass G f) =
        tot G f-tot G (F G f)+tot G (fun _ => mass G f) := by simp [tot,es,sum_add_distrib,sum_sub_distrib]
    rw [lin,invariant G hd,sub_self,zero_add,tot_const,tot_const,mul_zero] at z
    have mf := (mul_eq_zero.mp z).resolve_left (vol_pos G a).ne'
    have harm : F G f=f := funext fun s => by linarith only [form s,mf]
    obtain ⟨c,hc⟩ := harmonic_const G ⟨a,ha⟩ f harm
    have fc := funext hc
    rw [fc] at mf ⊢
    simp only [mass,tot_const,mul_div_cancel_left₀ _ (vol_pos G a).ne'] at mf
    ext; simp [mf]
  exact ⟨inject,LinearMap.injective_iff_surjective.mp inject⟩
def Z (hd : Mindeg G) (hb : Branching G) : Port V →ₗ[ℝ] Port V :=
  (LinearEquiv.ofBijective (system G) (invertible G hd hb)).symm.toLinearMap
theorem fundamental_eq (hd : Mindeg G) (hb : Branching G) (f : Port V) :
    system G (Z G hd hb f) = f := (LinearEquiv.ofBijective _ (invertible G hd hb)).apply_symm_apply f
#print axioms fundamental_eq
end
end Fundamental
