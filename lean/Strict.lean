import Kemeny
namespace Kemeny
open Finset Stationary Fundamental Walks Gap
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : Graph V)
def ordinaryK := ∑ a, piV G a*avg G (h G a)
lemma all_stars : (∀ a, ∀ i ∈ G.N a, G.N i={a}) ↔ Fintype.card V=2 := by
  let v := Classical.arbitrary V
  obtain ⟨w,hw⟩ := G.nonempty v
  have ne : v≠w := by intro e; exact G.loopless v (e ▸ hw)
  have pairCard : ({v,w}:Finset V).card=2 := by simp [ne]
  constructor
  · intro H
    have atw := H v w hw
    have atv := H w v (G.symm.mp hw)
    have covered (k : V) : k ∈ ({v,w}:Finset V) := by
      induction G.connected v k with
      | refl => simp
      | tail _ step ih =>
        rcases mem_insert.mp ih with eq|eq
        · rw [eq,atv,mem_singleton] at step; simp [step]
        · rw [mem_singleton] at eq; rw [eq,atw,mem_singleton] at step; simp [step]
    have u : (univ:Finset V)={v,w} := Subset.antisymm (fun j _ => covered j) (subset_univ _)
    simpa [←u] using pairCard
  · intro n a i hi
    have sub : G.N i ⊆ (univ:Finset V).erase i := fun j hj =>
      mem_erase.mpr ⟨fun e => G.loopless i (e ▸ hj),mem_univ _⟩
    have small := card_le_card sub
    simp [n] at small
    have ha := G.symm.mp hi
    exact eq_singleton_iff_unique_mem.mpr ⟨ha,fun k hk => card_le_one.mp small k hk a ha⟩
theorem double_average : hit G ≤ ordinaryK G ∧
    (hit G=ordinaryK G ↔ Fintype.card V=2) := by
  let n := fun a => avg G (hitBar G a)
  let s := fun a => avg G (h G a)
  have pos (a : V) : 0≤piV G a*(s a-n a) := mul_nonneg (pi_pos G a).le
    (sub_nonneg.mpr (fixed_target_comparison G a).1)
  have eq : ordinaryK G-hit G = ∑ a,piV G a*(s a-n a) := by simp [ordinaryK,hit,n,s,mul_sub,sum_sub_distrib]
  have pp := sum_nonneg (s:=univ) fun j _ => pos j
  refine ⟨by linarith,?_⟩
  rw [←all_stars G]
  constructor
  · intro same a
    have z := (sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ univ) => pos j)).mp (by linarith only [eq,same]) a (mem_univ a)
    apply (fixed_target_comparison G a).2.mp
    exact (sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left (pi_pos G a).ne')).symm
  · intro star
    have z : ∑ a,piV G a*(s a-n a)=0 := sum_eq_zero fun a _ => by
      have ha : n a=s a := (fixed_target_comparison G a).2.mpr (star a)
      rw [ha,sub_self,mul_zero]
    linarith
#print axioms double_average
end
end Kemeny
