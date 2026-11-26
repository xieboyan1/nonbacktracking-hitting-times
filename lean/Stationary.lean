import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Stationary
set_option linter.unusedSectionVars false
open Finset
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

structure Graph (V : Type*) [Fintype V] where
  N : V → Finset V
  symm : ∀ {i j}, j ∈ N i ↔ i ∈ N j
  loopless : ∀ i, i ∉ N i
  nonempty : ∀ i, (N i).Nonempty
  connected : ∀ i j, Relation.ReflTransGen (fun x y => y ∈ N x) i j

variable (G : Graph V)
def deg (i : V) : ℝ := (G.N i).card
def es (f : V → V → ℝ) := ∑ i, ∑ j ∈ G.N i, f i j
def vol := ∑ i, deg G i
def avg (f : V → ℝ) := es G (fun i _ => f i) / vol G

lemma vol_pos (a : V) : 0 < vol G := by
  apply lt_of_lt_of_le (b := deg G a)
  · unfold deg; exact_mod_cast (G.nonempty a).card_pos
  · exact single_le_sum (fun i _ => Nat.cast_nonneg (G.N i).card) (mem_univ a)

lemma flip (f : V → V → ℝ) : es G (fun i j => f j i) = es G f := by
  classical
  have exp (g : V → V → ℝ) : es G g = ∑ i, ∑ j, if j ∈ G.N i then g i j else 0 := by
    simp [es, ← Finset.sum_filter]
  rw [exp, Finset.sum_comm, exp]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
    by_cases hj : j ∈ G.N i
    · simp [hj, G.symm.mp hj]
    · simp [hj, mt G.symm.mpr hj]

-- h is the SRW mean; u is the fresh NB mean; v_ij=w_ij-u_i.
structure Rows (G : Graph V) (a : V) (h u : V → ℝ) (v : V → V → ℝ) : Prop where
  ha : h a = 0
  ua : u a = 0
  va : ∀ j ∈ G.N a, v a j = 0
  pos : ∀ i, i ≠ a → 0 < h i
  center : ∀ i, ∑ j ∈ G.N i, v i j = 0
  sr : ∀ i, i ≠ a → ∑ j ∈ G.N i, (h i - h j - 1) = 0
  nb : ∀ i, i ≠ a → ∑ j ∈ G.N i, (u i - u j - v j i - 1) = 0
  port : ∀ i, i ≠ a → ∀ j ∈ G.N i, (deg G i-1)*v i j + u j + v j i - u i + 1 = 0

variable {G} {a : V} {h u : V → ℝ} {v : V → V → ℝ}
def energy (G : Graph V) (h u : V → ℝ) (v : V → V → ℝ) (i j : V) :=
  ((h i-u i)-(h j-u j))^2/2 + (deg G i-2)*(v i j)^2 + (v i j+v j i)^2/2

private def residual (G : Graph V) (h u : V → ℝ) (v : V → V → ℝ) (i j : V) :=
  (h i-2*u i)*(h i-h j-1) + u i*(u i-u j-v j i-1) + (u i-1)*v i j +
  v i j*((deg G i-1)*v i j+u j+v j i-u i+1)

lemma identity (H : Rows G a h u v) :
    es G (energy G h u v) = es G (fun i _ => h i) - es G (fun i _ => u i) := by
  let F := residual G h u v
  let E := energy G h u v
  have zero : es G F = 0 := by
    apply sum_eq_zero
    intro i _
    unfold F residual
    simp only [sum_add_distrib, ← Finset.mul_sum]
    have last : ∑ j ∈ G.N i, v i j*((deg G i-1)*v i j+u j+v j i-u i+1) = 0 := by
      apply sum_eq_zero; intro j hj
      by_cases hi : i = a
      · subst i; simp [H.va j hj]
      · simp [H.port i hi j hj]
    rw [H.center, last]
    by_cases hi : i = a
    · subst i; simp [H.ha, H.ua]
    · simp [H.sr i hi, H.nb i hi]
  have localEq (i j : V) : F i j + F j i =
      E i j + E j i - h i - h j + u i + u j := by unfold F E residual energy; ring
  have eq := congrArg (es G) (funext fun i => funext fun j => localEq i j)
  have ff := flip G F
  have fe := flip G E
  have fh := flip G (fun i _ => h i)
  have fu := flip G (fun i _ => u i)
  change es G E = _
  simp only [es, sum_add_distrib, sum_sub_distrib] at eq ff fe fh fu zero ⊢
  linarith

lemma singleV (H : Rows G a h u v) (i j : V) (hj : j ∈ G.N i) (hd : (G.N i).card ≤ 1) :
    v i j = 0 := by
  have hs := eq_singleton_iff_unique_mem.mpr ⟨hj, fun k hk => card_le_one.mp hd k hk j hj⟩
  simpa [hs] using H.center i

lemma middle_pos (H : Rows G a h u v) (i j : V) (hj : j ∈ G.N i) :
    0 ≤ (deg G i-2)*(v i j)^2 := by
  by_cases hd : (G.N i).card ≤ 1
  · simp [singleV H i j hj hd]
  · have hd' : (2 : ℝ) ≤ deg G i := by unfold deg; exact_mod_cast (by omega : 2 ≤ (G.N i).card)
    exact mul_nonneg (by linarith) (sq_nonneg _)

lemma energy_pos (H : Rows G a h u v) (i j : V) (hj : j ∈ G.N i) : 0 ≤ energy G h u v i j := by
  unfold energy; linarith [middle_pos H i j hj, sq_nonneg ((h i-u i)-(h j-u j)), sq_nonneg (v i j+v j i)]

theorem comparison (H : Rows G a h u v) : avg G u ≤ avg G h := by
  have hp : 0 ≤ es G (energy G h u v) :=
    sum_nonneg fun i _ => sum_nonneg fun j hj => energy_pos H i j hj
  rw [identity H] at hp
  exact div_le_div_of_nonneg_right (by linarith) (vol_pos G a).le

theorem equality_iff (H : Rows G a h u v) :
    avg G u = avg G h ↔ ∀ i ∈ G.N a, G.N i = {a} := by
  constructor
  · intro he
    have mass := (div_left_inj' (vol_pos G a).ne').mp he
    have z : es G (energy G h u v) = 0 := by rw [identity H, mass, sub_self]
    have point (i j : V) (hj : j ∈ G.N i) : energy G h u v i j = 0 := by
      have rz := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ univ) =>
        sum_nonneg fun j hj => energy_pos H i j hj)).mp z i (mem_univ i)
      exact (sum_eq_zero_iff_of_nonneg (fun j hj => energy_pos H i j hj)).mp rz j hj
    have parts (i j : V) (hj : j ∈ G.N i) :
        h i-u i = h j-u j ∧ v i j+v j i = 0 ∧ (deg G i-2)*v i j=0 := by
      have ze := point i j hj
      unfold energy at ze
      have m := middle_pos H i j hj
      have sq₁ := sq_nonneg ((h i-u i)-(h j-u j))
      have sq₂ := sq_nonneg (v i j+v j i)
      have zm : (deg G i-2)*(v i j)^2=0 := by linarith
      have zs : ((h i-u i)-(h j-u j))^2=0 := by linarith
      have zt : (v i j+v j i)^2=0 := by linarith
      refine ⟨by nlinarith, by nlinarith, ?_⟩
      rcases mul_eq_zero.mp zm with hz|hz
      · simp [hz]
      · have : v i j = 0 := by nlinarith
        simp [this]
    intro i hi
    have ia := G.symm.mp hi
    have ni : i ≠ a := fun hi' => G.loopless a (hi' ▸ hi)
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨ia, fun k hk => ?_⟩
    by_contra hka
    have same (j : V) (hj : j ∈ G.N i) : u j = u i-1 := by
      have p := parts i j hj
      linarith [H.port i ni j hj, p.2.1, p.2.2]
    have p := (parts i k hk).1
    have q := (parts i a ia).1
    linarith [same k hk, same a ia, H.ha, H.pos k hka]
  · intro star
    have reach (i : V) : i=a ∨ i ∈ G.N a := by
      induction G.connected a i with
      | refl => exact Or.inl rfl
      | tail _ step ih =>
        rcases ih with rfl|h
        · exact Or.inr step
        · rw [star _ h, mem_singleton] at step; exact Or.inl step
    have equal (i : V) : u i = h i := by
      rcases reach i with rfl|hi
      · rw [H.ua, H.ha]
      · have ni : i ≠ a := fun hh => G.loopless a (hh ▸ hi)
        have sr := H.sr i ni
        have nb := H.nb i ni
        simp [star i hi, H.ha, H.ua, H.va i hi] at sr nb
        linarith
    rw [funext equal]

-- Uncentred first-step equations. w i j is the remaining time at i after
-- arrival from j. At degree one the next step is forced. All values at the
-- target vanish. h is the ordinary-walk table.
structure Bellman (G : Graph V) (a : V) (h : V → ℝ) (w : V → V → ℝ) : Prop where
  target : h a = 0
  stopped : ∀ j ∈ G.N a, w a j = 0
  nonneg : ∀ i, 0 ≤ h i
  ordinary : ∀ i, i ≠ a → deg G i * (h i-1) = ∑ j ∈ G.N i, h j
  remembered : ∀ i, i ≠ a → ∀ j ∈ G.N i,
    if (G.N i).card = 1 then w i j = 1 + w j i else
    (deg G i-1)*(w i j-1) = ∑ k ∈ (G.N i).erase j, w k i

def fresh (G : Graph V) (a : V) (w : V → V → ℝ) (i : V) : ℝ :=
  if i=a then 0 else 1 + (∑ j ∈ G.N i, w j i) / deg G i

theorem from_bellman {w : V → V → ℝ} (H : Bellman G a h w) :
    Rows G a h (fresh G a w) (fun i j => w i j - fresh G a w i) := by
  let u := fresh G a w
  have dp (i : V) : 0 < deg G i := by unfold deg; exact_mod_cast (G.nonempty i).card_pos
  have freshEq (i : V) (hi : i ≠ a) : deg G i*(u i-1) = ∑ j ∈ G.N i, w j i := by
    simp [u, fresh, hi, mul_div_cancel₀, mul_comm (deg G i), (dp i).ne']
  have portEq (i : V) (hi : i ≠ a) (j : V) (hj : j ∈ G.N i) :
      (deg G i-1)*(w i j-u i) + w j i-u i+1=0 := by
    have r := H.remembered i hi j hj
    have f := freshEq i hi
    by_cases hd : (G.N i).card = 1
    · have sn := eq_singleton_iff_unique_mem.mpr ⟨hj, fun k hk => card_le_one.mp hd.le k hk j hj⟩
      have d : deg G i = 1 := by simp [deg, hd]
      rw [d, sn] at f
      simp at f
      rw [d]; linarith
    · simp [hd] at r
      have e := sum_erase_add (G.N i) (fun k => w k i) hj
      nlinarith only [e, r, f]
  refine ⟨H.target, by simp [fresh], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simp [fresh, H.stopped j hj]
  · intro i hi
    have sr := H.ordinary i hi
    have pos := sum_nonneg (s := G.N i) fun j _ => H.nonneg j
    by_cases bad : h i ≤ 0
    · nlinarith only [pos, sr, mul_nonpos_of_nonneg_of_nonpos (dp i).le bad, dp i]
    · exact lt_of_not_ge bad
  · intro i
    change ∑ j ∈ G.N i, (w i j-u i) = 0
    by_cases hi : i=a
    · subst i; apply sum_eq_zero; intro j hj; simp [u, fresh, H.stopped j hj]
    by_cases hd : (G.N i).card = 1
    · obtain ⟨j, hj⟩ := G.nonempty i
      have sn := eq_singleton_iff_unique_mem.mpr ⟨hj, fun k hk => card_le_one.mp hd.le k hk j hj⟩
      have r := H.remembered i hi j hj
      simp [hd] at r
      simp [u, fresh, hi, sn, deg, r]
    · have e : ∑ j ∈ G.N i, ((deg G i-1)*(w i j-u i) + w j i-u i+1) = 0 :=
        sum_eq_zero fun j hj => portEq i hi j hj
      simp only [sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum, sum_const, nsmul_eq_mul] at e
      change (deg G i-1)*_ + _ - deg G i*u i + deg G i*1 = 0 at e
      have z : (deg G i-1)*(∑ j ∈ G.N i, (w i j-u i))=0 := by
        simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
        unfold deg at *
        nlinarith only [e, freshEq i hi]
      apply (mul_eq_zero.mp z).resolve_left
      intro hh
      apply hd
      have dd : deg G i = 1 := by linarith
      unfold deg at dd
      exact_mod_cast dd
  · intro i hi
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
    have r := H.ordinary i hi
    unfold deg at r
    linarith
  · intro i hi
    change ∑ j ∈ G.N i, (u i - u j - (w j i-u j)-1) = 0
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
    have r := freshEq i hi
    unfold deg at r
    linarith
  · intro i hi j hj
    change (deg G i-1)*(w i j-u i)+u j+(w j i-u j)-u i+1=0
    linarith only [portEq i hi j hj]

theorem fixed_target {w : V → V → ℝ} (H : Bellman G a h w) :
    avg G (fresh G a w) ≤ avg G h ∧
    (avg G (fresh G a w) = avg G h ↔ ∀ i ∈ G.N a, G.N i = {a}) :=
  ⟨comparison (from_bellman H), equality_iff (from_bellman H)⟩
#print axioms fixed_target
#print axioms comparison
#print axioms equality_iff
end
end Stationary
