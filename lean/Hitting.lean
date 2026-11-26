import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
namespace Hitting
set_option linter.unusedSectionVars false
open Finset Filter
open scoped Topology
noncomputable section
variable {S : Type*} [Fintype S] [DecidableEq S]
structure Chain (S : Type*) where
  N : S → Finset S
  pos : ∀ x, (N x).Nonempty
  stop : S → Bool
  escape : ∀ x, ∃ y, Relation.ReflTransGen (fun i j => j ∈ N i) x y ∧ stop y = true

variable (C : Chain S)
def K : (S → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun f x := if C.stop x then 0 else (∑ j ∈ C.N x, f j) / (C.N x).card
  map_add' f g := by ext x; dsimp; split <;> simp [sum_add_distrib,add_div]
  map_smul' c f := by ext x; dsimp; split <;> simp [← mul_sum, mul_div_assoc]
def alive (x : S) : ℝ := if C.stop x then 0 else 1
def M : (S → ℝ) →ₗ[ℝ] (S → ℝ) := LinearMap.id - K C
lemma degree_pos (x : S) : 0 < ((C.N x).card : ℝ) := by exact_mod_cast (C.pos x).card_pos

lemma maximum_principle {f : S → ℝ} (hm : ∀ i, 0 ≤ M C f i) : ∀ x, 0 ≤ f x := by
  intro x
  obtain ⟨z, _, least⟩ := exists_min_image univ f ⟨x, mem_univ _⟩
  have low (i : S) := least i (mem_univ i)
  by_contra! hneg
  have neg : f z < 0 := lt_of_le_of_lt (low x) hneg
  have away (i : S) (hi : f i = f z) : C.stop i = false := by
    cases hh : C.stop i with
    | false => rfl
    | true =>
      have p := hm i
      change 0 ≤ f i - (if C.stop i then 0 else _) at p
      simp [hh, hi] at p
      linarith
  have propagate (i : S) (hi : f i = f z) (j : S) (hj : j ∈ C.N i) : f j = f z := by
    have p := hm i
    change 0 ≤ f i - (if C.stop i then 0 else _) at p
    simp only [away i hi, Bool.false_eq_true, if_false, hi] at p
    have le := (div_le_iff₀ (degree_pos C i)).mp (sub_nonneg.mp p)
    have ze : ∑ k ∈ C.N i, (f k-f z) = 0 := by
      apply le_antisymm _ (sum_nonneg (fun k _ => sub_nonneg.mpr (low k)))
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
      linarith [mul_comm (f z) ((C.N i).card : ℝ)]
    exact sub_eq_zero.mp ((sum_eq_zero_iff_of_nonneg (fun k _ => sub_nonneg.mpr (low k))).mp ze j hj)
  obtain ⟨y,path,hy⟩ := C.escape z
  have val : f y = f z := by
    clear hy
    induction path with
    | refl => rfl
    | tail _ hj ih => exact propagate _ ih _ hj
  exact Bool.noConfusion (hy.symm.trans (away y val))

lemma unique_solution : Function.Injective (M C) := by
  apply (LinearMap.ker_eq_bot.mp ?_)
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  ext i
  have pos := maximum_principle C (f:=f) (by intro j; rw [hf]; rfl) i
  have neg := maximum_principle C (f:=-f) (by intro j; rw [map_neg, hf, neg_zero]; rfl) i
  change 0 ≤ -f i at neg
  change f i = 0
  linarith

def green : S → ℝ := Classical.choose
  (LinearMap.injective_iff_surjective.mp (unique_solution C) (alive C))
lemma equation : M C (green C) = alive C := Classical.choose_spec
  (LinearMap.injective_iff_surjective.mp (unique_solution C) (alive C))
lemma green_nonneg : ∀ i, 0 ≤ green C i := maximum_principle C (fun i => by
  rw [equation]; unfold alive; split <;> norm_num)
lemma first (i : S) : green C i = alive C i + K C (green C) i := by
  have hh := congrFun (equation C) i
  change green C i - K C (green C) i = alive C i at hh; linarith
def survival (n : ℕ) := ((K C)^[n]) (alive C)
def remainder (n : ℕ) := ((K C)^[n]) (green C)
def HasMean (x : S) (m : ℝ) :=
  Tendsto (fun n => ∑ k ∈ range n, survival C k x) atTop (𝓝 m)
lemma monoK {f g : S → ℝ} (p : ∀ x, f x ≤ g x) (i : S) : K C f i ≤ K C g i := by
  change (if C.stop i then 0 else _) ≤ (if C.stop i then 0 else _)
  split
  · rfl
  · exact div_le_div_of_nonneg_right (sum_le_sum fun j _ => p j) (degree_pos C i).le
theorem green_mean (x : S) : HasMean C x (green C x) := by
  let B := 1 + ∑ i, green C i
  have one : 1 ≤ B := by dsimp [B]; linarith [sum_nonneg (s:=univ) fun i _ => green_nonneg C i]
  have bp : 0 < B := by linarith
  have bound (i : S) : green C i ≤ B := by
    have := single_le_sum (fun j (_ : j ∈ univ) => green_nonneg C j) (mem_univ i)
    dsimp [B]; linarith
  let r := 1 - 1/B
  have r0 : 0 ≤ r := by dsimp [r]; exact sub_nonneg.mpr ((div_le_iff₀ bp).mpr (by linarith))
  have r1 : r < 1 := by dsimp [r]; linarith [one_div_pos.mpr bp]
  have dec (i : S) : K C (green C) i ≤ r * green C i := by
    have f := first C i
    cases hi : C.stop i with
    | true => change (if C.stop i then 0 else _) ≤ _; simpa [hi] using mul_nonneg r0 (green_nonneg C i)
    | false =>
      simp [alive, hi] at f
      have t := (div_le_one bp).mpr (bound i)
      dsimp [r]; rw [sub_mul,one_mul,one_div_mul_eq_div]; linarith
  have est (n : ℕ) : ∀ i, 0 ≤ remainder C n i ∧ remainder C n i ≤ r^n * green C i := by
    induction n with
    | zero => intro i; simp [remainder,green_nonneg]
    | succ n ih =>
      intro i
      have l := monoK C (f:=0) (fun j => (ih j).1) i
      have u := monoK C (g:=(r^n) • green C) (fun j => (ih j).2) i
      rw [map_zero] at l
      rw [map_smul] at u
      change K C (remainder C n) i ≤ r^n * K C (green C) i at u
      simpa only [remainder, Function.iterate_succ_apply',pow_succ,mul_assoc] using
        And.intro l (u.trans (mul_le_mul_of_nonneg_left (dec i) (pow_nonneg r0 n)))
  have telesc (n : ℕ) : survival C n = remainder C n - remainder C (n+1) := by
    induction n with
    | zero => ext i; change alive C i = green C i-K C (green C) i; linarith [first C i]
    | succ n ih =>
      simpa only [survival,remainder,Function.iterate_succ_apply',map_sub] using congrArg (K C) ih
  have part (n : ℕ) : ∑ k ∈ range n, survival C k x = green C x-remainder C n x := by
    induction n with
    | zero => simp [remainder]
    | succ n ih => rw [sum_range_succ,ih,telesc,Pi.sub_apply]; ring
  have lim : Tendsto (fun n => remainder C n x) atTop (𝓝 0) := squeeze_zero
    (fun n => (est n x).1) (fun n => (est n x).2)
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one r0 r1).mul_const (green C x))
  unfold HasMean; simp_rw [part]; simpa using (tendsto_const_nhds (x:=green C x)).sub lim
end
end Hitting
