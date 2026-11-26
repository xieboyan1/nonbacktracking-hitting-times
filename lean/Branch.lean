import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
namespace Branch
open Filter
open scoped Topology
noncomputable section
inductive Row (S : Type*) where
  | hit | one (x : S) | two (x y : S) | three (x y z : S)
variable {S : Type*}
def Row.apply (f : S → ℝ) : Row S → ℝ
  | .hit => 0 | .one x => f x | .two x y => (f x+f y)/2 | .three x y z => (f x+f y+f z)/3
def Row.cost : Row S → ℝ | .hit => 0 | _ => 1
variable (R : S → Row S)
def trunc : ℕ → S → ℝ
  | 0 => fun _ => 0
  | n+1 => fun s => (R s).cost + (R s).apply (trunc n)
-- trunc n is the expected number of steps made before stopping or time n.
lemma mono {f g : S → ℝ} (H : ∀ s, f s ≤ g s) (t : Row S) : t.apply f ≤ t.apply g := by
  cases t <;> simp only [Row.apply] <;> first | rfl | apply H | (gcongr <;> apply H)
lemma lin (f : S → ℝ) (c : ℝ) (t : Row S) : t.apply (fun i => c*f i) = c*t.apply f := by
  cases t <;> simp [Row.apply] <;> ring
theorem certificate [Fintype S] (f : S → ℝ) (pos : ∀ s, 0 ≤ f s)
    (eqn : ∀ s, f s = (R s).cost + (R s).apply f) (s : S) :
    Tendsto (fun n => trunc R n s) atTop (𝓝 (f s)) := by
  let B := 1+∑ i, f i
  have one : 1≤B := by dsimp [B]; linarith [Finset.sum_nonneg (s:=Finset.univ) fun i _ => pos i]
  have bp : 0<B := by linarith
  have bound (i : S) : f i ≤ B := by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => pos j) (Finset.mem_univ i)
    dsimp [B]; linarith
  let r := 1-1/B
  have r0 : 0≤r := sub_nonneg.mpr ((div_le_iff₀ bp).mpr (by linarith))
  have r1 : r<1 := by dsimp [r]; linarith [one_div_pos.mpr bp]
  have dec (i : S) : (R i).apply f ≤ r*f i := by
    have e := eqn i
    have d := (div_le_one bp).mpr (bound i)
    dsimp [r]; rw [sub_mul,one_mul,one_div_mul_eq_div]
    cases hr : R i <;> rw [hr] at e <;> simp only [Row.cost,Row.apply] at e ⊢
    · simp at e; simp [e]
    all_goals linarith
  have est (n : ℕ) : ∀ i, (1-r^n)*f i ≤ trunc R n i ∧ trunc R n i ≤ f i := by
    induction n with
    | zero => intro i; simp [trunc,pos]
    | succ n ih =>
      intro i
      have lo := mono (fun i => (ih i).1) (R i)
      have up := mono (fun i => (ih i).2) (R i)
      rw [lin] at lo
      have step := mul_le_mul_of_nonneg_left (dec i) (pow_nonneg r0 n)
      simp only [trunc,pow_succ]
      constructor <;> nlinarith only [lo,up,step,eqn i]
  have zero : Tendsto (fun n => f s-trunc R n s) atTop (𝓝 0) := squeeze_zero (g:=fun n : ℕ => r^n*f s)
    (fun n => sub_nonneg.mpr (est n s).2) (fun n => by change f s-trunc R n s ≤ r^n*f s; nlinarith only [(est n s).1])
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one r0 r1).mul_const (f s))
  simpa using (tendsto_const_nhds (x:=f s)).sub zero
end
end Branch
