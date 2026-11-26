import Gap
import Corridors
namespace Bounds
set_option linter.unusedSectionVars false
open Finset Stationary Fundamental Gap Corridors
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {G : Graph V} {a : V} (d : Data G a)
def s (i j : V) := (d.eta i j + t d i j)/2
def c (i j : V) := (d.eta i j - t d i j)/2
def localEnergy (i j : V) := (deg G i-2)*(d.eta i j)^2+2*(s d i j)^2
def energy := es G (localEnergy d)
def normSq (G : Graph V) (f : V → V → ℝ) := es G (fun i j => (f i j)^2)
lemma eq_es {f g : V → V → ℝ} (p : ∀ i, ∀ j ∈ G.N i,f i j=g i j) : es G f=es G g :=
  sum_congr rfl fun i _ => sum_congr rfl fun j hj => p i j hj
lemma le_es {f g : V → V → ℝ} (p : ∀ i, ∀ j ∈ G.N i,f i j≤g i j) : es G f≤es G g :=
  sum_le_sum fun i _ => sum_le_sum fun j hj => p i j hj
lemma integral (f g : V → V → ℝ) (k l : ℝ) :
    es G (fun i j => k*f i j+l*g i j)=k*es G f+l*es G g := by simp [es,sum_add_distrib,←mul_sum]
lemma scaled (f : V → V → ℝ) (k : ℝ) : es G (fun i j => k*f i j)=k*es G f := by simp [es,←mul_sum]
lemma source (i j : V) (hj : j ∈ G.N i) : d.e i j = (deg G i-2)*d.eta i j+2*s d i j := by
  rw [d.source i j hj]; unfold s t; ring
lemma product : es G (fun i j => d.eta i j*d.e i j) = energy d := by
  have eq : es G (fun i j => 4*(d.eta i j*d.e i j)-4*localEnergy d i j) =
      es G (fun i j => 2*(d.eta i j)^2-2*(t d i j)^2) := by
    apply eq_es; intro i j hj; rw [source d i j hj]; unfold localEnergy s; ring
  simp only [es,sum_sub_distrib,←mul_sum] at eq
  have iso := isometry d
  unfold es at iso
  unfold energy es; linarith only [eq,iso]
lemma dmin (hd : Mindeg G) (i : V) : 2 ≤ deg G i := by unfold deg; exact_mod_cast hd i
lemma ep (hd : Mindeg G) (i j : V) : 0 ≤ localEnergy d i j :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr (dmin hd i)) (sq_nonneg _)) (by positivity)
lemma gap_pos (hd : Mindeg G) : 0 ≤ energy d :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => ep d hd i j
theorem lower (hd : Mindeg G) (D : ℝ) (hD : ∀ i,deg G i≤D) :
    normSq G d.e ≤ D * energy d := by
  rw [energy,←scaled]
  apply le_es; intro i j hj
  have up := mul_le_mul_of_nonneg_right (hD i) (ep d hd i j)
  apply le_trans _ up
  rw [source d i j hj]; unfold localEnergy
  nlinarith only [mul_nonneg (sub_nonneg.mpr (dmin hd i)) (sq_nonneg (d.eta i j-s d i j))]
lemma square (k : ℝ) : 2*k*energy d - k^2*normSq G d.eta ≤ normSq G d.e := by
  rw [←product]; unfold normSq
  have e := le_es (G:=G) (f:=fun i j => 2*k*(d.eta i j*d.e i j)-k^2*(d.eta i j)^2)
    (g:=fun i j => (d.e i j)^2) (fun i j _ => by dsimp only; nlinarith only [sq_nonneg (d.e i j-k*d.eta i j)])
  simpa only [es,sum_sub_distrib,←mul_sum] using e
theorem upper_min (D : ℝ) (lo : 2<D) (hd : ∀ i,D ≤ deg G i) :
    (D-2)*energy d ≤ normSq G d.e := by
  have h : (D-2)*normSq G d.eta ≤ energy d := by
    unfold normSq energy; rw [←scaled]; apply le_es; intro i j _
    unfold localEnergy
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hd i)) (sq_nonneg (d.eta i j)),sq_nonneg (s d i j)]
  nlinarith only [square d (D-2),mul_le_mul_of_nonneg_left h (sub_nonneg.mpr lo.le)]
lemma decompose : normSq G d.eta = normSq G (c d)+normSq G (s d) := by
  have e : es G (fun i j => 2*(c d i j)^2+2*(s d i j)^2) =
      es G (fun i j => (d.eta i j)^2+(t d i j)^2) := by
    apply eq_es; intro i j _; unfold c s; ring
  have iso := isometry d
  simp only [es,sum_add_distrib,←mul_sum] at e iso
  unfold normSq es; linarith
theorem upper_chain (hd : Mindeg G) (hb : Branching G) :
    energy d ≤ 2*(lengthBound G hd hb : ℝ)*normSq G d.e := by
  let L : ℝ := lengthBound G hd hb
  have l : 1≤L := by dsimp [L,lengthBound]; exact_mod_cast (Nat.le_add_right 1 _)
  have high := chain_norm G hd hb (c d) (fun i j => by unfold c t; ring)
    (fun i => by simp only [c,div_eq_mul_inv,←sum_mul,sum_sub_distrib,d.cent,centerT,sub_self,zero_mul])
  let H := es G (fun i j => if 3≤(G.N i).card then (d.eta i j)^2 else 0)
  have ch : es G (fun i j => if 3≤(G.N i).card then (c d i j)^2 else 0) ≤
      2*H+2*normSq G (s d) := by
    unfold H normSq; rw [←integral]; apply le_es
    intro i j _; split
    · have eq : c d i j=d.eta i j-s d i j := by unfold c s; ring
      rw [eq]; nlinarith only [sq_nonneg (d.eta i j+s d i j)]
    · simp only [*,if_false,mul_zero,zero_add]; positivity
  have big : H+2*normSq G (s d) ≤ energy d := by
    unfold H normSq energy
    rw [←one_mul (es G _),←integral]; apply le_es
    intro i j _; unfold localEnergy; split
    · rename_i h; have bound : 3 ≤ deg G i := by unfold deg; exact_mod_cast h
      nlinarith only [mul_nonneg (sub_nonneg.mpr bound) (sq_nonneg (d.eta i j))]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr (dmin hd i)) (sq_nonneg (d.eta i j))]
  have sn : 0 ≤ normSq G (s d) := sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have coercive : normSq G d.eta ≤ 2*L*energy d := by
    change normSq G (c d) ≤ L*_ at high
    rw [decompose d]
    nlinarith only [high,mul_le_mul_of_nonneg_left ch (by linarith : 0≤L),
      mul_le_mul_of_nonneg_left big (by linarith : 0≤2*L),mul_nonneg (by linarith : 0≤2*L-1) sn]
  let k := (2*L)⁻¹
  have kpos : 0<k := inv_pos.mpr (by linarith)
  have inv : k*(2*L)=1 := inv_mul_cancel₀ (by linarith)
  have sm : k*normSq G d.eta ≤ energy d := by
    have p := mul_le_mul_of_nonneg_left coercive kpos.le
    rwa [←mul_assoc,inv,one_mul] at p
  have e : k*energy d ≤ normSq G d.e := by nlinarith only [square d k,mul_le_mul_of_nonneg_left sm kpos.le]
  have out := mul_le_mul_of_nonneg_left e (by linarith : 0 ≤ 2*L)
  rwa [←mul_assoc,mul_comm (2*L) k,inv,one_mul] at out
end
end Bounds
