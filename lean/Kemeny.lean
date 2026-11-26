import GapData
import Bounds
namespace Kemeny
open Finset Stationary Walks Fundamental Gap Bounds Corridors
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : Graph V)
def hit := ∑ a, piV G a * avg G (hitBar G a)
-- Each diagonal block is averaged over the predecessor at vertex a.
def projected (hd : Mindeg G) (hb : Branching G) :=
  (∑ a,bar G (kernelCol G hd hb a) a)-1
def ret (a j : V) := 1+w G a j a
def retMean (a : V) := (∑ j ∈ G.N a,ret G a j)/deg G a
def variance (a : V) := (∑ j ∈ G.N a,(ret G a j-retMean G a)^2)/deg G a
def Vr := ∑ a,(piV G a)^2 * variance G a
def Delta : ℝ := (univ.sup fun i : V => (G.N i).card : ℕ)
lemma upperDegree (i : V) : deg G i ≤ Delta G := by
  unfold deg Delta; exact_mod_cast (le_sup (f:=fun i : V => (G.N i).card) (mem_univ i))
lemma pi_sum (hb : Branching G) : ∑ a,piV G a=1 := by
  obtain ⟨a,_⟩ := hb
  simp only [piV,div_eq_mul_inv,←sum_mul]
  change vol G*(vol G)⁻¹=1; exact mul_inv_cancel₀ (vol_pos G a).ne'
lemma return_center (a j : V) : err G a a j=ret G a j-retMean G a := by
  simp only [err,ret,retMean,if_pos rfl,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,
    meanIn,hitPort]
  change _ - _/deg G a = _ - (deg G a+_)/deg G a
  field_simp [(dp G a).ne']; ring
lemma source_norm (a : V) (hd : Mindeg G) (hb : Branching G) :
    normSq G (make G a hd hb).e = deg G a*variance G a := by
  change (∑ i,∑ j ∈ G.N i,(err G a i j)^2)=_
  rw [sum_eq_single a]
  · simp only [return_center,variance]
    rw [mul_comm,div_mul_cancel₀ _ (dp G a).ne']
  · intro i _ hi; simp [err,hi]
  · simp
def localGap (hd : Mindeg G) (hb : Branching G) (a : V) :=
  energy (make G a hd hb) / vol G
lemma local_identity (hd : Mindeg G) (hb : Branching G) (a : V) :
    localGap G hd hb a = avg G (hitBar G a) -
      (bar G (kernelCol G hd hb a) a/piV G a-1) := by
  rw [←solavg,localGap,←product,←gap_identity]
  change es G (fun i _ => hitBar G a i - bar G (sol G hd hb a) i)/vol G = _
  simp [avg,es,sum_sub_distrib,sub_div]
lemma gap_sum (hd : Mindeg G) (hb : Branching G) :
    hit G-projected G hd hb=∑ a,piV G a*localGap G hd hb a := by
  have p (a : V) : piV G a*localGap G hd hb a =
      piV G a*avg G (hitBar G a)-bar G (kernelCol G hd hb a) a+piV G a := by
    rw [local_identity]; field_simp [(pi_pos G a).ne']; ring
  simp [hit,projected,p,sum_add_distrib,sum_sub_distrib,pi_sum G hb]; ring
lemma vr_sum (hd : Mindeg G) (hb : Branching G) :
    Vr G=∑ a, piV G a*(normSq G (make G a hd hb).e/vol G) := by
  apply sum_congr rfl; intro a _
  rw [source_norm]; unfold piV; ring
theorem variance_bounds (hd : Mindeg G) (hb : Branching G) :
    Vr G/Delta G ≤ hit G-projected G hd hb ∧
    hit G-projected G hd hb ≤ 2*(lengthBound G hd hb:ℝ)*Vr G := by
  obtain ⟨a,ha⟩ := hb
  have br : Branching G := ⟨a,ha⟩
  have Dpos := lt_of_lt_of_le (dp G a) (upperDegree G a)
  rw [gap_sum,vr_sum G hd br,div_le_iff₀ Dpos,Finset.sum_mul,Finset.mul_sum]
  constructor
  · apply sum_le_sum; intro i _
    have h := lower (make G i hd br) hd (Delta G) (upperDegree G)
    have e := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (vol_pos G i).le) (pi_pos G i).le
    dsimp only [localGap]; convert e using 1; ring
  · apply sum_le_sum; intro i _
    have h := upper_chain (make G i hd br) hd br
    have e := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (vol_pos G i).le) (pi_pos G i).le
    dsimp only [localGap]; convert e using 1; ring
theorem min_degree_bound (hd : Mindeg G) (hb : Branching G) (δ : ℝ)
    (strong : 2<δ) (mind : ∀ i, δ ≤ deg G i) :
    hit G-projected G hd hb ≤ Vr G/(δ-2) := by
  rw [le_div_iff₀ (sub_pos.mpr strong),gap_sum,vr_sum G hd hb,Finset.sum_mul]
  apply sum_le_sum; intro i _
  have h := upper_min (make G i hd hb) δ strong mind
  have e := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (vol_pos G i).le) (pi_pos G i).le
  dsimp only [localGap]; convert e using 1; ring
lemma var_nonneg (a : V) : 0≤variance G a :=
  div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (dp G a).le
lemma var_zero (a : V) : variance G a=0 ↔ ∀ j ∈ G.N a, ∀ k ∈ G.N a,ret G a j=ret G a k := by
  constructor
  · intro h
    have z := (div_eq_zero_iff.mp h).resolve_right (dp G a).ne'
    have const (j : V) (hj : j ∈ G.N a) : ret G a j=retMean G a := by
      have e := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (ret G a j-retMean G a))).mp z j hj
      nlinarith
    intro j hj k hk; rw [const j hj,const k hk]
  · intro h
    obtain ⟨k,hk⟩ := G.nonempty a
    have e : retMean G a=ret G a k := by
      apply (div_eq_iff (dp G a).ne').mpr
      rw [sum_congr rfl (fun j hj => h j hj k hk),sum_const,nsmul_eq_mul,mul_comm]
      rfl
    unfold variance
    rw [sum_eq_zero (fun j hj => by rw [h j hj k hk,e,sub_self]; norm_num),zero_div]
theorem comparison_and_equality (hd : Mindeg G) (hb : Branching G) :
    projected G hd hb ≤ hit G ∧ (hit G=projected G hd hb ↔
      ∀ a, ∀ j ∈ G.N a, ∀ k ∈ G.N a,ret G a j=ret G a k) := by
  have le := variance_bounds G hd hb
  obtain ⟨a,ha⟩ := hb
  have dpos := lt_of_lt_of_le (dp G a) (upperDegree G a)
  have pos (i : V) : 0 ≤ (piV G i)^2*variance G i := mul_nonneg (sq_nonneg _) (var_nonneg G i)
  have vn : 0≤Vr G := sum_nonneg fun i _ => pos i
  have dif := (div_nonneg vn dpos.le).trans le.1
  refine ⟨by linarith,?_⟩
  constructor
  · intro eq i
    have lo := (div_le_iff₀ dpos).mp le.1
    rw [eq,sub_self,zero_mul] at lo
    have z := (sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ univ) => pos j)).mp (le_antisymm lo vn) i (mem_univ i)
    exact (var_zero G i).mp ((mul_eq_zero.mp z).resolve_left (pow_ne_zero _ (pi_pos G i).ne'))
  · intro uniform
    have z : Vr G=0 := sum_eq_zero fun i _ => by rw [(var_zero G i).mpr (uniform i),mul_zero]
    have up := le.2
    rw [z,mul_zero] at up; linarith
#print axioms variance_bounds
#print axioms min_degree_bound
#print axioms comparison_and_equality
end
end Kemeny
