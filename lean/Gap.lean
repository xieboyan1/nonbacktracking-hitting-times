import Fundamental
namespace Gap
open Finset Stationary Walks Fundamental
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : Graph V)
def piV (i : V) := deg G i / vol G
lemma pi_pos (a : V) : 0 < piV G a := div_pos (dp G a) (vol_pos G a)
def indicator (a : V) (s : V×V) : ℝ := if s.1=a then 1 else 0
def bias (a i : V) : ℝ := 1 - (if i=a then 1 else 0) / piV G a
def kernelCol (hd : Mindeg G) (hb : Branching G) (a : V) := Z G hd hb (indicator a)
def central (f : Port V) (i j : V) := f (i,j)-bar G f i
lemma sumBar (f : Port V) (i : V) : ∑ j ∈ G.N i,f (i,j) = deg G i * bar G f i := by
  unfold bar; rw [mul_comm,div_mul_cancel₀ _ (dp G i).ne']
lemma centered (f : Port V) (i : V) : ∑ j ∈ G.N i, central G f i j=0 := by
  simp only [central,sum_sub_distrib,sum_const,nsmul_eq_mul]; rw [sumBar]; unfold deg; ring
lemma baravg (f : Port V) : avg G (bar G f) = mass G f := by
  unfold avg mass tot es
  congr 1
  apply sum_congr rfl; intro i _
  simp [sumBar G f i, deg]
lemma intsystem (hd : Mindeg G) (g : Port V) (a : V) : mass G (system G g)=mass G g := by
  unfold mass
  have e : tot G (system G g) = tot G g-tot G (F G g)+tot G (fun _ => mass G g) := by
    simp [tot,es,system,W,sum_add_distrib,sum_sub_distrib]
  rw [e,invariant G hd,sub_self,zero_add,tot_const]
  simp [mass,mul_comm (vol G), (vol_pos G a).ne']
lemma indmass (a : V) : mass G (indicator a)=piV G a := by
  classical
  unfold mass tot es piV
  congr 1
  rw [sum_eq_single a]
  · simp [indicator,deg]
  · intro i _ hi; simp [indicator,hi]
  · simp
def sol (hd : Mindeg G) (hb : Branching G) (a : V) (s : V×V) :=
  (bar G (kernelCol G hd hb a) a - kernelCol G hd hb a s) / piV G a
lemma solbar (hd : Mindeg G) (hb : Branching G) (a i : V) :
    bar G (sol G hd hb a) i =
     (bar G (kernelCol G hd hb a) a - bar G (kernelCol G hd hb a) i)/piV G a := by
  let k := kernelCol G hd hb a
  change (∑ j ∈ G.N i, (bar G k a-k (i,j))/piV G a)/deg G i = _
  simp only [div_eq_mul_inv,←sum_mul,sum_sub_distrib,sum_const,nsmul_eq_mul]
  rw [sumBar]
  change (deg G i * _ - deg G i * _) * _ * _ = _
  field_simp [(dp G i).ne',(pi_pos G a).ne']; ring
lemma solavg (hd : Mindeg G) (hb : Branching G) (a : V) :
    avg G (bar G (sol G hd hb a)) = bar G (kernelCol G hd hb a) a/piV G a-1 := by
  let k := kernelCol G hd hb a
  have mk : mass G k=piV G a := by rw [←intsystem G hd k a]; change mass G (system G (Z G hd hb (indicator a))) = _; rw [fundamental_eq,indmass]
  have ek : tot G k=piV G a*vol G := (div_eq_iff (vol_pos G a).ne').mp mk
  rw [baravg]
  change (es G (fun i j => (bar G k a-k (i,j))/piV G a))/vol G = _
  simp only [es,div_eq_mul_inv,←sum_mul,sum_sub_distrib,sum_const,nsmul_eq_mul]
  change (vol G*bar G k a-tot G k) * _ * _ = _
  rw [ek]
  field_simp [(vol_pos G a).ne',(pi_pos G a).ne']; ring
lemma sol_poisson (hd : Mindeg G) (hb : Branching G) (a : V) (s : V×V) :
    sol G hd hb a s - F G (sol G hd hb a) s = bias G a s.1 := by
  let k := kernelCol G hd hb a
  have mk : mass G k=piV G a := by rw [←intsystem G hd k a]; change mass G (system G (Z G hd hb (indicator a))) = _; rw [fundamental_eq,indmass]
  have row := congrFun (fundamental_eq G hd hb (indicator a)) s
  change k s - F G k s + mass G k = indicator a s at row
  rw [mk] at row
  have den : ((allowed G s).card:ℝ) ≠ 0 := by exact_mod_cast (allowed_pos G s).card_pos.ne'
  have af : F G (sol G hd hb a) s = (bar G k a-F G k s)/piV G a := by
    change (∑ j ∈ allowed G s, (bar G k a-k (j,s.1))/piV G a) / _ = (_ - (∑ j ∈ allowed G s,k (j,s.1)) / _) / _
    simp only [div_eq_mul_inv,←sum_mul,sum_sub_distrib,sum_const,nsmul_eq_mul]
    field_simp [den,(pi_pos G a).ne']; ring
  rw [af]
  change (_-k s)/_ - (_-F G k s)/_ = 1-indicator a s/_
  field_simp [(pi_pos G a).ne']; linarith

-- Weak port equations for the difference of killed and full potentials.
structure Data (G : Graph V) (a : V) where
  x : V → ℝ
  U : V → ℝ
  eta : V → V → ℝ
  z : V → V → ℝ
  e : V → V → ℝ
  anchor : x a=0
  cent : ∀ i, ∑ j ∈ G.N i, eta i j=0
  centZ : ∀ i, ∑ j ∈ G.N i, z i j=0
  harm : ∀ i, ∑ j ∈ G.N i,(x i-x j-eta j i)=0
  full : ∀ i, ∑ j ∈ G.N i,(U i-U j-z j i-bias G a i)=0
  fullPort : ∀ i, ∀ j ∈ G.N i,(deg G i-1)*z i j+U j+z j i-U i+bias G a i=0
  source : ∀ i, ∀ j ∈ G.N i, e i j=(deg G i-1)*eta i j + x j-x i+eta j i
  support : ∀ i, i≠a → ∀ j ∈ G.N i, e i j=0
  stop : ∀ j ∈ G.N a, eta a j = -z a j

variable {G} {a : V}
def t (d : Data G a) (i j : V) := d.x j-d.x i+d.eta j i
lemma centerT (d : Data G a) (i : V) : ∑ j ∈ G.N i, t d i j=0 := by
  have eq := d.harm i
  simp only [t,sum_sub_distrib,sum_add_distrib] at *; linarith
lemma isometry (d : Data G a) : es G (fun i j => (t d i j)^2) = es G (fun i j => (d.eta i j)^2) := by
  have cross (f : V → V → ℝ) (hz : ∀ i, ∑ j ∈ G.N i,f i j=0) :
      es G (fun i j => 2*d.x i*f i j)=0 := by simp [es,←mul_sum,hz]
  have eq := flip G (fun i j => (d.x i + d.eta i j)^2)
  have expand (f : V → V → ℝ) :
      es G (fun i j => (d.x i+f i j)^2) =
      es G (fun i _ => (d.x i)^2)+es G (fun i j => 2*d.x i*f i j)+es G (fun i j => (f i j)^2) := by
    simp [es,add_sq,sum_add_distrib]
  have eq' : es G (fun i j => (d.x i+t d i j)^2) = es G (fun i j => (d.x i+d.eta i j)^2) := by
    have q (i j : V) : d.x i+t d i j = d.x j+d.eta j i := by unfold t; ring
    simpa only [q] using eq
  rw [expand,expand,cross _ (centerT d),cross _ d.cent] at eq'
  linarith

lemma gap_identity (d : Data G a) : es G (fun i _ => d.x i) = es G (fun i j => d.eta i j*d.e i j) := by
  let f := fun i j => -d.x i*(d.U i-d.U j-d.z j i-bias G a i) +
    d.U i*(d.x i-d.x j-d.eta j i) +
    d.eta i j*((deg G i-1)*d.z i j+d.U j+d.z j i-d.U i+bias G a i) +
    (d.U i-bias G a i)*d.eta i j - d.x i*d.z i j
  have zero : es G f=0 := by
    apply sum_eq_zero; intro i _
    have p : ∑ j ∈ G.N i,d.eta i j*((deg G i-1)*d.z i j+d.U j+d.z j i-d.U i+bias G a i)=0 :=
      sum_eq_zero fun j hj => by rw [d.fullPort i j hj,mul_zero]
    simp only [f,sum_sub_distrib,sum_add_distrib,←mul_sum,d.cent,d.centZ,d.full,d.harm,p,mul_zero,add_zero,sub_zero]
  let g := fun i j => d.x i-d.eta i j*d.e i j
  have localEq (i j : V) (hj : j ∈ G.N i) : f i j + f j i = g i j + g j i := by
    have w (k l : V) (hl : l ∈ G.N k) : d.eta k l*d.e k l = -d.z k l*d.e k l := by
      by_cases hk : k=a
      · subst k; rw [d.stop l hl]
      · simp [d.support k hk l hl]
    have xb (k : V) : d.x k*bias G a k=d.x k := by by_cases h : k=a <;> simp [bias,h,d.anchor]
    dsimp [g]
    rw [w i j hj,w j i (G.symm.mp hj),d.source i j hj,d.source j i (G.symm.mp hj)]
    dsimp [f]
    linarith only [xb i,xb j]
  have sym (p : V → V → ℝ) : es G (fun i j => p i j+p j i) = es G p + es G p := by
    have e := flip G p
    simp only [es,sum_add_distrib] at e ⊢; rw [e]
  have e : es G (fun i j => f i j+f j i) = es G (fun i j => g i j+g j i) :=
    sum_congr rfl fun i _ => sum_congr rfl fun j hj => localEq i j hj
  rw [sym,sym,zero] at e
  simp only [es,g,sum_sub_distrib] at e ⊢; linarith
end
end Gap
