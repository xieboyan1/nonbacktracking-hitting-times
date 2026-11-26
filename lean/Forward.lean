import Kemeny
namespace Forward
set_option linter.unusedSectionVars false
open Finset Stationary Fundamental Kemeny Gap
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] (G : Graph V)
def J (f : Port V) (s : V×V) := f (s.2,s.1)
lemma JJ (f : Port V) : J (J f)=f := rfl
def transition (f : Port V) := J (F G (J f))
def operator (f : Port V) := fun s => f s-transition G f s+mass G f
def inverse (hd : Mindeg G) (hb : Branching G) (f : Port V) := J (Z G hd hb (J f))
lemma massJ (f : Port V) : mass G (J f)=mass G f := by
  unfold mass tot; rw [show es G (fun i j => J f (i,j))=es G (fun i j => f (i,j)) from flip G _]
lemma solution (hd : Mindeg G) (hb : Branching G) (f : Port V) : operator G (inverse G hd hb f)=f := by
  funext s
  have e := congrFun (fundamental_eq G hd hb (J f)) (s.2,s.1)
  change _-_+mass G (J _) = _
  rw [massJ]; exact e
lemma genuine_transition (f : Port V) (i j : V) :
    transition G f (i,j) = (∑ k ∈ Walks.allowed G (j,i),f (j,k))/(Walks.allowed G (j,i)).card := rfl
def dot (f g : Port V) := es G (fun i j => f (i,j)*g (i,j))
lemma adjoint (hd : Mindeg G) (f g : Port V) : dot G (F G f) g = dot G f (transition G g) := by
  let p := fun i j => f (i,j)*transition G g (i,j)
  rw [show dot G f (transition G g)=es G p from rfl,←flip G p]
  apply sum_congr rfl
  intro i _
  have hi := Bounds.dmin hd i
  apply mul_left_cancel₀ (show deg G i-1≠0 by linarith)
  rw [Finset.mul_sum,Finset.mul_sum]
  have a (j : V) (hj : j ∈ G.N i) :
      (deg G i-1)*(F G f (i,j)*g (i,j)) =
      (∑ k ∈ G.N i,f (k,i))*g (i,j) - f (j,i)*g (i,j) := by
    have e := at_port G hd f hj
    nlinarith only [congrArg (fun z : ℝ => z*g (i,j)) e]
  have b (j : V) (hj : j ∈ G.N i) :
      (deg G i-1)*p j i =
      f (j,i)*(∑ k ∈ G.N i,g (i,k)) - f (j,i)*g (i,j) := by
    have e := at_port G hd (J g) hj
    change _ * F G (J g) (i,j)+g (i,j)=∑ k ∈ G.N i,g (i,k) at e
    change _*(f (j,i)* F G (J g) (i,j))=_
    nlinarith only [congrArg (fun z : ℝ => f (j,i)*z) e]
  rw [sum_congr rfl a,sum_congr rfl b]
  simp [sum_sub_distrib,←mul_sum,←sum_mul]
lemma sys_adjoint (hd : Mindeg G) (f g : Port V) :
    dot G (system G f) g=dot G f (operator G g) := by
  have e := adjoint G hd f g
  change es G (fun i j => (f (i,j)-F G f (i,j)+mass G f)*g (i,j)) =
    es G (fun i j => f (i,j)*(g (i,j)-transition G g (i,j)+mass G g))
  have k : mass G f*tot G g=tot G f*mass G g := by unfold mass; ring
  simp only [es,tot,dot,add_mul,sub_mul,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,
    ←mul_sum,←sum_mul] at e k ⊢
  linarith
lemma block (hd : Mindeg G) (hb : Branching G) (a : V) :
    bar G (inverse G hd hb (indicator a)) a = bar G (kernelCol G hd hb a) a := by
  let f := Z G hd hb (indicator a)
  let g := inverse G hd hb (indicator a)
  have eq := sys_adjoint G hd f g
  change dot G (system G (Z G hd hb (indicator a))) g = dot G f (operator G (inverse G hd hb (indicator a))) at eq
  rw [fundamental_eq,solution] at eq
  have left (k : Port V) : dot G (indicator a) k=∑ j ∈ G.N a,k (a,j) := by
    unfold dot es
    rw [sum_eq_single a]
    · simp [indicator]
    · intro i _ hi; simp [indicator,hi]
    · simp
  rw [left] at eq
  have swap : dot G f (indicator a)=dot G (indicator a) f :=
    Bounds.eq_es (fun i j _ => mul_comm _ _)
  rw [swap,left] at eq
  exact congrArg (fun z : ℝ => z/deg G a) eq
theorem projected_trace (hd : Mindeg G) (hb : Branching G) :
    (∑ a,bar G (inverse G hd hb (indicator a)) a)-1 = projected G hd hb := by
  simp only [block,projected]
-- Valid ports form a closed subsystem. Extending the inverse to auxiliary
-- pairs leaves its values on valid ports uniquely specified.
def Valid (s : V×V) := s.2 ∈ G.N s.1
lemma depends_valid {f g : Port V} (same : ∀ s, Valid G s → f s=g s) :
    F G f = F G g ∧ mass G f=mass G g := by
  constructor
  · funext s
    apply congrArg (fun z : ℝ => z / (Walks.allowed G s).card)
    apply sum_congr rfl
    intro k hk; apply same
    apply G.symm.mp
    unfold Walks.allowed at hk
    split at hk
    · exact hk
    · exact (mem_erase.mp hk).2
  · apply congrArg (fun z : ℝ => z/vol G)
    exact Bounds.eq_es (fun i j hj => same (i,j) hj)
theorem valid_inverse (hd : Mindeg G) (hb : Branching G) (rhs f : Port V)
    (he : ∀ s,Valid G s → system G f s=rhs s) :
    ∀ s,Valid G s → f s=Z G hd hb rhs s := by
  classical
  let g : Port V := fun s => if Valid G s then f s else rhs s + F G f s - mass G f
  have same (s) (h : Valid G s) : g s=f s := by simp [g,h]
  have dep := depends_valid G same
  have eq : system G g = rhs := by
    funext s
    change g s-F G g s+mass G g=rhs s
    rw [dep.1,dep.2]
    by_cases hs : Valid G s
    · rw [same s hs]; exact he s hs
    · simp [g,hs]; ring
  have uniq := (invertible G hd hb).1 (eq.trans (fundamental_eq G hd hb rhs).symm)
  exact fun s hs => (same s hs).symm.trans (congrFun uniq s)
#print axioms valid_inverse
#print axioms projected_trace
end
end Forward
