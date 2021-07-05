import tactic
import topology.basic topology.path_connected
import lemmas

open classical unit_interval path
open_locale classical unit_interval
noncomputable theory

universes u v w

namespace based

variables (X : Type u) [topological_space X] (x : X)

def loop_space := path x x

structure homotopy (p q : loop_space X x) :=
(to_fun  : I × I → X)
(contin  : continuous to_fun)
(source' : ∀ t, to_fun ⟨0 , t⟩ = x)
(target' : ∀ t, to_fun ⟨1 , t⟩ = x )
(left'   : ∀ y, to_fun ⟨y , 0⟩ = p.to_fun y)
(right'  : ∀ y, to_fun ⟨y , 1⟩ = q.to_fun y)

def in_homotopy : loop_space X x → loop_space X x → Prop := λ p q, nonempty (homotopy X x p q)

variables p q r : loop_space X x

def trivial_homotopy : homotopy X x p p := 
{ to_fun  := p.to_fun ∘ prod.fst,
  contin  := continuous.comp (p.continuous') (continuous_fst),
  source' := λ _, p.source',
  target' := λ _, p.target',
  left'   := λ _, rfl,
  right'  := λ _, rfl }

def inverse_homotopy (h : homotopy X x q p) : homotopy X x p q :=
{ to_fun  := h.to_fun ∘ (λ i, ⟨id i.1, σ i.2⟩),
  contin  := continuous.comp (h.contin) (continuous.prod_map (continuous_id) (continuous_symm)),
  source' := λ _, h.source' _,
  target' := λ _, h.target' _,
  left'   := λ _, by simp [h.right'],
  right'  := λ _, by simp [h.left'] }

def coe_I_Icc02 : ↥I × ↥I → ↥I × ↥(I ∪ (set.Icc (1 : ℝ) 2)) := λ i, ⟨i.1 , ⟨i.2 , or.inl i.2.2⟩⟩

instance : has_coe (↥I × ↥I) (↥I × ↥(I ∪ (set.Icc (1 : ℝ) 2))) := { coe := coe_I_Icc02 }

def sum_fun : I × I → (I × I) ⊕ (I × set.Icc (1 : ℝ) 2) := (λ i, dite (prod.snd i ≤ (1 : set.Icc (0 : ℝ) 2)) (λ h', sum.inl ⟨i.1 , ⟨i.2 , and.intro i.2.2.1 h'⟩⟩) 
                                                                                                             (λ h', sum.inr ⟨i.1 , ⟨i.2 , and.intro (le_of_not_ge (λ hi, h' (ge_iff_le.2 hi))) i.2.2.2⟩⟩)) 
                                                            ∘ (λ ⟨i , j⟩, (⟨id i , (Icc_homeo_I (0 : ℝ) 2 (by simp)).to_equiv.inv_fun j⟩ : I × set.Icc (0 : ℝ) 2))

-- λ y, ((λ (i : (I × I) ⊕ (I × set.Icc (1 : ℝ) 2)), @sum.rec (I × I) (I × set.Icc (1 : ℝ) 2) (λ _, X) h.to_fun (λ i, g.to_fun ⟨id i.1 , (Icc_homeo_I _ _ _).to_equiv.to_fun i.2⟩)) (sum_fun y))

def sum_funb (h : homotopy X x p r) (g : homotopy X x r q) : ((I × I) ⊕ (I × set.Icc (1 : ℝ) 2)) → X :=
@sum.rec (I × I) (I × set.Icc (1 : ℝ) 2) (λ _, X) h.to_fun (g.to_fun ∘ (λ (ii : I × set.Icc (1 : ℝ) 2), ⟨prod.fst ii , ((Icc_homeo_I (1 : ℝ) 2 (by linarith)).to_equiv.to_fun ∘ prod.snd) ii⟩))

lemma sum_funb_continuous (h : homotopy X x p r) (g : homotopy X x r q) : continuous (sum_funb X x p q r h g) :=
continuous_sum_rec h.contin (continuous.comp (g.contin) (continuous.prod_map continuous_id (Icc_homeo_I (1 : ℝ) 2 (by linarith)).continuous_to_fun))

def third_homotopy (h : homotopy X x p r) (g : homotopy X x r q) : homotopy X x p q :=
{ to_fun  := (sum_funb X x p q r h g) ∘ sum_fun,
  contin  := _,
  source' := _,
  target' := _,
  left'   := _,
  right'  := _ }

instance : inhabited (homotopy X x p p) := { default := trivial_homotopy X x p }

instance inhabited_if_opp_inhabited (h : inhabited (homotopy X x q p)) : inhabited (homotopy X x p q) :=
{ default := inverse_homotopy X x p q h.default }

def in_hom_reflx : reflexive (in_homotopy X x) := λ p, nonempty_of_inhabited

def in_hom_symm  : symmetric (in_homotopy X x) := λ p q, assume h' : in_homotopy X x p q,
                                                         have h : inhabited (homotopy X x p q) := inhabited_of_nonempty h',
                                                         @nonempty_of_inhabited (homotopy X x q p) (based.inhabited_if_opp_inhabited X x q p h)

def in_hom_trans : transitive (in_homotopy X x) := _

def loop_space_setoid : setoid (loop_space X x) :=
{ r     := in_homotopy X x,
  iseqv := and.intro (in_hom_reflx X x) 
           (and.intro (in_hom_symm X x) _) }

end based