import tactic
import topology.basic topology.path_connected
import lemmas

open classical unit_interval path
open_locale classical unit_interval filter topological_space
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

def third_fun1 (h : homotopy X x p r) : Π (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)), (ij.2 ≤ 1) → X := λ ij h', h.to_fun ⟨ij.1 , ⟨ij.2 , and.intro ij.2.2.1 h'⟩⟩

#check add_neg_le_add_neg_iff

def zero_le_sub_one_of_not_le_one (j : ℝ) (h : ¬ j ≤ 1) : 0 ≤ j - 1 :=
begin
  rw sub_eq_add_neg,
  rw ← (sub_zero (0 : ℝ)),
  rw sub_eq_add_neg,
  rw add_neg_le_add_neg_iff,
  rw add_zero,
  rw zero_add,
  linarith,
end

def sub_one_le_one_of_le_two (j : ℝ) (h : j ≤ 2) : j - 1 ≤ 1 :=
begin
  rw sub_eq_add_neg,
  linarith,
end

def zero_le_sub_one_of_one_le (j : ℝ) (h : 1 ≤ j) : 0 ≤ j - 1 :=
begin
  rw sub_eq_add_neg,
  linarith,
end

def third_fun2 (g : homotopy X x r q) : Π (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)), (¬ ij.2 ≤ 1) → X := 
λ ij h', g.to_fun ⟨ij.1 , ⟨ij.2 - 1 , and.intro (zero_le_sub_one_of_not_le_one _ h') (sub_one_le_one_of_le_two ij.2 ij.2.2.2)⟩⟩

def third_fun (h : homotopy X x p r) (g : homotopy X x r q) : 
↥I × ↥(set.Icc (0 : ℝ) 2) → X := λ ij, dite (ij.2 ≤ 1) (third_fun1 X x p r h ij) 
                                                       (third_fun2 X x q r g ij)

lemma third_fun1_contin (h : homotopy X x p r) : continuous (third_fun1 X x p r h : {ij : ↥I × ↥(set.Icc (0 : ℝ) 2)| ij.2 ≤ 1} → X)
:= continuous.comp (h.contin) (by continuity)

lemma third_fun2_contin (g : homotopy X x r q) : continuous (third_fun2 X x q r g : {ij : ↥I × ↥(set.Icc (0 : ℝ) 2) | ¬ ij.2 ≤ 1} → X) 
:= continuous.comp (g.contin) (by continuity)

@[simp, norm_cast] lemma coe_one_two (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)) (H : ij.2 = 1) : (ij.2 : ℝ) = 1 :=
begin
  rw H,
  split,
end

lemma third_fun1_eq (h : homotopy X x p r) (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)) (hij : ij.2 ≤ 1) : third_fun1 X x p r h ij hij = h.to_fun ⟨ij.1 , ⟨ij.2 , and.intro ij.2.2.1 hij⟩⟩ :=
rfl 

lemma third_fun2_eq (g : homotopy X x r q) (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)) (hij : ¬ ij.2 ≤ 1) : third_fun2 X x q r g ij hij = g.to_fun ⟨ij.1 , ⟨ij.2 - 1 , and.intro (zero_le_sub_one_of_not_le_one _ hij) (sub_one_le_one_of_le_two ij.2 ij.2.2.2)⟩⟩ :=
rfl

lemma third_fun1_eq_at_one (h : homotopy X x p r) (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)) (hij : ij.2 ≤ 1) (H : ij.2 = 1) :
(third_fun1 X x p r h ij hij) = r.to_fun ij.1 := 
begin
  transitivity,
  rw third_fun1_eq,
  simp only [H],
  simp,
  rw h.right',
end

def aux_third_fun (g : homotopy X x r q) : Π (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)), (1 ≤ ij.2) → X :=
λ ij h', g.to_fun (ij.1 , ⟨ij.2 - 1 , and.intro (zero_le_sub_one_of_one_le _ h') (sub_one_le_one_of_le_two _ ij.2.2.2)⟩)

lemma aux_third_fun_contin (g : homotopy X x r q) : continuous (aux_third_fun X x q r g : {ij : ↥I × ↥(set.Icc (0 : ℝ) 2)| 1 ≤ ij.2} → X) :=
continuous.comp (g.contin) (by continuity)

lemma third_fun2_eq_aux (g : homotopy X x r q) (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)) (hij : ¬ ij.2 ≤ 1) (hij' : 1 ≤ ij.2): third_fun2 X x q r g ij hij = aux_third_fun X x q r g ij hij' := rfl

lemma aux_third_fun_eq (g : homotopy X x r q) (ij  : ↥I × ↥(set.Icc (0 : ℝ) 2)) (hij : 1 ≤ ij.2) : aux_third_fun X x q r g ij hij = g.to_fun ⟨ij.1 , ⟨ij.2 - 1 , and.intro (zero_le_sub_one_of_one_le _ hij) (sub_one_le_one_of_le_two _ ij.2.2.2)⟩⟩ := rfl

lemma third_fun2_eq_aux2 (g : homotopy X x r q) (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)) (hij : ¬ ij.2 ≤ 1) : third_fun2 X x q r g ij hij = aux_third_fun X x q r g ij (le_of_not_le hij) := rfl

lemma aux_third_fun_eq_at_one (g : homotopy X x r q) (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)) (hij : 1 ≤ ij.2) (H : ij.2 = 1) : 
(aux_third_fun X x q r g ij hij) = r.to_fun ij.1 :=
begin
  rw aux_third_fun_eq,
  simp [H],
  rw g.left',
end

lemma third_fun2_aux_preimage_agree (g : homotopy X x r q) (s : set X) : (↑((third_fun2 X x q r g : {ij : ↥I × ↥(set.Icc (0 : ℝ) 2) | ¬ ij.2 ≤ 1} → X) ⁻¹' s) : set (↥I × ↥(set.Icc (0 : ℝ) 2)))
                                                                       = ↑((aux_third_fun X x q r g : {ij : ↥I × ↥(set.Icc (0 : ℝ) 2) | 1 ≤ ij.2} → X) ⁻¹' s) \ {ij | ij.2 = 1} :=
begin
  ext,
  split,
  rename x_1 i,
  intro hi,
  cases hi with hi2 hi,
  split,
  split,
  swap,
  apply set.mem_def.2,
  apply le_of_not_le,
  apply (@set.mem_def _ i _).1,
  exact hi2,
  apply (@set.mem_preimage _ _ (aux_third_fun X x q r g : {ij : ↥I × ↥(set.Icc (0 : ℝ) 2) | 1 ≤ ij.2} → X) s ⟨i , _⟩).2,
  rw coe_pi_fun_eq,
  rw ← third_fun2_eq_aux,
  have H := (@set.mem_preimage _ _ (third_fun2 X x q r g : {ij : ↥I × ↥(set.Icc (0 : ℝ) 2) | ¬ ij.2 ≤ 1} → X) s ⟨i , hi2⟩).1 hi,
  use H,
  apply (@set.mem_def _ i _).2,
  intro H,
  apply set.mem_def.2 hi2,
  apply le_of_eq,
  exact set.mem_def.2 H,
  rename x_1 i,
  intro hi,
  cases hi with hi1 hi2,
  split,
  apply (@set.mem_preimage _ _ (third_fun2 X x q r g : {ij : ↥I × ↥(set.Icc (0 : ℝ) 2) | ¬ ij.2 ≤ 1} → X) s ⟨i , _⟩).2,
  rw coe_pi_fun_eq,
  rw third_fun2_eq_aux,
  cases hi1 with hi hi1,
  have H := (@set.mem_preimage _ _ (aux_third_fun X x q r g : {ij : ↥I × ↥(set.Icc (0 : ℝ) 2) | 1 ≤ ij.2} → X) s ⟨i , _⟩).1 hi1,
  use H,
  cases hi1 with hi hi1,
  use hi,
  cases hi1 with hi1 hi,
  apply set.mem_def.2,
  simp,
  apply lt_of_le_of_ne,
  use hi1,
  simp at hi2,
  symmetry,
  exact hi2,
end

lemma third_frontier1 (h : homotopy X x p r) (g : homotopy X x r q) :
∀ (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)),
ij ∈ frontier {jk : ↥I × ↥(set.Icc (0 : ℝ) 2) | jk.2 ≤ 1} →
∀ (H : ¬ ij.2 ≤ 1),
filter.tendsto (third_fun1 X x p r h : {jk : ↥I × ↥(set.Icc (0 : ℝ) 2) | jk.2 ≤ 1} → X)
               ↑(𝓝 ij)
               (𝓝 ((third_fun2 X x q r g) ij H)) :=
begin
  intros ij hij H,
  apply filter.tendsto_def.2,
  intros s hs,
  have H' := front_single ij hij,
  by_contra,
  apply H,
  apply le_of_eq,
  exact H',
end

lemma third_frontier2 (h : homotopy X x p r) (g : homotopy X x r q) :
∀ (ij : ↥I × ↥(set.Icc (0 : ℝ) 2)),
ij ∈ frontier {jk : ↥I × ↥(set.Icc (0 : ℝ) 2) | jk.2 ≤ 1} →
∀ (H : ij.2 ≤ 1),
filter.tendsto (third_fun2 X x q r g : {jk : ↥I × ↥(set.Icc (0 : ℝ) 2) | ¬ jk.2 ≤ 1} → X)
               ↑(𝓝 ij)
               (𝓝 ((third_fun1 X x p r h) ij H)) :=
begin
  intros ij hij H,
  apply filter.tendsto_def.2,
  intros s hs,
  have H' := front_single ij hij,
  rw (third_fun1_eq_at_one X x p r h ij H H') at hs,
  rw ← (aux_third_fun_eq_at_one X x q r g ij _ H') at hs,
  swap,
  apply le_of_eq,
  symmetry,
  exact H',
  rw ← (@coe_pi_fun_eq _ _ _ (aux_third_fun X x q r g) _ _) at hs,
  have aux_H := continuous.continuous_at (aux_third_fun_contin X x q r g),
  swap,
  split,
  apply le_of_eq,
  symmetry,
  exact H',
  have aux_H' := continuous_at.preimage_mem_nhds aux_H hs,
  rw nhds_subtype_eq_comap at aux_H',
  rcases aux_H' with ⟨U , hU1 , hU2⟩,
  split,
  swap,
  exact U ∪ (↑((third_fun2 X x q r g : {ij : ↥I × ↥(set.Icc (0 : ℝ) 2)| ¬ ij.2 ≤ 1} → X) ⁻¹' s) : set (↥I × ↥(set.Icc (0 : ℝ) 2))),
  split,
  apply (𝓝 ij).sets_of_superset,
  exact hU1,
  intros a ha,
  left,
  exact ha,
  ext,
  rename x_1 jk,
  split,
  intro hjk,
  cases hjk with hjk1 hjk2,
  split,
  exact hjk1,
  right,
  split,
  exact hjk2,
  intro hjk,
  cases hjk with hjk1 hjk2,
  cases hjk2,
  rw third_fun2_aux_preimage_agree,
  split,
  split,
  apply hU2,
  use hjk2,
  apply set.mem_def.2,
  by_contra,
  apply hjk1,
  apply le_of_not_le,
  use h,
  simp,
  intro H,
  apply hjk1,
  apply le_of_eq,
  exact H,
  exact hjk2,
end

lemma third_contin (h : homotopy X x p r) 
                   (g : homotopy X x r q) :
continuous (third_fun X x p q r h g) := 
continuous_dif (↥I × ↥(set.Icc (0 : ℝ) 2)) X (_) 
               (third_fun1 X x p r h) (third_fun2 X x q r g) 
               (third_fun1_contin X x p r h) (third_fun2_contin X x q r g) 
               (third_frontier1 X x p q r h g) (third_frontier2 X x p q r h g)

def third_homotopy (h : homotopy X x p r) (g : homotopy X x r q) : homotopy X x p q :=
{ to_fun  := third_fun X x p q r h g ∘ (prod.map id (Icc_homeo_I (0 : ℝ) 2 (by linarith)).symm),
  contin  := continuous.comp (third_contin X x p q r h g) (continuous.prod_map continuous_id (Icc_homeo_I (0 : ℝ) 2 (by linarith)).continuous_inv_fun),
  source' := λ t, 
  begin
    rename h hom,
    simp,
    have H := Icc_homeo_I_symm_apply_coe (0 : ℝ) 2 (by linarith) t,
    rw sub_zero at H,
    rw add_zero at H,
    have H' : (((Icc_homeo_I (0 : ℝ) 2 (by linarith)).symm t) : set.Icc (0 : ℝ) 2) = ⟨2 * t , _⟩,
    ext,
    exact H,
    rw H',
    by_cases ((⟨0 , ⟨2 * t , _⟩⟩ : ↥I × ↥(set.Icc (0 : ℝ) 2)).2 ≤ 1),
    rw third_fun,
    simp [h],
    rw third_fun1_eq,
    simp,
    exact hom.source' _,
    
  end,
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