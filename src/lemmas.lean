import tactic
import topology.basic topology.path_connected topology.continuous_on
import data.set order.filter.basic

open classical unit_interval path
open_locale classical unit_interval filter topological_space
noncomputable theory

universes u v w

instance : has_one ↥(set.Icc (0 : ℝ) 2) := { one := ⟨1 , and.intro (by simp) (by linarith)⟩ }

@[simp, norm_cast] lemma coe_one : ((1 : set.Icc (0 : ℝ) 2) : ℝ) = 1 := rfl

@[simp] lemma mk_one (h : (1 : ℝ) ∈ set.Icc (0 : ℝ) 2) : (⟨1 , h⟩ : set.Icc (0 : ℝ) 2) = 1 := rfl 

def coe_Pi_fun (α : Type u) (β : Type v) (p : α → Prop) (f : Π (a : α), p a → β) : {a : α | p a} → β := λ a, f a a.2

instance (α : Type u) (β : Type v) (p : α → Prop) : has_coe (Π (a : α), p a → β) ({a | p a} → β) := { coe := λ f, coe_Pi_fun α β p f }

@[simp, norm_cast] lemma coe_pi_fun {α : Type u} {β : Type v} {p : α → Prop} {f : Π (a : α), p a → β} : (f : {a | p a} → β) = coe_Pi_fun α β p f := rfl
 
instance coe_sub (α : Type u) (s : set α) : has_coe {x // x ∈ s} s := { coe := λ ⟨a , h⟩, ⟨a , h⟩ }

instance mem_sub {α : Type u} {s : set α} : has_mem {x // x ∈ s} (set ↥s) := { mem := λ ⟨a , h⟩ U, (⟨a , h⟩ : s) ∈ U }

@[simp] lemma mem_sub_norm (α : Type u) (s : set α) (U : set ↥s) (a : {x // x ∈ s}) (h : a.1 ∈ s) : (a : {x // x ∈ s}) ∈ (U : set s) ↔ (⟨a.1 , h⟩ : s) ∈ (U : set s) := by simp

instance subset_has_mem (α : Type u) (s : set α) : has_mem α (set ↥s) := { mem := λ a U, ∃ (h : a ∈ s), (⟨a , h⟩ : s) ∈ U }

@[simp] lemma subset_has_mem_norm (α : Type u) (s : set α) (U : set ↥s) (a : α) (h : a ∈ s) : a ∈ U ↔ ↑(⟨a , h⟩ : s) ∈ U := iff.rfl

def coe_subset_fun (α : Type u) (s : set α) (U : set s) : set α := {a | a ∈ U}

instance coe_subset (α  : Type u) (s : set α) : has_coe (set s) (set α) := { coe := coe_subset_fun α s }

@[simp, norm_cast] lemma mem_sub_norm_more (α : Type u) (s : set α) (U : set s) : (U : set α) = {a | a ∈ U} := rfl

@[simp, norm_cast] lemma mem_sub_norm_univ (α : Type u) (s : set α) (x : α) : x ∈ ((@set.univ s) : set α) ↔ x ∈ s := 
begin 
  split,
  { intro h,
  cases h,
  exact h_w, },
  { 
    intro h,
    split,
    swap,
    exact h,
    rw set.univ,
    apply set.mem_def.2,
    tauto,
  },
end

@[simp, norm_cast] lemma mem_sub_norm_univ_eq (α : Type u) (s : set α) : ↑(@set.univ s) = s := set.ext (λ x, mem_sub_norm_univ α s x)

@[simp] lemma mem_sub_norm_sub (α : Type u) (s : set α) (U : set s) : (U : set α) ⊆ s :=
begin 
  intros x hx,
  cases hx,
  exact hx_w,
end

@[simp] lemma mem_sub_norm_sub2 (α : Type u) (s : set α) (U V : set s) : U ⊆ V ↔ (U : set α) ⊆ (V : set α) :=
begin
  split,
  intro H,
  intros a ha,
  cases ha with Ha ha,
  split,
  swap,
  exact Ha,
  apply H,
  exact ha,
  intro H,
  intros a ha,
  cases a with a Ha,
  specialize H ⟨_ , ha⟩,
  cases H with Ha' H,
  simp [Ha] at H,
  exact H,
end 

@[simp, norm_cast] lemma mem_sub_norm_inter (α : Type u) (s : set α) (x y : set s) : (↑(x ∩ y) : set α) = ↑x ∩ ↑y :=
begin
  apply set.ext,
  intro a,
  split,
  intro ha,
  cases ha,
  cases ha_h,
  split,
  split,
  exact ha_h_left,
  split,
  exact ha_h_right,
  intro ha,
  simp,
  simp at ha,
  cases ha with hax hay,
  cases hax with hasx hax,
  cases hay with hasy hay,
  have haa : hasx = hasy,
  {
    simp,
  },
  rw haa at *,
  existsi hasy,
  split,
  exact hax,
  exact hay,
end

def intersection_filter (α : Type u) (s : set α) (𝓕 : filter α) : filter s := 
{ sets := {U | ∃ (F : set α), F ∈ 𝓕 ∧ (U : set α) = (s : set α) ∩ (F : set α)},
  univ_sets := set.mem_def.2 (exists.intro (@set.univ α) 
                                           (and.intro 𝓕.univ_sets 
                                           (trans (mem_sub_norm_univ_eq α s) (by simp)))),
  sets_of_superset := λ x y hx hxy, 
                     begin 
                       cases hx with F hF,
                       existsi (y : set α) ∪ F,
                       split,
                       {
                         apply (𝓕.sets_of_superset hF.1),
                         simp,
                       },
                       {
                         apply set.eq_of_subset_of_subset,
                         intros y₁ hy₁,
                         split,
                         exact mem_sub_norm_sub α s y hy₁,
                         left,
                         exact hy₁,
                         rw set.inter_distrib_left,
                         intros xx hxx,
                         cases hxx,
                         cases hxx,
                         exact hxx_right,
                         rw ← hF.2 at hxx,
                         cases hxx,
                         specialize hxy hxx_h,
                         split,
                         exact hxy,
                       },
                     end,
  inter_sets := λ x y hx hy,
                begin 
                  cases hx with Fx hFx,
                  cases hy with Fy hFy,
                  existsi Fx ∩ Fy,
                  split,
                  apply (𝓕.inter_sets hFx.1 hFy.1),
                  apply set.eq_of_subset_of_subset,
                  intros a ha,
                  split,
                  cases ha,
                  exact ha_w,
                  cases hFx,
                  cases hFy,
                  rw mem_sub_norm_inter at ha,
                  rw hFx_right at ha,
                  rw hFy_right at ha,
                  split,
                  cases ha,
                  cases ha_left,
                  exact ha_left_right,
                  cases ha,
                  cases ha_right,
                  exact ha_right_right,
                  intros a ha,
                  rw mem_sub_norm_inter,
                  split,
                  rw hFx.2,
                  cases ha,
                  cases ha_right,
                  split,
                  exact ha_left,
                  exact ha_right_left,
                  rw hFy.2,
                  cases ha,
                  cases ha_right,
                  split,
                  exact ha_left,
                  exact ha_right_right,
                end }

instance (α : Type u) (s : set α) : has_coe (filter α) (filter s) := { coe := intersection_filter α s }

variables (α : Type u) (β : Type v) (p : α → Prop) [topological_space α] [topological_space β]

def interior_set (s : set α) : set s := {e | (e : α) ∈ interior s}

@[simp] lemma interior_set_norm (s : set α) : ↑(interior_set α s) = interior s := 
begin
  apply set.ext,
  intro x,
  split,
  intro hx,
  rcases hx with ⟨a , b , c ,d⟩,
  split,
  use c,
  exact d,
  intro hx,
  rcases hx with ⟨a , b , c⟩,
  split,
  split,
  use b,
  exact c,
  rcases b with ⟨d  , e⟩,
  apply e,
  exact c,
end

lemma continuous_dif (f : Π (a : α), p a → β) (g : Π (a : α), ¬ p a → β)
                     (hf : continuous (f : {a | p a} → β))
                     (hg : continuous (g : {a | ¬ p a} → β))
                     (hfb : ∀ x ∈ (frontier {a | p a}), 
                            ∀ H : ¬ p x, (filter.tendsto (f : {a | p a} → β) ↑(𝓝 x) (𝓝 ((g : {a | ¬ p a} → β) ⟨x , H⟩))))
                     (hgb : ∀ x ∈ (frontier {a | p a}),
                            ∀ H : p x, (filter.tendsto (g : {a | ¬ p a} → β) ↑(𝓝 x) (𝓝 ((f : {a | p a} → β) ⟨x , H⟩))))
                     : continuous (λ a, dite (p a) (f a) (g a)) := 
continuous_iff_continuous_at.2 (λ x, 
begin
  apply filter.tendsto_def.2,
  intros s hs,
  have H1 := set.compl_union_self (interior ({a | p a})),
  rw ← closure_compl at H1,
  rw closure_eq_interior_union_frontier at H1,
  rw frontier_compl at H1,
  have H2 : x ∈ interior {a : α | p a}ᶜ ∪ frontier {a : α | p a} ∪ interior {a : α | p a},
  {
    have H2a : x ∈ set.univ,
    apply set.mem_def.2,
    tauto,
    rw ← H1 at H2a,
    exact H2a,
  },
  cases H2 with H3 H2,
  swap,
  have Hx : p x,
  {
    apply set.mem_def.1,
    apply interior_subset,
    exact H2,
  },
  simp [Hx] at hs,
  have Hf : ((f : {a | p a} → β) ⁻¹' s) ∈ (𝓝 ⟨x , Hx⟩ : filter {a | p a}),
  {
    have Hfa := continuous_iff_continuous_at.1 hf ⟨x , Hx⟩,
    have Hfaa := filter.tendsto_def.1 Hfa s,
    apply Hfaa,
    exact hs,
  },
  rw nhds_subtype_eq_comap at Hf,
  rcases Hf with ⟨U , HU1 , HU2⟩,
  have HU3 : U ∩ (interior {a | p a}) ∈ 𝓝 x,
  {
    apply filter.inter_mem_sets,
    exact HU1,
    rw interior_eq_nhds' at H2,
    simp at H2,
    apply interior_mem_nhds.2,
    exact H2,
  },
  apply (𝓝 x).sets_of_superset,
  exact HU3,
  intros a ha,
  cases ha with haU haI,
  have Ha2 : p a,
  {
     apply set.mem_def.1,
     apply mem_of_mem_nhds,
     apply mem_interior_iff_mem_nhds.1,
     exact haI,
  },
  have Ha3 : (⟨a , Ha2⟩ : {a |  p a}) ∈ coe ⁻¹' U,
  {
     apply set.mem_def.2,
     apply set.mem_def.2,
     use haU,
  },
  specialize HU2 Ha3,
  simp [Ha2],
  use HU2,
  cases H3,
  have Hx : ¬ p x,
  {
     rw set.compl_set_of p at H3,
     apply (@set.mem_def α x {a | ¬ p a}).1,
     apply @interior_subset α _ {a | ¬ p a},
     exact H3,
  },
  simp [Hx] at hs,
  have Hg : ((g : {a | ¬ p a} → β) ⁻¹' s) ∈ (𝓝 ⟨x , Hx⟩ : filter {a | ¬ p a}),
  {
     have Hga := continuous_iff_continuous_at.1 hg ⟨x , Hx⟩,
     have Hgaa := filter.tendsto_def.1 Hga s,
     apply Hgaa,
     exact hs,
  },
  rw nhds_subtype_eq_comap at Hg,
  rcases Hg with ⟨U , HU1 , HU2⟩,
  have HU3 : U ∩ (interior {a | ¬ p a}) ∈ 𝓝 x,
  {
    apply filter.inter_mem_sets,
    exact HU1,
    rw interior_eq_nhds' at H3,
    rw set.compl_set_of p at H3,
    simp at H3,
    apply interior_mem_nhds.2,
    exact H3,
  },
  apply (𝓝 x).sets_of_superset,
  exact HU3,
  intros a ha,
  cases ha with haU haI,
  have Ha2 : ¬ p a,
  {
    apply (@set.mem_def α a {a | ¬ p a}).1,
    apply @interior_subset α _ {a | ¬ p a},
    exact haI,
  },
  have Ha3 : (⟨a , Ha2⟩ : {a | ¬ p a}) ∈ coe ⁻¹' U,
  {
    apply set.mem_def.2,
    apply set.mem_def.2,
    use haU,
  },
  specialize HU2 Ha3,
  simp [Ha2],
  use HU2,
  by_cases p x,
  specialize hgb x H3 h,
  rw filter.tendsto_def at hgb,
  simp [h] at hs,
  specialize hgb s hs,
  rcases hgb with ⟨V, HV1, HV2⟩,
  have Hf : ((f : {a | p a} → β) ⁻¹' s) ∈ (𝓝 ⟨x , h⟩ : filter {a | p a}),
  {
    have Hfa := continuous_iff_continuous_at.1 hf ⟨x , h⟩,
    have Hfaa := filter.tendsto_def.1 Hfa s,
    apply Hfaa,
    exact hs,
  },
  rw nhds_subtype_eq_comap at Hf,
  rcases Hf with ⟨U , HU1 , HU2⟩,
  have HUV := filter.inter_mem_sets HU1 HV1,
  apply (𝓝 x).sets_of_superset,
  exact HUV,
  intros a ha,
  cases ha with haU haV,
  rename h Hx,
  by_cases p a,
  swap,
  simp [h],
  have Ha2 : a ∈ {a | ¬ p a} ∩ V,
  {
    split,
    use h,
    exact haV,
  },
  rw ← HV2 at Ha2,
  cases Ha2 with Ha Ha2,
  use Ha2,
  have Ha : (⟨a , h⟩ : {a | p a}) ∈ coe ⁻¹' U,
  {
    apply set.mem_def.2,
    apply set.mem_def.2,
    use haU,
  },
  specialize HU2 Ha,
  simp [h],
  use HU2,
  specialize hfb x H3 h,
  rw filter.tendsto_def at hfb,
  simp [h] at hs,
  specialize hfb s hs,
  rcases hfb with ⟨V , HV1 , HV2⟩,
  have Hg : ((g : {a | ¬ p a} → β) ⁻¹' s) ∈ (𝓝 ⟨x , h⟩ : filter {a | ¬ p a}),
  {
    have Hga := continuous_iff_continuous_at.1 hg ⟨x , h⟩,
    have Hgaa := filter.tendsto_def.1 Hga s,
    apply Hgaa,
    exact hs,
  },
  rw nhds_subtype_eq_comap at Hg,
  rcases Hg with ⟨U , HU1 , HU2⟩,
  have HUV := filter.inter_mem_sets HU1 HV1,
  apply (𝓝 x).sets_of_superset,
  exact HUV,
  intros a ha,
  cases ha with haU haV,
  rename h Hx,
  by_cases p a,
  simp [h],
  have Ha2 : a ∈ {a | p a} ∩ V,
  {
    split,
    use h,
    exact haV,
  },
  rw ← HV2 at Ha2,
  cases Ha2 with Ha Ha2,
  use Ha2,
  have Ha : (⟨a , h⟩ : {a | ¬ p a}) ∈ coe ⁻¹' U,
  {
    apply set.mem_def.2,
    apply set.mem_def.2,
    use haU,
  },
  specialize HU2 Ha,
  simp [h],
  use HU2,
end).

lemma front_single (x : ↥I × ↥(set.Icc (0 : ℝ) 2)) : x ∈ frontier {a : ↥I × ↥(set.Icc (0 : ℝ) 2) | a.snd ≤ 1} → x.snd = 1 := 
λ hx, 
frontier_le_subset_eq (continuous_snd) (by continuity) hx

lemma coe_pi_fun_eq {α : Type u} {β : Type v} {p : α → Prop} {f : Π (a : α), p a → β} {x : α} {hx : p x} : (f : {a | p a} → β) ⟨x , hx⟩ = f x hx := rfl