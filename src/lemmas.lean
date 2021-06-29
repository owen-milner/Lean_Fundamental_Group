import tactic
import topology.basic topology.path_connected

open classical unit_interval path
open_locale classical unit_interval
noncomputable theory

universes u v w

lemma singleton_frontier : ∀ (a : ↥I × ↥I),
                           a ∈ frontier {x : ↥I × ↥I | x.snd ≤ half} →
                           a.snd = half :=
assume a : ↥I × ↥I,
assume h : a ∈ frontier {x : ↥I × ↥I | x.snd ≤ half},
have h' : frontier {b : ↥I × ↥I | prod.snd b ≤ half} ⊆ {b : ↥I × ↥I | prod.snd b = (λ x, half) b} := 
          frontier_le_subset_eq continuous_snd continuous_const,
have ha : a ∈ {x : ↥I × ↥I | prod.snd x = half} := h' h,
ha