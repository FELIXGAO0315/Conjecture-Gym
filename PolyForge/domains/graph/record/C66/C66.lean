import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C66 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) ≤ 0) :
    (G.maxDegree : ℤ) ≤ (Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) - 5 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s1, s2, s3]
  have s5 : (G.indepNum : ℤ) ≥ 2 := by have hr := s4; omega
  have s6 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s1, s2]
  have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s5, s7]
  linarith [s8]
