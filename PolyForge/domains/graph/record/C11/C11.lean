import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C11 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.indepNum : ℤ)) :
    (G.maxDegree : ℤ) ≤ 2 * (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) - 3 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    linarith [hw]
  have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s6 : -2 * (G.maxDegree : ℤ) + 4 * (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 5 := by linarith [s1, s2, s3, s4, s5]
  have s7 : -(G.maxDegree : ℤ) + 2 * (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by have hr := s6; omega
  linarith [s7]
