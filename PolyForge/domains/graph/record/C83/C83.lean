import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C83 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.maxDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) (hn2 : (Fintype.card V : ℤ) ≥ 4) :
    (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 9 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn2]
  have s3 : (G.maxDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s6 : 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s2, s3, s4, s5]
  have s7 : (G.indepNum : ℤ) ≥ 3 := by have hr := s6; omega
  have s8 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 9 := by linarith [s1, s7]
  linarith [s8]
