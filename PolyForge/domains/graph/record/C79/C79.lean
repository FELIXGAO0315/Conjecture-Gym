import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C79 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.edgeFinset.card : ℤ) ≥ 5) (hn2 : (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0) :
    (G.maxDegree : ℤ) ≤ (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) - 3 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s5 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s1, s2, s3, s4]
  have s6 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s5; omega
  have s7 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s1, s2]
  have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s9 : -(G.maxDegree : ℤ) + (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s6, s8, s4]
  linarith [s9]
