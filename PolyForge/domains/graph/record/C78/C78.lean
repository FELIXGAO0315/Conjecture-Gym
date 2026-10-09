import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C78 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≤ 0) :
    (G.vertexCoverNum.toNat : ℤ) ≥ -2 * (Fintype.card V : ℤ) + 8 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s3 : -(G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s5 : 4 * (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 15 := by linarith [s1, s2, s3, s4]
  have s6 : 2 * (Fintype.card V : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by have hr := s5; omega
  linarith [s6]
