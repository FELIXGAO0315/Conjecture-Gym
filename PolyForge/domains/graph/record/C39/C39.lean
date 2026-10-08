import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C39 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0) :
    2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s2 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s4 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s6 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s3, s1, s4, s5]
  have s7 : (G.indepNum : ℤ) ≥ 2 := by have hr := s6; omega
  have s8 : 2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s1, s2, s7]
  linarith [s8]
