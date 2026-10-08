import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C98 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) (hn2 : (G.cliqueNum : ℤ) ≥ 3) :
    (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.cliqueNum : ℤ) ≥ 3 := by linarith [hn2]
  have s5 : -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s4, s5]
  have s7 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s6; omega
  have s8 : (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s3, s7]
  linarith [s8]
