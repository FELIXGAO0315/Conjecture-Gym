import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : -(G.cliqueNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≤ 0) (hn2 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≤ 0) :
    (G.indepNum : ℤ) ≥ -2 * (G.maxDegree : ℤ) + 5 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s2 : 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s3 : 2 * (G.maxDegree : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s3; omega
  have s5 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s5, s1]
  have s7 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s8 : 2 * (G.maxDegree : ℤ) + (G.indepNum : ℤ) ≥ 5 := by linarith [s4, s7]
  linarith [s8]
