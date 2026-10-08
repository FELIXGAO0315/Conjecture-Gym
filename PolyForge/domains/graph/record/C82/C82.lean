import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C82 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : 2 * (G.minDegree : ℤ) - (G.indepNum : ℤ) ≥ 0) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≥ 3) :
    2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s2 : (G.indepNum : ℤ) ≥ 0 := by positivity
  have s3 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn2]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3, s4]
  have s6 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s7 : 2 * (G.minDegree : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s8 : 2 * (G.minDegree : ℤ) ≥ 1 := by linarith [s6, s7]
  have s9 : (G.minDegree : ℤ) ≥ 1 := by have hr := s8; omega
  have s10 : 2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s1, s9]
  linarith [s10]
