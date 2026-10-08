import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C128 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hp2 : G.IsAcyclic) (hn1 : 2 * (G.maxDegree : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0) (hn2 : (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) :
    (G.chromaticNumber.toNat : ℤ) - (G.indepNum : ℤ) ≤ 0 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G hp2
    linarith [hw]
  have s3 : (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s5 : -6 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ -4 := by linarith [s1, s2, s3, s4]
  have s6 : -(G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 0 := by have hr := s5; omega
  linarith [s6]
