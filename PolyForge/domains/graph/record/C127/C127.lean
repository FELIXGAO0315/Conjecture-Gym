import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C127 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 1) (hp2 : G.IsTree) (hn1 : -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) (hn2 : (Fintype.card V : ℤ) ≥ 4) :
    (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≤ 1 := by
  have s1 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp2)
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn2]
  have s3 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int G (by omega)
    linarith [hw]
  have s4 : -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -3 := by linarith [s1, s3, s4]
  have s6 : -(G.chromaticNumber.toNat : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ -1 := by have hr := s5; omega
  linarith [s6]
