import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C104 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) :
    2 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≤ -1 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int G (by omega)
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp1)
    linarith [hw]
  have s7 : (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s9 : -6 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ -4 := by linarith [s5, s6, s7, s8]
  have s10 : -(G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 0 := by have hr := s9; omega
  have s11 : -2 * (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 1 := by linarith [s4, s10]
  linarith [s11]
