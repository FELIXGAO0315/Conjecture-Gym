import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C69 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.diam : ℤ) ≥ 0) (hn2 : (G.maxDegree : ℤ) ≤ 4) :
    (G.indepNum : ℤ) + (G.diam : ℤ) + (G.radius.toNat : ℤ) ≥ 3 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s5 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.diam : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : 2 * (G.diam : ℤ) ≥ 1 := by linarith [s4, s5]
  have s7 : (G.diam : ℤ) ≥ 1 := by have hr := s6; omega
  have s8 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    linarith [hw]
  have s9 : 4 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s8, s4, s5]
  have s10 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s9; omega
  have s11 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
    have hw := tau_le_card_sub_one_int G (by omega)
    linarith [hw]
  have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s13 : (G.indepNum : ℤ) + (G.diam : ℤ) + (G.radius.toNat : ℤ) ≥ 3 := by linarith [s7, s10, s11, s12]
  linarith [s13]
