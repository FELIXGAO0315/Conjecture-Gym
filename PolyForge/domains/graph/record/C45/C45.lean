import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C45 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : ¬ G.IsAcyclic) (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 6) (hn2 : (G.edgeFinset.card : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) :
    (G.vertexCoverNum.toNat : ℤ) ≤ 2 * (Fintype.card V : ℤ) + 2 * (G.radius.toNat : ℤ) - 9 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 6 := by linarith [hn1]
  have s3 : (Fintype.card V : ℤ) ≥ 6 := by linarith [s1, s2]
  have s4 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s5 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp1
    linarith [hw]
  have s6 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
    have hw := girth_le_diam_int G hp1 hp2
    linarith [hw]
  have s7 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp2
    linarith [hw]
  have s8 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s5, s6, s7]
  have s9 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s8; omega
  have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s11 : 2 * (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 9 := by linarith [s3, s4, s9, s10]
  linarith [s11]
