import OmegaBound.ADVXXZGeneralGridFull

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private abbrev ChunkCountCode {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (r : Fin 6) (u : Shape w) :=
  Chunk w → Fin ((n*g.joint.prob (r,u)).floor.toNat + 1)

private abbrev ShapeCountCode {w : ℕ} (g : GlobalSpec w) (n : ℕ) (r : Fin 6) :=
  (u : Shape w) → ChunkCountCode g n r u

private abbrev RegionCountCode {w : ℕ} (g : GlobalSpec w) (n : ℕ) :=
  (r : Fin 6) → ShapeCountCode g n r

private abbrev ExactGridCode {w : ℕ} (g : GlobalSpec w) (n : ℕ) :=
  Side → RegionCountCode g n

private noncomputable def fintypeChunkCountCode {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (r : Fin 6) (u : Shape w) : Fintype (ChunkCountCode g n r u) := inferInstance

private noncomputable def fintypeShapeCountCode {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (r : Fin 6) : Fintype (ShapeCountCode g n r) :=
  @Pi.instFintype (Shape w) (fun u => ChunkCountCode g n r u) inferInstance inferInstance
    (fun u => fintypeChunkCountCode g n r u)

private noncomputable def fintypeRegionCountCode {w : ℕ} (g : GlobalSpec w) (n : ℕ) :
    Fintype (RegionCountCode g n) :=
  @Pi.instFintype (Fin 6) (fun r => ShapeCountCode g n r) inferInstance inferInstance
    (fun r => fintypeShapeCountCode g n r)

private noncomputable def fintypeExactGridCode {w : ℕ} (g : GlobalSpec w) (n : ℕ) :
    Fintype (ExactGridCode g n) :=
  @Pi.instFintype Side (fun _ => RegionCountCode g n) inferInstance inferInstance
    (fun _ => fintypeRegionCountCode g n)

private def exactGridCode {w : ℕ} (g : GlobalSpec w) (n : ℕ) (ξ : ExactGrid g n) :
    ExactGridCode g n :=
  fun W r u σ => ⟨ξ.count W r u σ, by
    rw [Nat.lt_succ_iff, ← ξ.total W r u]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)⟩

noncomputable instance instFintypeExactGrid {w : ℕ} (g : GlobalSpec w) (n : ℕ) :
    Fintype (ExactGrid g n) := by
  letI : Fintype (ExactGridCode g n) := fintypeExactGridCode g n
  exact Fintype.ofInjective (exactGridCode g n) (by
    intro ξ η h
    cases ξ with
    | mk countξ totalξ gradedξ =>
      cases η with
      | mk countη totalη gradedη =>
        have hc : countξ = countη := by
          funext W r u σ
          exact congrArg Fin.val
            (congrFun (congrFun (congrFun (congrFun h W) r) u) σ)
        cases hc
        rfl)


noncomputable instance instFintypeFullGrid {w : ℕ} (g : GlobalSpec w) (n : ℕ) (ε : ℚ) :
    Fintype (FullGrid g n ε) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

end OmegaBound.ADVXXZGeneral
end
