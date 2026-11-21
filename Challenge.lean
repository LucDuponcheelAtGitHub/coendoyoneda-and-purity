module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Category.KleisliCat
public import Mathlib.Algebra.Group.Defs

@[expose] public section

namespace CoEndoYonedaAndPurity

open CategoryTheory
open Opposite
open Functor

universe u

abbrev CYF {C : Type (u + 1)} [LargeCategory.{u} C] (Z : C) : C ⥤ Type u where
  obj Y := Z ⟶ Y
  map y2x := TypeCat.ofHom (fun z2y => z2y ≫ y2x)
  map_id _ := by
    ext z2y
    exact Category.comp_id z2y
  map_comp y2x x2w := by
    ext z2y
    exact (Category.assoc z2y y2x x2w).symm

/-- The CoYoneda endofunctor `CYEF FF Z = CYF Z ⋙ FF : C ⥤ C`. -/
abbrev CYEF {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C) (Z : C) : C ⥤ C :=
  CYF Z ⋙ FF

/-- Terminal type `T` in `Type u`. -/
abbrev T : Type u := PUnit.{u + 1}

/-- The unique element `tt*` of `T`. -/
abbrev tt_star : T := PUnit.unit

/-- The global-like endofunctor `G FF = CYEF FF (FF.obj T) : C ⥤ C`. -/
abbrev G {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C) : C ⥤ C :=
  CYEF FF (FF.obj T)

/-- Action of the functional functor `FF : Type u ⥤ C` on a function `f : Z → Y`. -/
def FF_hom {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    {Z Y : Type u} (f : Z → Y) : FF.obj Z ⟶ FF.obj Y :=
  FF.map (TypeCat.ofHom f)

/-- Global-like elements `g : Z → Hom[ FF.obj T , FF.obj Z ]`. -/
def g {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    {Z : Type u} (z : Z) : FF.obj T ⟶ FF.obj Z :=
  FF_hom FF (fun (_ : T) => z)

/-- `BasicFunctionalCategory C FF` packages the unit-like natural transformation `η : 𝟭 C ⟶ G FF`
    and the general parametric law `η_eq`. -/
class BasicFunctionalCategory (C : Type (u + 1)) [LargeCategory.{u} C] (FF : Type u ⥤ C) where
  η : 𝟭 C ⟶ G FF
  η_eq : ∀ (Z : Type u), η.app (FF.obj Z) = FF_hom FF (g FF (Z := Z))

/-- `FunctionalCategory C FF` extends `BasicFunctionalCategory C FF` with multiplication `μ`
and the left identity law `id_left` (`idˡ`). -/
class FunctionalCategory (C : Type (u + 1)) [LargeCategory.{u} C] (FF : Type u ⥤ C)
    extends BasicFunctionalCategory C FF where
  μ : (G FF ⋙ G FF) ⟶ G FF
  id_left : ∀ (Z : C), η.app ((G FF).obj Z) ≫ μ.app Z = 𝟙 ((G FF).obj Z)

/-- `G ∘F EF` (diagrammatically `EF ⋙ G FF`). -/
abbrev G_EF {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C) (EF : C ⥤ C) : C ⥤ C :=
  EF ⋙ G FF

/-- `CYF (FF.obj T) ∘F G` (diagrammatically `G FF ⋙ CYF (FF.obj T)`). -/
abbrev CYF_G {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C) : C ⥤ Type u :=
  G FF ⋙ CYF (FF.obj T)

/-- `CYF∘G ∘F EF` (diagrammatically `EF ⋙ CYF_G FF`). -/
abbrev CYF_G_EF {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C) (EF : C ⥤ C) :
    C ⥤ Type u :=
  EF ⋙ CYF_G FF

/-- `fft2cyefz = g id : Hom[ FF.obj T , (CYEF FF Z).obj Z ]`. -/
def fft2cyefz {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C) (Z : C) :
    FF.obj T ⟶ (CYEF FF Z).obj Z :=
  g FF (𝟙 Z)

/-- Forward map `τz→fz` of the CoEndoYoneda isomorphism:
    maps a natural transformation `τz : CYEF FF Z ⟶ G_EF FF EF` to an element of
 `(CYF_G_EF FF EF).obj Z`. -/
def τz_to_fz {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    {EF : C ⥤ C} {Z : C} (τz : CYEF FF Z ⟶ G_EF FF EF) : (CYF_G_EF FF EF).obj Z :=
  fft2cyefz FF Z ≫ τz.app Z

/-- Auxiliary function `fz→ay→z2y→fft2gefy` mapping `z2y : Z ⟶ Y` to
  `fz ≫ (G_EF FF EF).map z2y`. -/
def fz_to_ay_to_z2y_to_fft2gefy {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    {EF : C ⥤ C} {Z : C} (fz : (CYF_G_EF FF EF).obj Z) (Y : C) (z2y : Z ⟶ Y) :
    FF.obj T ⟶ (G_EF FF EF).obj Y :=
  fz ≫ (G_EF FF EF).map z2y

/-- Object component `fz→τz-hom` of the backward map of the CoEndoYoneda isomorphism. -/
def fz_to_τz_hom {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [FunctionalCategory C FF] {EF : C ⥤ C} {Z : C}
    (fz : (CYF_G_EF FF EF).obj Z) (Y : C) :
    (CYEF FF Z).obj Y ⟶ (G_EF FF EF).obj Y :=
  FF_hom FF (fz_to_ay_to_z2y_to_fft2gefy FF fz Y) ≫ FunctionalCategory.μ.app (EF.obj Y)

/-- In `UniversalOriginOfEta`, `ηFFT` is the image of the identity natural transformation
    `𝟙 (G FF)` under the forward map `τz_to_fz` for `EF = 𝟭 C` and `Z = FF.obj T`. -/
def ηFFT {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C) :
    FF.obj T ⟶ (G FF).obj (FF.obj T) :=
  τz_to_fz FF (EF := 𝟭 C) (Z := FF.obj T) (𝟙 (G FF))

/-- An `Idempotent` monad satisfies `mMap mPure mz = mPure mz` for all `mz : M Z`. -/
class Idempotent (M : Type u → Type u) [Monad M] : Prop where
  idempotent : ∀ {Z : Type u} (mz : M Z), (pure <$> mz) = (pure mz : M (M Z))

/-- `IsPure M` (enforcing purity) states that `(mz >>= (pure ∘ pure)) = pure mz` for all
    `mz : M Z`. -/
class IsPure (M : Type u → Type u) [Monad M] : Prop where
  enforcingPurity : ∀ {Z : Type u} (mz : M Z),
    (mz >>= ((pure : M Z → M (M Z)) ∘ (pure : Z → M Z))) = (pure mz : M (M Z))

/-- The canonical identity-on-objects functional functor
    `KFF : Type u ⥤ KleisliCat M`. -/
def KFF (M : Type u → Type u) [Monad M] [LawfulMonad M] : Type u ⥤ KleisliCat M where
  obj Z := Z
  map f := fun z => pure (f z)
  map_id _ := by
    ext
    dsimp [CategoryStruct.id, KleisliCat.id_def]
    rfl
  map_comp _ _ := by
    ext
    dsimp [CategoryStruct.comp, KleisliCat.comp_def, Bind.kleisliRight]
    rw [pure_bind]
    rfl

/-- `KleisliBasicFunctionalCategory M` is `BasicFunctionalCategory
    (KleisliCat M) (KFF M)`. -/
abbrev KleisliBasicFunctionalCategory (M : Type u → Type u) [Monad M] [LawfulMonad M] :=
  BasicFunctionalCategory (KleisliCat M) (KFF M)

/-- `MonadicTerminalTypeSubSingleton M` states that every terminal computation `mt : M T`
is equal to `pure tt_star`. -/
class MonadicTerminalTypeSubSingleton (M : Type u → Type u) [Monad M] : Prop where
  monadic_terminal_type_sub_singleton : ∀ (mt : M T), mt = pure tt_star

/-- `List` monad instance (`pure z = [z]`, `zs >>= f = zs.flatMap f`). -/
instance instMonadList : Monad List where
  pure z := [z]
  bind zs z_to_my := zs.flatMap z_to_my

/-- The `Read R` (Reader) monad `R → Z`. -/
def Read (R Z : Type u) : Type u := R → Z

instance instMonadRead (R : Type u) : Monad (Read R) where
  pure z := fun _ => z
  bind m z_to_ry := fun r => z_to_ry (m r) r

/-- The `Write W` (Writer) monad `Z × W` over a monoid `W`. -/
def Write (W Z : Type u) : Type u := Z × W

instance instMonadWrite (W : Type u) [Monoid W] : Monad (Write W) where
  pure z := (z, 1)
  bind mz z_to_wy :=
    let (y, w) := z_to_wy mz.1
    (y, mz.2 * w)

/-- The `State S` monad `S → Z × S`. -/
def State (S Z : Type u) : Type u := S → Z × S

instance instMonadState (S : Type u) : Monad (State S) where
  pure z := fun s => (z, s)
  bind mz z_to_sy := fun s =>
    let (z, s') := mz s
    z_to_sy z s'

/-- The `Cont R` (Continuation) monad `(Z → R) → R`. -/
def Cont (R Z : Type u) : Type u := (Z → R) → R

instance instMonadCont (R : Type u) : Monad (Cont R) where
  pure z := fun k => k z
  bind mz z_to_my := fun k => mz (fun z => z_to_my z k)

/-- The `ErrorState E S` monad `S → (E × S) ⊕ (Z × S)` simulating `IO`. -/
def ErrorState (E S Z : Type u) : Type u := S → (E × S) ⊕ (Z × S)

instance instMonadErrorState (E S : Type u) : Monad (ErrorState E S) where
  pure z := fun s => Sum.inr (z, s)
  bind mz z_to_my := fun s =>
    match mz s with
    | Sum.inl err => Sum.inl err
    | Sum.inr (z, s') => z_to_my z s'

/-!
## Main Theorems
-/

theorem η_eq_T {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [BasicFunctionalCategory C FF] :
    (BasicFunctionalCategory.η (C := C) (FF := FF)).app (FF.obj T) =
      g FF (g FF tt_star) := by
  sorry

theorem fz_to_τz_commute {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [FunctionalCategory C FF] {EF : C ⥤ C} {Z Y X : C}
    (fz : (CYF_G_EF FF EF).obj Z) (y2x : Y ⟶ X) :
    (CYEF FF Z).map y2x ≫ fz_to_τz_hom FF fz X =
      fz_to_τz_hom FF fz Y ≫ (G_EF FF EF).map y2x := by
  sorry

theorem to_from_proof_hom {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [FunctionalCategory C FF] {EF : C ⥤ C} {Z : C} (fz : (CYF_G_EF FF EF).obj Z) :
    fft2cyefz FF Z ≫ fz_to_τz_hom FF fz Z = fz := by
  sorry

theorem from_to_proof' {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [FunctionalCategory C FF] {EF : C ⥤ C} {Z : C}
    (τz : CYEF FF Z ⟶ G_EF FF EF) (Y : C) :
    fz_to_τz_hom FF (τz_to_fz FF τz) Y = τz.app Y := by
  sorry

theorem ηFFT_is_η_at_FFT {C : Type (u + 1)} [LargeCategory.{u} C] (FF : Type u ⥤ C)
    [BasicFunctionalCategory C FF] :
    ηFFT FF = (BasicFunctionalCategory.η (C := C) (FF := FF)).app (FF.obj T) := by
  sorry

theorem set_is_functional_category :
    Nonempty (FunctionalCategory (Type u) (𝟭 (Type u))) := by
  sorry

theorem idempotent_iff_isPure (M : Type u → Type u) [Monad M] [LawfulMonad M] :
    Idempotent M ↔ IsPure M := by
  sorry

theorem kleisliBasicFunctionalCategory_iff_idempotent
    (M : Type u → Type u) [Monad M] [LawfulMonad M] :
    Nonempty (KleisliBasicFunctionalCategory M) ↔ Idempotent M := by
  sorry

theorem isPure_implies_monadicTerminalTypeSubSingleton
    (M : Type u → Type u) [Monad M] [LawfulMonad M]
    (ep : IsPure M) : MonadicTerminalTypeSubSingleton M := by
  sorry

theorem maybe_not_pure : ¬ IsPure (Option : Type u → Type u) := by
  sorry

theorem list_not_pure : ¬ IsPure (List : Type u → Type u) := by
  sorry

theorem read_purity_implies (R : Type u) :
    IsPure (Read R) → Subsingleton R := by
  sorry

theorem write_purity_implies (W : Type u) [Monoid W] :
    IsPure (Write W) → Subsingleton W := by
  sorry

theorem state_purity_implies (S : Type u) :
    IsPure (State S) → Subsingleton S := by
  sorry

theorem cont_purity_implies (R : Type u) :
    IsPure (Cont R) → Subsingleton R := by
  sorry

theorem io_not_pure {E S : Type u} (e : E) (s : S) :
    ¬ IsPure (ErrorState E S) := by
  sorry

end CoEndoYonedaAndPurity
