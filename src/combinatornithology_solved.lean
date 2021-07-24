-- Happy π-Approximation Day (22/7)!    

/-
  These logic puzzles are mainly inspired by the ones in the book 
  "To Mock a Mockingbird", written by Raymond Smullyan.
-/

namespace enchantedforest

  namespace introduction
    /-
    A certain enchanted forest in a mystical land far away 
    is inhabited by talking birds.
    -/

    -- all birds in the enchanted forest belong to the type `Bird`
    -- a `Type` can be thought of as being similar to a `Set`
    constant Bird : Type 

    /-
    Given any birds `A` and `B`, if the name of bird `B` is called out to `A`, 
    then `A` responds with the name of another bird.
    -/

    -- `response A B` is the response of Bird `A` on hearing Bird `B`'s name
    constant response : Bird → Bird → Bird

    -- better notation for denoting response
    -- the operator is left-associative
    -- the `◁` symbol (typed as `\lhd`) resembles an ear/beak
    infix `◁`:100 := response

  end introduction

  open introduction

  namespace forestcompositionaxiom
    /-
    Given any birds `A`, `B`, `C`, the bird `C` is said to *compose* 
    `A` with `B` if for every bird `x`, the following condition holds
                      (C ◁ x) = (A ◁ (B ◁ x))

    This part of the forest has the property that for any two birds
    `A` and `B`, there is a third bird `C` that composes `A` with `B`.
    -/

    -- composition of birds, implemented as a function similar to `response`
    constant compose : Bird → Bird → Bird
    -- notation for composition
    infixr `∘` := compose
    -- the definition of composition
    axiom composition (A B : Bird) : ∀ {x : Bird}, (A ∘ B) ◁ x = A ◁ (B ◁ x)
  end forestcompositionaxiom

  /-
  Two birds `A` and `B` form an *agreeable pair* if there is another bird `x`
  that they agree on, i.e., if their responses on hearing the name `x` are the same.
  (or in symbols,  (A ◁ x) = (B ◁ x))

  A bird `A` is *agreeable* if it forms an agreeable pair with every other bird `B`.
  -/

  -- the definition of agreeable birds
  def agreeable_pair (A B : Bird) := ∃ x, A ◁ x = B ◁ x
  def is_agreeable (A : Bird) := ∀ β, agreeable_pair A β

  section agreeable_theorems

    open forestcompositionaxiom -- assume the composition law holds

    -- For birds `A` and `B`, if `C = A ∘ B` is agreeable,
    -- then so is `A`. 
    theorem agreeable_composition
        {A B C : Bird}
        (composition_hypothesis : C = A ∘ B)
        (agreeability_hypothesis : is_agreeable C) 
        :
        is_agreeable A :=
    begin
      unfold is_agreeable at *,
      unfold agreeable_pair at *,

      intro β,
      rw composition_hypothesis at agreeability_hypothesis,

      cases (agreeability_hypothesis (β ∘ B)) with w h,
      
      existsi (B ◁ w),
      rw composition at h,
      rw composition at h,
      exact h,
    end

  end agreeable_theorems

  namespace mockingbird
    /-
      A *mockingbird* is a kind of bird whose response to any bird `x`
      is exactly the response of `x` to itself.

      https://en.wikipedia.org/wiki/Mockingbird
    -/

    -- the definition of a mockingbird
    constant M : Bird
    constant M.call (x : Bird) : M ◁ x = x ◁ x
  end mockingbird

  /-
  A bird `A` is said to be *fond* of another bird `B` if
  the bird `A` responds to the name `B` with the same name `B`.
  -/

  -- the definition of fondness
  def is_fond_of (A B : Bird) := A ◁ B = B

  /-
  A bird `E` is called *egocentric* if it is fond of itself.
  -/

  -- the definition of egocentricity
  def is_egocentric (E : Bird) := E ◁ E = E

  section mockingbird_theorems
    open mockingbird 

    -- The mockingbird is agreeable.
    theorem mockingbird_agreeable : is_agreeable M :=
    begin
      unfold is_agreeable,
      unfold agreeable_pair,

      intro β,
      existsi β,
      rw M.call,
    end

    open forestcompositionaxiom

    -- If a mockingbird is in the forest and the composition law holds, 
    -- then every bird is fond of at least one bird.
    theorem mockingbird_induces_fondness : ∀ A, ∃ (B : Bird), is_fond_of A B :=
    begin
      intro A,
      unfold is_fond_of,

      existsi ((A ∘ M) ◁ (A ∘ M)), -- this is similar to the Y-combinator

      conv
      begin
        to_rhs,
        rw composition,
        rw M.call,
      end,
    end

    open forestcompositionaxiom

    -- If the composition law holds and a mockingbird is in the forest,
    -- then there is a bird that is egocentric.
    theorem exists_egocentric : ∃ E, is_egocentric E :=
    begin
      unfold is_egocentric,
      cases (mockingbird_induces_fondness M) with E h,
      existsi E,
      rw is_fond_of at h,
      rw M.call at h,
      exact h,
    end
  end mockingbird_theorems

  /-
  A bird `B` is called *hopelessly egocentric* if
  for every bird `x`, `B ◁ x = B`. 
  -/

  -- the definition of hopeless egocentricity
  def is_hopelessly_egocentric (B : Bird) := ∀ x, B ◁ x = B

  /-
  More generally, a bird `A` is *fixated* on a bird `B` if
  for every bird `x`, the response of `A` on hearing `x` is `B`.

  Thus a hopelessly egocentric bird is one that is fixated on itself.
  -/

  -- the definition of fixatedness
  def is_fixated_on (A B : Bird) := ∀ x, A ◁ x = B

  namespace kestrel
    /-
      A bird `K` is a *kestrel* if for any bird `x`,
      the bird `K ◁ x` is fixated on `x`.

      https://en.wikipedia.org/wiki/Kestrel
    -/

    -- the definition of a kestrel
    constant K : Bird
    constant K.call : ∀ (x y : Bird), (K ◁ x) ◁ y = x
  end kestrel

  section kestrel_theorems
    open kestrel

    -- An egocentric kestrel must be hopelessly egocentric.
    theorem kestrel_egocentrism (kestrel_egocentric : is_egocentric K) : 
      (is_hopelessly_egocentric K) :=
    begin
      unfold is_hopelessly_egocentric,
      intro β,
      unfold is_egocentric at kestrel_egocentric,
      
      calc (K ◁ β) = (K ◁ β) : by refl
      ...          = (K ◁ K) ◁ β : by rw kestrel_egocentric
      ...          = K : by rw K.call,
    end

    -- The left cancellation law for kestrels.
    theorem kestrel_left_cancellation 
      (x y : Bird) 
      (kestrel_application : (K ◁ x) = (K ◁ y)) :
      (x = y) :=
    begin
      calc x = (K ◁ x) ◁ K : by rw K.call
      ...    = (K ◁ y) ◁ K : by rw kestrel_application
      ...    = y : by rw K.call,
    end

    -- For an arbitrary bird `x`, if `K` is fond of `K ◁ x`,
    -- then `K` is fond of `x`.
    theorem kestrel_fondness 
      (x : Bird)
      (fond_Kx : is_fond_of K (K ◁ x)) :
      is_fond_of K x :=
    begin
      rw is_fond_of at *,
      calc K ◁ x = K ◁ (K ◁ x) ◁ K : by rw K.call
      ...        = (K ◁ x) ◁ K : by rw fond_Kx
      ...        =  x : by rw K.call,
    end
  end kestrel_theorems

  namespace identitybird
    /-
      If the name of a bird `x` is called out to the identity bird `I`,
      it responds with just `x`.

      This bird is sometimes called the "Ibis", or also (rather rudely) as the
      "idiot bird".

      https://en.wikipedia.org/wiki/Ibis
    -/

    -- the definition of the identity bird
    constant I : Bird
    constant I.call : ∀ (x : Bird), (I ◁ x) = x
  end identitybird

  section identitybird_theorems
    open identitybird

    -- If the forest contains an identity bird `I` that is agreeable,
    -- then every bird is fond of at least one bird.
    -- This does not rely on the composition axiom.
    theorem agreeable_identity_induces_fondness 
      (I_agreeable : is_agreeable I) :
      ∀ B, ∃ x, is_fond_of B x :=
    begin
      unfold is_agreeable at I_agreeable,
      intro β,
      unfold agreeable_pair at I_agreeable,
      unfold is_fond_of,

      cases (I_agreeable β),
      existsi w,
      rw I.call at h,
      apply eq.symm,
      exact h,
    end

    -- If every bird is fond of at least one bird, then
    -- the identity bird must be agreeable.
    theorem fondness_induces_agreeable_identity
      (all_birds_fond : ∀ B, ∃ x, is_fond_of B x) :
      is_agreeable I :=
    begin
      unfold is_agreeable,
      unfold is_fond_of at all_birds_fond,

      intro β,
      rw agreeable_pair,
      cases (all_birds_fond β),
      existsi w,
      rw I.call,
      rw h,
    end
  end identitybird_theorems

  namespace lark
    /-
      The *lark* `L` is a bird which, on hearing the name of an
      arbitrary bird `x`, calls out the name of the bird that
      composes `x` with the mockingbird `M`.

      https://en.wikipedia.org/wiki/Lark
    -/

    -- the definition of a lark
    constant L : Bird
    constant L.call : ∀ (x y : Bird), (L ◁ x) ◁ y = x ◁ (y ◁ y)
  end lark

  section lark_theorems
    open lark

    -- DIY: Show that the presence of a just lark
    -- (with no additional known birds or conditions)
    -- implies the presence of an egocentric bird.
    theorem lark_implies_egocentric : ∃ E, is_egocentric E :=
    begin
      sorry,
    end
  end lark_theorems

  namespace bluebird
    /-
      The *bluebird* `B` is a bird that can perform composition.

      For birds `x`, `y`, `z`, the following property holds:
            `(((B ◁ x) ◁ y) ◁ z) = x ◁ (y ◁ z)`

      https://en.wikipedia.org/wiki/Bluebird
    -/

    -- the definition of a bluebird
    constant B : Bird
    constant B.call : ∀ (x y z : Bird), (((B ◁ x) ◁ y) ◁ z) = x ◁ (y ◁ z)
  end bluebird

  section bluebird_theorems
    open bluebird
    open forestcompositionaxiom

    -- The bluebird is capable of composing one bird with another.
    theorem bluebird_composition (x y : Bird) :
      ∀ z : Bird, ((B ◁ x) ◁ y) ◁ z = (x ∘ y) ◁ z :=
    begin
      intro z,
      rw B.call,
      rw composition,
    end

    open mockingbird

    -- If a mockingbird and a bluebird are in the forest,
    -- for every bird `A` in the forest, one can contruct a
    -- bird `β` using bird calls such that `A` is fond of `β`.
    theorem all_birds_fond : ∀ A, ∃ β, is_fond_of A β :=
    begin
      intro A,
      existsi (B ◁ A ◁ M) ◁ (B ◁ A ◁ M),
      unfold is_fond_of,
      conv
      begin
        to_rhs,
        rw B.call,
        rw M.call,
      end,
    end

  end bluebird_theorems

  namespace starling
    /-
      A *starling* is a bird `S` that satisfies the following condition
          `(((S ◁ x) ◁ y) ◁ z) = (x ◁ z) ◁ (y ◁ z)`

      https://en.wikipedia.org/wiki/Starling
    -/

    -- definition of the starling
    constant S : Bird
    constant S.call : ∀ (x y z : Bird), (((S ◁ x) ◁ y) ◁ z) = (x ◁ z) ◁ (y ◁ z)
  end starling

  section summoning_a_sagebird
    /-
      According to folklore, a *sagebird* or an *oracle bird* `Θ` is
      believed to have the property that if the name of any bird `x` is 
      called out to `θ`, it responds with the name of a bird that `x` is fond of.
    
      Interestingly, the existence of a sagebird can be deduced from the birds
      encountered so far.
    -/
  
    -- adding all the known birds
    open mockingbird
    open kestrel
    open identitybird
    open lark
    open bluebird
    open starling

    -- a sage bird exists in the forest
    theorem sagebird_existence_simple :
      ∃ θ, ∀ x, x ◁ (θ ◁ x) = θ ◁ x :=
    begin
      existsi (S ◁ L ◁ L),
      intro x,
      rw S.call,
      conv
      begin
        to_rhs,
        rw L.call,
      end,
    end
  end summoning_a_sagebird

  namespace vireo
    /-
      A *vireo* `V` is a bird that has the property that
      for arbitrary birds `x`, `y` and `z`, the following holds

      ((V ◁ x) ◁ y) ◁ z = z ◁ (x ◁ y)

      https://en.wikipedia.org/wiki/Vireo
    -/

    constant V : Bird
    constant V.call : ∀ (x y z : Bird), V ◁ x ◁ y ◁ z = z ◁ x ◁ y
  end vireo

end enchantedforest

/-
  # To-do:
  - the star(t)ling fact that `S` and `K` form a complete basis
  - Ornithologic
  - Avian arithmetic
-/

/-
  # References:

  1. "To Mock a Mockingbird", by Raymond Smullyan (https://en.wikipedia.org/wiki/To_Mock_a_Mockingbird)
  2. "To Dissect a Mockingbird", by David Keenan (https://dkeenan.com/Lambda/index.htm)
  3. SKI Combinator calculus (https://en.wikipedia.org/wiki/SKI_combinator_calculus)
-/