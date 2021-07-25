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

  notation [parsing_only] A ` agreeable_with ` B := (∃ x, A ◁ x = B ◁ x)
  notation [parsing_only] A `is_agreeable` := ∀ β, A agreeable_with β

  section agreeable_theorems
    -- This is the first puzzle of the game

    open forestcompositionaxiom -- assume the composition law holds
    
    -- For birds `A` and `B`, if `C = A ∘ B` is agreeable,
    -- then so is `A`. 
    theorem agreeable_composition
        {A B C : Bird}
        (composition_hypothesis : C = A ∘ B)
        (agreeability_hypothesis : C is_agreeable) 
        :
        A is_agreeable :=
    begin
      sorry,
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
  notation [parsing_only] A ` is_fond_of ` B := A ◁ B = B

  /-
  A bird `E` is called *egocentric* if it is fond of itself.
  -/

  -- the definition of egocentricity
  notation [parsing_only] E ` is_egocentric ` := E ◁ E = E

  section mockingbird_theorems
    open mockingbird 

    -- The mockingbird is agreeable.
    theorem mockingbird_agreeable : M is_agreeable :=
    begin
      sorry,
    end

    open forestcompositionaxiom

    -- If a mockingbird is in the forest and the composition law holds, 
    -- then every bird is fond of at least one bird.
    theorem mockingbird_induces_fondness : ∀ A, ∃ B, A is_fond_of B :=
    begin
      intro A,

      existsi ((A ∘ M) ◁ (A ∘ M)), -- this is similar to the Y-combinator

      conv
      begin
        to_rhs,
      end,
      sorry,
    end

    open forestcompositionaxiom

    -- If the composition law holds and a mockingbird is in the forest,
    -- then there is a bird that is egocentric.
    theorem exists_egocentric : ∃ E, E is_egocentric :=
    begin
      sorry,
    end
  end mockingbird_theorems

  /-
  A bird `B` is called *hopelessly egocentric* if
  for every bird `x`, `B ◁ x = B`. 
  -/

  -- the definition of hopeless egocentricity
  notation [parsing_only] B ` is_hopelessly_egocentric ` := ∀ x, B ◁ x = B

  /-
  More generally, a bird `A` is *fixated* on a bird `B` if
  for every bird `x`, the response of `A` on hearing `x` is `B`.

  Thus a hopelessly egocentric bird is one that is fixated on itself.
  -/

  -- the definition of fixatedness
  notation [parsing_only] A ` is_fixated_on ` B := ∀ x, A ◁ x = B

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
    theorem kestrel_egocentrism (kestrel_egocentric : K is_egocentric) : 
      (K is_hopelessly_egocentric) :=
    begin
      sorry,
    end

    -- The left cancellation law for kestrels.
    theorem kestrel_left_cancellation 
      (x y : Bird) 
      (kestrel_application : (K ◁ x) = (K ◁ y)) :
      (x = y) :=
    begin
      sorry,
    end

    -- For an arbitrary bird `x`, if `K` is fond of `K ◁ x`,
    -- then `K` is fond of `x`.
    theorem kestrel_fondness 
      (x : Bird)
      (fond_Kx : K is_fond_of (K ◁ x)) :
      K is_fond_of x :=
    begin
      sorry,
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
      (I_agreeable : I is_agreeable) :
      ∀ B, ∃ x, B is_fond_of x :=
    begin
      sorry,
    end

    -- If every bird is fond of at least one bird, then
    -- the identity bird must be agreeable.
    theorem fondness_induces_agreeable_identity
      (all_birds_fond : ∀ B, ∃ x, B is_fond_of x) :
      I is_agreeable :=
    begin
      sorry,
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
    theorem lark_implies_egocentric : ∃ E, E is_egocentric :=
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
      sorry,
    end

    open mockingbird

    -- If a mockingbird and a bluebird are in the forest,
    -- for every bird `A` in the forest, one can contruct a
    -- bird `β` using bird calls such that `A` is fond of `β`.
    theorem all_birds_fond : ∀ A, ∃ β, A is_fond_of β :=
    begin
      sorry,
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
    theorem sagebird_existence :
      ∃ θ, ∀ x, x ◁ (θ ◁ x) = θ ◁ x :=
    begin
      sorry,
    end  
  end summoning_a_sagebird

  /-
    As you leave the forest, you notice a flock of *vireos* flying by.
    It is clearly a large flock, although the exact number does not
    seem constant.
  -/
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
    A star~t~ling fact:

    All birds can be derived from just the 
    kestrel (`K`) and the
    starling (`S`)!
  -/

-- TO-DO
namespace ornithologic
end ornithologic

namespace avianarithmetic
end avianarithmetic

/-
  # References:

  1. "To Mock a Mockingbird", by Raymond Smullyan (https://en.wikipedia.org/wiki/To_Mock_a_Mockingbird)
  2. "To Dissect a Mockingbird", by David Keenan (https://dkeenan.com/Lambda/index.htm)
  3. SKI Combinator calculus (https://en.wikipedia.org/wiki/SKI_combinator_calculus)
-/
