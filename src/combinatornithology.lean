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
    -- the ` ◁ ` symbol (typed as `\lhd`) resembles an ear/beak
    infix ` ◁ ` : 100 := response

  end introduction

  open introduction


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
    constant I.call : ∀ x : Bird, (I ◁ x) = x
    
  end identitybird


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
  notation [parsing_only] E ` is_egocentric` := E ◁ E = E

  section defending_the_identitybird
    open identitybird

    /-
      Students of Combinatornithology sometimes rudely referred to the
      identity bird as the "idiot bird", because of its apparent simplicity.

      The theorems in this section show why the identity bird is actually quite
      intelligent.
    -/

    -- The identity bird is fond of every bird.
    theorem identity_fond_of_all : ∀ x : Bird, I is_fond_of x :=
    begin
      sorry
    end

    -- The identity bird is egocentric.
    theorem identity_egocentric : I is_egocentric :=
    begin
      sorry
    end

    /-
      The identity bird has an unusually large heart! It is fond of every bird.

      It is also egocentric, but it is fond of itself no more than it is of any
      other bird.
    -/
  end defending_the_identitybird

  /-
  A bird `B` is called *hopelessly egocentric* if
  for every bird `x`, `B ◁ x = B`. 
  -/

  -- the definition of hopeless egocentricity
  notation [parsing_only] B ` is_hopelessly_egocentric` := ∀ x, B ◁ x = B

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

    -- For any bird `x`, the bird `K ◁ x` is fixated on `x`.
    theorem k_x_fixated_on_x : ∀ x, K ◁ x is_fixated_on x :=
    begin
      sorry
    end

    -- An egocentric kestrel must be hopelessly egocentric.
    theorem kestrel_egocentrism 
      (kestrel_egocentric : K is_egocentric) : 
      (K is_hopelessly_egocentric) :=
    begin
      sorry
    end

    -- The left cancellation law for kestrels.
    theorem kestrel_left_cancellation 
      (x y : Bird) 
      (kestrel_application : (K ◁ x) = (K ◁ y)) :
      (x = y) :=
    begin
      sorry
    end

    -- `*` For an arbitrary bird `x`, if `K` is fond of `K ◁ x`,
    -- then `K` is fond of `x`.
    theorem kestrel_fondness 
      (x : Bird)
      (fond_Kx : K is_fond_of (K ◁ x)) :
      K is_fond_of x :=
    begin
      sorry,
    end
  end kestrel_theorems

  /-
  Two birds `A` and `B` form an *agreeable pair* if there is another bird `x`
  that they agree on, i.e., if their responses on hearing the name `x` are the same.
  (or in symbols,  (A ◁ x) = (B ◁ x))

  A bird `A` is *agreeable* if it forms an agreeable pair with every other bird `B`.
  -/

  -- the definition of agreeable birds

  notation [parsing_only] A ` is_agreeable_with ` B := (∃ x : Bird, A ◁ x = B ◁ x)
  notation [parsing_only] A ` is_agreeable` := ∀ β : Bird, A is_agreeable_with β

  section identitybird_theorems
    open identitybird

    -- If the forest contains an identity bird `I` that is agreeable,
    -- then every bird is fond of at least one bird.
    -- This does not rely on the composition axiom.
    theorem agreeable_identity_induces_fondness 
      (I_agreeable : I is_agreeable) :
      ∀ B, ∃ x, B is_fond_of x :=
    begin
      sorry
    end

    -- `*` If every bird is fond of at least one bird, then
    -- the identity bird must be agreeable.
    theorem fondness_induces_agreeable_identity
      (all_birds_fond : ∀ B, ∃ x, B is_fond_of x) :
      I is_agreeable :=
    begin
      sorry
    end
  end identitybird_theorems


  namespace mockingbird
    /-
      A *mockingbird* is a kind of bird whose response to any bird `x`
      is exactly the response of `x` to itself.

      https://en.wikipedia.org/wiki/Mockingbird
    -/

    -- the definition of a mockingbird
    constant M : Bird
    constant M.call : ∀ x, M ◁ x = x ◁ x

  end mockingbird

  namespace forestcompositionlaw
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
    infixr ` ∘ ` := compose
    -- the definition of composition
    axiom composition (A B : Bird) : ∀ {x : Bird}, (A ∘ B) ◁ x = A ◁ (B ◁ x)

  end forestcompositionlaw

  section mockingbird_theorems
    open mockingbird 

    -- The mockingbird is agreeable.
    theorem mockingbird_agreeable : M is_agreeable :=
    begin
      sorry
    end

    open forestcompositionlaw

    -- If a mockingbird is in the forest and the composition law holds, 
    -- then every bird is fond of at least one bird.
    theorem mockingbird_induces_fondness : ∀ A, ∃ B, A is_fond_of B :=
    begin
      intro A,

      existsi ((A ∘ M) ◁ (A ∘ M)),

      conv
      begin
        to_rhs,
      end,
      sorry,
    end

    -- If the composition law holds and a mockingbird is in the forest,
    -- then there is a bird that is egocentric.
    theorem exists_egocentric : ∃ E, E is_egocentric :=
    begin
      sorry,
    end

    -- `*` If `A` is an agreeable bird and the composition law holds,
    -- every bird is fond of at least one bird.
    theorem agreeability_induces_fondness 
      (α : Bird)
      (α_agreeable : α is_agreeable)
      : ∀ A, ∃ B, A is_fond_of B :=
    begin
      sorry
    end

    -- A proof of the earlier theorem as a corollary of the previous one.
    theorem mockingbird_agreeable_fondness : ∀ A, ∃ B, A is_fond_of B :=
    begin
      exact (agreeability_induces_fondness M mockingbird_agreeable)
    end

  end mockingbird_theorems

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
    open forestcompositionlaw

    -- The bluebird is capable of composing one bird with another.
    theorem bluebird_composition (x y : Bird) :
      ∀ z : Bird, ((B ◁ x) ◁ y) ◁ z = (x ∘ y) ◁ z :=
    begin
      sorry
    end

    open mockingbird

    -- If a mockingbird and a bluebird are in the forest,
    -- for every bird `A` in the forest, one can contruct a
    -- bird `β` using bird calls such that `A` is fond of `β`.
    theorem all_birds_fond : ∀ A, ∃ β, A is_fond_of β :=
    begin
      sorry
    end

  end bluebird_theorems

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

  namespace lark_theorems
    open lark

    -- `*` Every bird is fond of a hopelessly egocentric lark.
    theorem egocentric_lark_popular
      (egocentric_lark : L is_egocentric) :
      ∀ β, β is_fond_of L :=
    begin
      sorry
    end
    
  end lark_theorems

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

  section starling_theorems
    open starling
    open kestrel

    /-
      The existence of a Starling and a Kestrel in the forest is
      sufficient to imply the existence of several other birds.
    -/

    -- Derive the identity bird.
    

    -- Derive the mockingbird.


    -- `*` Derive the bluebird.


  end starling_theorems

  section summoning_a_sagebird
    /-
      According to folklore, a *sagebird* or an *oracle bird* `Θ` is
      believed to have the property that if the name of any bird `x` is 
      called out to `θ`, it responds with the name of a bird that `x` is fond of.
    
      Interestingly, the existence of a sagebird can be deduced from the birds
      encountered so far.
    -/
  
    -- adding all the known birds
    open identitybird
    open kestrel
    open mockingbird
    open bluebird
    open lark
    open starling

    -- a sage bird exists in the forest
    theorem sagebird_existence :
      ∃ θ, ∀ x, x ◁ (θ ◁ x) = θ ◁ x :=
    begin
      sorry,
    end  
  end summoning_a_sagebird

end enchantedforest

  /-
    A star~t~ling fact:

    All birds can be derived from just the 
    kestrel (`K`) and the
    starling (`S`)!

    # The algorithm

    Define the `α-eliminate` of an expression `E` to be
    an expression `F` such that `F α = E`.
    1. The α-eliminate of `α` is `I`.
    2. If `α` does not occur in `E`, then `K E` is the
        α-eliminate.
    3. If `E` is of the form `F α`, then `F` is the
        α-eliminate of `E`.
    4. If `E = F G`, and `F'` and `G'` are the corresponding
      α-eliminates of the expressions, then 
          `S (F') (G')` is the corresponding α-eliminate.

    Repeated α-elimination of all the variables involved gives the
    expression for the bird in terms of `S` and `K`.

    For a recursive bird `U` (i.e., a bird whose call depends on itself),
    replace every occurrence of the letter `U` in the call with an unused
    variable name and solve as above. 
    
    Call this modified bird `V`. It satisfies the property `V ◁ U = U`.
    
    Since the existence of the mockingbird and the bluebird is sufficient to 
    guarantee that every bird is fond of some bird, one can find a bird `F` such that
    `V` is fond of `F`, that is, `V ◁ F = F`. But this is the property that `U` is required
    to satisfy. Thus `F`, which can be derived from `S` and `K` using the sage bird,
    is the required bird.
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
  4. The Natural Number Game (https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)
-/