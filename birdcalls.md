# Bird calls in the enchanted forest

## Introduction

A certain enchanted forest in a mystical land far away is inhabited by talking birds.

Given any birds `A` and `B`, if the name of bird `B` is called out to `A`, then `A` responds with the name of another bird. The name of the bird that `A` calls out on hearing the name of `B` is written as `A ◁ B`.

## Mockingbirds (M)

### Description

A *mockingbird* is a kind of bird whose response to any bird `x`
is exactly the response of `x` to itself.

https://en.wikipedia.org/wiki/Mockingbird

### Call

∀ x, M ◁ x = x ◁ x

## Kestrels (K)

### Description

A bird `K` is a *kestrel* if for any bird `x`,
the bird `K ◁ x` is fixated on `x`.

https://en.wikipedia.org/wiki/Kestrel

### Call

∀ (x y : Bird), (K ◁ x) ◁ y = x

## Ibises / Identity Birds (I)

### Description

If the name of a bird `x` is called out to the identity bird `I`,
it responds with just `x`.

This bird is sometimes called the "Ibis", or also (rather rudely) as the
"idiot bird".

https://en.wikipedia.org/wiki/Ibis

### Call

∀ (x : Bird), (I ◁ x) = x

## Larks (L)

### Description

The *lark* `L` is a bird which, on hearing the name of an
arbitrary bird `x`, calls out the name of the bird that
composes `x` with the mockingbird `M`.

https://en.wikipedia.org/wiki/Lark

### Call

∀ (x y : Bird), (L ◁ x) ◁ y = x ◁ (y ◁ y)

## Bluebirds (B)

### Description

The *bluebird* `B` is a bird that can perform composition.

For birds `x`, `y`, `z`, the following property holds:
    `(((B ◁ x) ◁ y) ◁ z) = x ◁ (y ◁ z)`

https://en.wikipedia.org/wiki/Bluebird

### Call

∀ (x y z : Bird), (((B ◁ x) ◁ y) ◁ z) = x ◁ (y ◁ z)

## Starlings (S)

### Description

A *starling* is a bird `S` that satisfies the following condition
`(((S ◁ x) ◁ y) ◁ z) = (x ◁ z) ◁ (y ◁ z)`. A starling distributes
the call of `z` between `x` and `y`.

https://en.wikipedia.org/wiki/Starling

### Call

∀ (x y z : Bird), (((S ◁ x) ◁ y) ◁ z) = (x ◁ z) ◁ (y ◁ z)

## Sage birds (Θ)

### Description

According to folklore, a *sagebird* or an *oracle bird* `Θ` is
believed to have the property that if the name of any bird `x` is 
called out to `θ`, it responds with the name of a bird that `x` is fond of.

### Call

∀ x, x ◁ (θ ◁ x) = θ ◁ x

---
