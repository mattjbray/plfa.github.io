---
src       : "src/plfa/Induction.lagda.md"
title     : "Induction: Proof by Induction"
layout    : page
prev      : /Naturals/
permalink : /Induction/
next      : /Relations/
---

{% raw %}<pre class="Agda"><a id="146" class="Keyword">module</a> <a id="153" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html" class="Module">plfa.Induction</a> <a id="168" class="Keyword">where</a>
</pre>{% endraw %}
> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of _inductive datatypes_ are proved by
_induction_.


## Imports

We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
{% raw %}<pre class="Agda"><a id="763" class="Keyword">import</a> <a id="770" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="808" class="Symbol">as</a> <a id="811" class="Module">Eq</a>
<a id="814" class="Keyword">open</a> <a id="819" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="822" class="Keyword">using</a> <a id="828" class="Symbol">(</a><a id="829" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="832" class="Symbol">;</a> <a id="834" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="838" class="Symbol">;</a> <a id="840" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="844" class="Symbol">;</a> <a id="846" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="849" class="Symbol">)</a>
<a id="851" class="Keyword">open</a> <a id="856" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="871" class="Keyword">using</a> <a id="877" class="Symbol">(</a><a id="878" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="884" class="Symbol">;</a> <a id="886" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="891" class="Symbol">;</a> <a id="893" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="899" class="Symbol">;</a> <a id="901" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="903" class="Symbol">)</a>
<a id="905" class="Keyword">open</a> <a id="910" class="Keyword">import</a> <a id="917" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="926" class="Keyword">using</a> <a id="932" class="Symbol">(</a><a id="933" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="934" class="Symbol">;</a> <a id="936" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="940" class="Symbol">;</a> <a id="942" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="945" class="Symbol">;</a> <a id="947" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="950" class="Symbol">;</a> <a id="952" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="955" class="Symbol">;</a> <a id="957" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="960" class="Symbol">)</a>
</pre>{% endraw %}

## Properties of operators

Operators pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Identity_.   Operator `+` has left identity `0` if `0 + n ≡ n`, and
  right identity `0` if `n + 0 ≡ n`, for all `n`. A value that is both
  a left and right identity is just called an identity. Identity is also
  sometimes called _unit_.

* _Associativity_.   Operator `+` is associative if the location
  of parentheses does not matter: `(m + n) + p ≡ m + (n + p)`,
  for all `m`, `n`, and `p`.

* _Commutativity_.   Operator `+` is commutative if order of
  arguments does not matter: `m + n ≡ n + m`, for all `m` and `n`.

* _Distributivity_.   Operator `*` distributes over operator `+` from the
  left if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`, and `p`,
  and from the right if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`,
  `p`, and `q`.

Addition has identity `0` and multiplication has identity `1`;
addition and multiplication are both associative and commutative;
and multiplication distributes over addition.

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will often call
out these properties---or their lack---for instance by pointing out
that a newly introduced operator is associative but not commutative.

#### Exercise `operators` {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.

{% raw %}<pre class="Agda"><a id="2975" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Associativity

One property of addition is that it is _associative_, that is, that the
location of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

Here `m`, `n`, and `p` are variables that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables:
{% raw %}<pre class="Agda"><a id="3332" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#3332" class="Function">_</a> <a id="3334" class="Symbol">:</a> <a id="3336" class="Symbol">(</a><a id="3337" class="Number">3</a> <a id="3339" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3341" class="Number">4</a><a id="3342" class="Symbol">)</a> <a id="3344" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3346" class="Number">5</a> <a id="3348" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3350" class="Number">3</a> <a id="3352" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3354" class="Symbol">(</a><a id="3355" class="Number">4</a> <a id="3357" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3359" class="Number">5</a><a id="3360" class="Symbol">)</a>
<a id="3362" class="Symbol">_</a> <a id="3364" class="Symbol">=</a>
  <a id="3368" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="3378" class="Symbol">(</a><a id="3379" class="Number">3</a> <a id="3381" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3383" class="Number">4</a><a id="3384" class="Symbol">)</a> <a id="3386" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3388" class="Number">5</a>
  <a id="3392" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3400" class="Number">7</a> <a id="3402" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3404" class="Number">5</a>
  <a id="3408" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3416" class="Number">12</a>
  <a id="3421" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3429" class="Number">3</a> <a id="3431" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3433" class="Number">9</a>
  <a id="3437" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3445" class="Number">3</a> <a id="3447" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3449" class="Symbol">(</a><a id="3450" class="Number">4</a> <a id="3452" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3454" class="Number">5</a><a id="3455" class="Symbol">)</a>
  <a id="3459" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for _all_ the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
_proof by induction_.


## Proof by induction

Recall the definition of natural numbers consists of a _base case_
which tells us that `zero` is a natural, and an _inductive case_
which tells us that if `m` is a natural then `suc m` is also a natural.

Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need to prove two cases.
First is the _base case_, where we show the property holds for `zero`.
Second is the _inductive case_, where we assume the property holds for
an arbitrary natural `m` (we call this the _inductive hypothesis_), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis---namely that `P` holds for `m`---then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties:

    -- In the beginning, no properties are known.

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply:

    -- On the first day, one property is known.
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today:

    -- On the second day, two properties are known.
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new:

    -- On the third day, three properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))

You've got the hang of it by now:

    -- On the fourth day, four properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the _n_'th day there will be _n_ distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day _n+1_.


## Our first proof: associativity

To prove associativity, we take `P m` to be the property:

    (m + n) + p ≡ m + (n + p)

Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

If we can demonstrate both of these, then associativity of addition
follows by induction.

Here is the proposition's statement and proof:
{% raw %}<pre class="Agda"><a id="+-assoc"></a><a id="7687" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7687" class="Function">+-assoc</a> <a id="7695" class="Symbol">:</a> <a id="7697" class="Symbol">∀</a> <a id="7699" class="Symbol">(</a><a id="7700" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7700" class="Bound">m</a> <a id="7702" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7702" class="Bound">n</a> <a id="7704" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7704" class="Bound">p</a> <a id="7706" class="Symbol">:</a> <a id="7708" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7709" class="Symbol">)</a> <a id="7711" class="Symbol">→</a> <a id="7713" class="Symbol">(</a><a id="7714" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7700" class="Bound">m</a> <a id="7716" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7718" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7702" class="Bound">n</a><a id="7719" class="Symbol">)</a> <a id="7721" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7723" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7704" class="Bound">p</a> <a id="7725" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7727" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7700" class="Bound">m</a> <a id="7729" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7731" class="Symbol">(</a><a id="7732" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7702" class="Bound">n</a> <a id="7734" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7736" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7704" class="Bound">p</a><a id="7737" class="Symbol">)</a>
<a id="7739" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7687" class="Function">+-assoc</a> <a id="7747" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="7752" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7752" class="Bound">n</a> <a id="7754" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7754" class="Bound">p</a> <a id="7756" class="Symbol">=</a>
  <a id="7760" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="7770" class="Symbol">(</a><a id="7771" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="7776" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7778" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7752" class="Bound">n</a><a id="7779" class="Symbol">)</a> <a id="7781" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7783" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7754" class="Bound">p</a>
  <a id="7787" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7795" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7752" class="Bound">n</a> <a id="7797" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7799" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7754" class="Bound">p</a>
  <a id="7803" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
   <a id="7810" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="7815" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7817" class="Symbol">(</a><a id="7818" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7752" class="Bound">n</a> <a id="7820" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7822" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7754" class="Bound">p</a><a id="7823" class="Symbol">)</a>
  <a id="7827" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="7829" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7687" class="Function">+-assoc</a> <a id="7837" class="Symbol">(</a><a id="7838" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7842" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7842" class="Bound">m</a><a id="7843" class="Symbol">)</a> <a id="7845" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7845" class="Bound">n</a> <a id="7847" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7847" class="Bound">p</a> <a id="7849" class="Symbol">=</a>
  <a id="7853" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="7863" class="Symbol">(</a><a id="7864" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7868" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7842" class="Bound">m</a> <a id="7870" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7872" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7845" class="Bound">n</a><a id="7873" class="Symbol">)</a> <a id="7875" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7877" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7847" class="Bound">p</a>
  <a id="7881" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7889" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7893" class="Symbol">(</a><a id="7894" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7842" class="Bound">m</a> <a id="7896" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7898" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7845" class="Bound">n</a><a id="7899" class="Symbol">)</a> <a id="7901" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7903" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7847" class="Bound">p</a>
  <a id="7907" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7915" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7919" class="Symbol">((</a><a id="7921" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7842" class="Bound">m</a> <a id="7923" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7925" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7845" class="Bound">n</a><a id="7926" class="Symbol">)</a> <a id="7928" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7930" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7847" class="Bound">p</a><a id="7931" class="Symbol">)</a>
  <a id="7935" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="7938" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="7943" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7947" class="Symbol">(</a><a id="7948" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7687" class="Function">+-assoc</a> <a id="7956" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7842" class="Bound">m</a> <a id="7958" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7845" class="Bound">n</a> <a id="7960" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7847" class="Bound">p</a><a id="7961" class="Symbol">)</a> <a id="7963" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="7969" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7973" class="Symbol">(</a><a id="7974" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7842" class="Bound">m</a> <a id="7976" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7978" class="Symbol">(</a><a id="7979" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7845" class="Bound">n</a> <a id="7981" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7983" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7847" class="Bound">p</a><a id="7984" class="Symbol">))</a>
  <a id="7989" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7997" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="8001" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7842" class="Bound">m</a> <a id="8003" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8005" class="Symbol">(</a><a id="8006" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7845" class="Bound">n</a> <a id="8008" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8010" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7847" class="Bound">p</a><a id="8011" class="Symbol">)</a>
  <a id="8015" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provides evidence for the
proposition:

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p`
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    (m + n) + p ≡ m + (n + p)

Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:

    ⟨ cong suc (+-assoc m n p) ⟩

Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.

A relation is said to be a _congruence_ for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well-founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of https://agda.github.io/agda-stdlib/v1.1/Agda.

## Induction as recursion

As a concrete example of how induction corresponds to recursion, here
is the computation that occurs when instantiating `m` to `2` in the
proof of associativity.

{% raw %}<pre class="Agda"><a id="+-assoc-2"></a><a id="11039" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11039" class="Function">+-assoc-2</a> <a id="11049" class="Symbol">:</a> <a id="11051" class="Symbol">∀</a> <a id="11053" class="Symbol">(</a><a id="11054" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11054" class="Bound">n</a> <a id="11056" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11056" class="Bound">p</a> <a id="11058" class="Symbol">:</a> <a id="11060" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11061" class="Symbol">)</a> <a id="11063" class="Symbol">→</a> <a id="11065" class="Symbol">(</a><a id="11066" class="Number">2</a> <a id="11068" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11070" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11054" class="Bound">n</a><a id="11071" class="Symbol">)</a> <a id="11073" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11075" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11056" class="Bound">p</a> <a id="11077" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11079" class="Number">2</a> <a id="11081" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11083" class="Symbol">(</a><a id="11084" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11054" class="Bound">n</a> <a id="11086" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11088" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11056" class="Bound">p</a><a id="11089" class="Symbol">)</a>
<a id="11091" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11039" class="Function">+-assoc-2</a> <a id="11101" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11101" class="Bound">n</a> <a id="11103" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11103" class="Bound">p</a> <a id="11105" class="Symbol">=</a>
  <a id="11109" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="11119" class="Symbol">(</a><a id="11120" class="Number">2</a> <a id="11122" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11124" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11101" class="Bound">n</a><a id="11125" class="Symbol">)</a> <a id="11127" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11129" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11103" class="Bound">p</a>
  <a id="11133" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11141" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11145" class="Symbol">(</a><a id="11146" class="Number">1</a> <a id="11148" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11150" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11101" class="Bound">n</a><a id="11151" class="Symbol">)</a> <a id="11153" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11155" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11103" class="Bound">p</a>
  <a id="11159" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11167" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11171" class="Symbol">((</a><a id="11173" class="Number">1</a> <a id="11175" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11177" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11101" class="Bound">n</a><a id="11178" class="Symbol">)</a> <a id="11180" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11182" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11103" class="Bound">p</a><a id="11183" class="Symbol">)</a>
  <a id="11187" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="11190" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="11195" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11199" class="Symbol">(</a><a id="11200" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11275" class="Function">+-assoc-1</a> <a id="11210" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11101" class="Bound">n</a> <a id="11212" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11103" class="Bound">p</a><a id="11213" class="Symbol">)</a> <a id="11215" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="11221" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11225" class="Symbol">(</a><a id="11226" class="Number">1</a> <a id="11228" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11230" class="Symbol">(</a><a id="11231" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11101" class="Bound">n</a> <a id="11233" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11235" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11103" class="Bound">p</a><a id="11236" class="Symbol">))</a>
  <a id="11241" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11249" class="Number">2</a> <a id="11251" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11253" class="Symbol">(</a><a id="11254" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11101" class="Bound">n</a> <a id="11256" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11258" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11103" class="Bound">p</a><a id="11259" class="Symbol">)</a>
  <a id="11263" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
  <a id="11267" class="Keyword">where</a>
  <a id="11275" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11275" class="Function">+-assoc-1</a> <a id="11285" class="Symbol">:</a> <a id="11287" class="Symbol">∀</a> <a id="11289" class="Symbol">(</a><a id="11290" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11290" class="Bound">n</a> <a id="11292" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11292" class="Bound">p</a> <a id="11294" class="Symbol">:</a> <a id="11296" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11297" class="Symbol">)</a> <a id="11299" class="Symbol">→</a> <a id="11301" class="Symbol">(</a><a id="11302" class="Number">1</a> <a id="11304" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11306" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11290" class="Bound">n</a><a id="11307" class="Symbol">)</a> <a id="11309" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11311" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11292" class="Bound">p</a> <a id="11313" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11315" class="Number">1</a> <a id="11317" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11319" class="Symbol">(</a><a id="11320" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11290" class="Bound">n</a> <a id="11322" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11324" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11292" class="Bound">p</a><a id="11325" class="Symbol">)</a>
  <a id="11329" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11275" class="Function">+-assoc-1</a> <a id="11339" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11339" class="Bound">n</a> <a id="11341" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11341" class="Bound">p</a> <a id="11343" class="Symbol">=</a>
    <a id="11349" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
      <a id="11361" class="Symbol">(</a><a id="11362" class="Number">1</a> <a id="11364" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11366" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11339" class="Bound">n</a><a id="11367" class="Symbol">)</a> <a id="11369" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11371" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11341" class="Bound">p</a>
    <a id="11377" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="11387" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11391" class="Symbol">(</a><a id="11392" class="Number">0</a> <a id="11394" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11396" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11339" class="Bound">n</a><a id="11397" class="Symbol">)</a> <a id="11399" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11401" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11341" class="Bound">p</a>
    <a id="11407" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="11417" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11421" class="Symbol">((</a><a id="11423" class="Number">0</a> <a id="11425" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11427" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11339" class="Bound">n</a><a id="11428" class="Symbol">)</a> <a id="11430" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11432" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11341" class="Bound">p</a><a id="11433" class="Symbol">)</a>
    <a id="11439" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="11442" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="11447" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11451" class="Symbol">(</a><a id="11452" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11539" class="Function">+-assoc-0</a> <a id="11462" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11339" class="Bound">n</a> <a id="11464" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11341" class="Bound">p</a><a id="11465" class="Symbol">)</a> <a id="11467" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
      <a id="11475" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11479" class="Symbol">(</a><a id="11480" class="Number">0</a> <a id="11482" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11484" class="Symbol">(</a><a id="11485" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11339" class="Bound">n</a> <a id="11487" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11489" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11341" class="Bound">p</a><a id="11490" class="Symbol">))</a>
    <a id="11497" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="11507" class="Number">1</a> <a id="11509" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11511" class="Symbol">(</a><a id="11512" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11339" class="Bound">n</a> <a id="11514" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11516" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11341" class="Bound">p</a><a id="11517" class="Symbol">)</a>
    <a id="11523" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
    <a id="11529" class="Keyword">where</a>
    <a id="11539" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11539" class="Function">+-assoc-0</a> <a id="11549" class="Symbol">:</a> <a id="11551" class="Symbol">∀</a> <a id="11553" class="Symbol">(</a><a id="11554" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11554" class="Bound">n</a> <a id="11556" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11556" class="Bound">p</a> <a id="11558" class="Symbol">:</a> <a id="11560" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11561" class="Symbol">)</a> <a id="11563" class="Symbol">→</a> <a id="11565" class="Symbol">(</a><a id="11566" class="Number">0</a> <a id="11568" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11570" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11554" class="Bound">n</a><a id="11571" class="Symbol">)</a> <a id="11573" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11575" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11556" class="Bound">p</a> <a id="11577" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11579" class="Number">0</a> <a id="11581" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11583" class="Symbol">(</a><a id="11584" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11554" class="Bound">n</a> <a id="11586" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11588" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11556" class="Bound">p</a><a id="11589" class="Symbol">)</a>
    <a id="11595" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11539" class="Function">+-assoc-0</a> <a id="11605" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11605" class="Bound">n</a> <a id="11607" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11607" class="Bound">p</a> <a id="11609" class="Symbol">=</a>
      <a id="11617" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
        <a id="11631" class="Symbol">(</a><a id="11632" class="Number">0</a> <a id="11634" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11636" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11605" class="Bound">n</a><a id="11637" class="Symbol">)</a> <a id="11639" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11641" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11607" class="Bound">p</a>
      <a id="11649" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="11661" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11605" class="Bound">n</a> <a id="11663" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11665" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11607" class="Bound">p</a>
      <a id="11673" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="11685" class="Number">0</a> <a id="11687" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11689" class="Symbol">(</a><a id="11690" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11605" class="Bound">n</a> <a id="11692" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11694" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11607" class="Bound">p</a><a id="11695" class="Symbol">)</a>
      <a id="11703" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}

## Terminology and notation

The symbol `∀` appears in the statement of associativity to indicate that
it holds for all numbers `m`, `n`, and `p`.  We refer to `∀` as the _universal
quantifier_, and it is discussed further in Chapter [Quantifiers]({{ site.baseurl }}/Quantifiers/).

Evidence for a universal quantifier is a function.  The notations

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

and

    +-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)

are equivalent. They differ from a function type such as `ℕ → ℕ → ℕ`
in that variables are associated with the each argument type, and the
result type may mention (or depend upon) these variables; hence they
are called _dependent functions_.


## Our second proof: commutativity

Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:

    m + n ≡ n + m

The proof requires that we first demonstrate two lemmas.

### The first lemma

The base case of the definition of addition states that zero
is a left-identity:

    zero + n ≡ n

Our first lemma states that zero is also a right-identity:

    m + zero ≡ m

Here is the lemma's statement and proof:
{% raw %}<pre class="Agda"><a id="+-identityʳ"></a><a id="12927" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12927" class="Function">+-identityʳ</a> <a id="12939" class="Symbol">:</a> <a id="12941" class="Symbol">∀</a> <a id="12943" class="Symbol">(</a><a id="12944" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12944" class="Bound">m</a> <a id="12946" class="Symbol">:</a> <a id="12948" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12949" class="Symbol">)</a> <a id="12951" class="Symbol">→</a> <a id="12953" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12944" class="Bound">m</a> <a id="12955" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="12957" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="12962" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="12964" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12944" class="Bound">m</a>
<a id="12966" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12927" class="Function">+-identityʳ</a> <a id="12978" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="12983" class="Symbol">=</a>
  <a id="12987" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="12997" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="13002" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="13004" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="13011" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="13019" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="13026" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="13028" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12927" class="Function">+-identityʳ</a> <a id="13040" class="Symbol">(</a><a id="13041" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13045" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13045" class="Bound">m</a><a id="13046" class="Symbol">)</a> <a id="13048" class="Symbol">=</a>
  <a id="13052" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="13062" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13066" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13045" class="Bound">m</a> <a id="13068" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="13070" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="13077" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="13085" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13089" class="Symbol">(</a><a id="13090" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13045" class="Bound">m</a> <a id="13092" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="13094" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="13098" class="Symbol">)</a>
  <a id="13102" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13105" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="13110" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13114" class="Symbol">(</a><a id="13115" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12927" class="Function">+-identityʳ</a> <a id="13127" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13045" class="Bound">m</a><a id="13128" class="Symbol">)</a> <a id="13130" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="13136" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13140" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13045" class="Bound">m</a>
  <a id="13144" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:

    ∀ (m : ℕ) → m + zero ≡ m

Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + zero ≡ zero

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    (suc m) + zero = suc m

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + zero) = suc m

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + zero ≡ m

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:

    ⟨ cong suc (+-identityʳ m) ⟩

Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.

### The second lemma

The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:

    suc m + n ≡ suc (m + n)

Our second lemma does the same for `suc` on the second argument:

    m + suc n ≡ suc (m + n)

Here is the lemma's statement and proof:
{% raw %}<pre class="Agda"><a id="+-suc"></a><a id="14584" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14584" class="Function">+-suc</a> <a id="14590" class="Symbol">:</a> <a id="14592" class="Symbol">∀</a> <a id="14594" class="Symbol">(</a><a id="14595" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14595" class="Bound">m</a> <a id="14597" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14597" class="Bound">n</a> <a id="14599" class="Symbol">:</a> <a id="14601" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14602" class="Symbol">)</a> <a id="14604" class="Symbol">→</a> <a id="14606" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14595" class="Bound">m</a> <a id="14608" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14610" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14614" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14597" class="Bound">n</a> <a id="14616" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14618" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14622" class="Symbol">(</a><a id="14623" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14595" class="Bound">m</a> <a id="14625" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14627" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14597" class="Bound">n</a><a id="14628" class="Symbol">)</a>
<a id="14630" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14584" class="Function">+-suc</a> <a id="14636" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14641" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14641" class="Bound">n</a> <a id="14643" class="Symbol">=</a>
  <a id="14647" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="14657" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14662" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14664" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14668" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14641" class="Bound">n</a>
  <a id="14672" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14680" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14684" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14641" class="Bound">n</a>
  <a id="14688" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14696" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14700" class="Symbol">(</a><a id="14701" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14706" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14708" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14641" class="Bound">n</a><a id="14709" class="Symbol">)</a>
  <a id="14713" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="14715" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14584" class="Function">+-suc</a> <a id="14721" class="Symbol">(</a><a id="14722" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14726" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14726" class="Bound">m</a><a id="14727" class="Symbol">)</a> <a id="14729" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14729" class="Bound">n</a> <a id="14731" class="Symbol">=</a>
  <a id="14735" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="14745" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14749" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14726" class="Bound">m</a> <a id="14751" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14753" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14757" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14729" class="Bound">n</a>
  <a id="14761" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14769" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14773" class="Symbol">(</a><a id="14774" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14726" class="Bound">m</a> <a id="14776" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14778" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14782" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14729" class="Bound">n</a><a id="14783" class="Symbol">)</a>
  <a id="14787" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="14790" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="14795" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14799" class="Symbol">(</a><a id="14800" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14584" class="Function">+-suc</a> <a id="14806" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14726" class="Bound">m</a> <a id="14808" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14729" class="Bound">n</a><a id="14809" class="Symbol">)</a> <a id="14811" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="14817" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14821" class="Symbol">(</a><a id="14822" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14826" class="Symbol">(</a><a id="14827" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14726" class="Bound">m</a> <a id="14829" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14831" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14729" class="Bound">n</a><a id="14832" class="Symbol">))</a>
  <a id="14837" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14845" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14849" class="Symbol">(</a><a id="14850" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14854" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14726" class="Bound">m</a> <a id="14856" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14858" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14729" class="Bound">n</a><a id="14859" class="Symbol">)</a>
  <a id="14863" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + suc n ≡ suc (zero + n)

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    suc m + suc n ≡ suc (suc m + n)

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + suc n) ≡ suc (suc (m + n))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + suc n ≡ suc (m + n)

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:

    ⟨ cong suc (+-suc m n) ⟩

Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.

### The proposition

Finally, here is our proposition's statement and proof:
{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="16157" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16157" class="Function">+-comm</a> <a id="16164" class="Symbol">:</a> <a id="16166" class="Symbol">∀</a> <a id="16168" class="Symbol">(</a><a id="16169" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16169" class="Bound">m</a> <a id="16171" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16171" class="Bound">n</a> <a id="16173" class="Symbol">:</a> <a id="16175" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16176" class="Symbol">)</a> <a id="16178" class="Symbol">→</a> <a id="16180" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16169" class="Bound">m</a> <a id="16182" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16184" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16171" class="Bound">n</a> <a id="16186" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16188" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16171" class="Bound">n</a> <a id="16190" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16192" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16169" class="Bound">m</a>
<a id="16194" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16157" class="Function">+-comm</a> <a id="16201" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16201" class="Bound">m</a> <a id="16203" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="16208" class="Symbol">=</a>
  <a id="16212" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="16222" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16201" class="Bound">m</a> <a id="16224" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16226" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="16233" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16236" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12927" class="Function">+-identityʳ</a> <a id="16248" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16201" class="Bound">m</a> <a id="16250" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16256" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16201" class="Bound">m</a>
  <a id="16260" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16268" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="16273" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16275" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16201" class="Bound">m</a>
  <a id="16279" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="16281" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16157" class="Function">+-comm</a> <a id="16288" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16288" class="Bound">m</a> <a id="16290" class="Symbol">(</a><a id="16291" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16295" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16295" class="Bound">n</a><a id="16296" class="Symbol">)</a> <a id="16298" class="Symbol">=</a>
  <a id="16302" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="16312" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16288" class="Bound">m</a> <a id="16314" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16316" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16320" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16295" class="Bound">n</a>
  <a id="16324" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16327" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14584" class="Function">+-suc</a> <a id="16333" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16288" class="Bound">m</a> <a id="16335" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16295" class="Bound">n</a> <a id="16337" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16343" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16347" class="Symbol">(</a><a id="16348" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16288" class="Bound">m</a> <a id="16350" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16352" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16295" class="Bound">n</a><a id="16353" class="Symbol">)</a>
  <a id="16357" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16360" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="16365" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16369" class="Symbol">(</a><a id="16370" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16157" class="Function">+-comm</a> <a id="16377" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16288" class="Bound">m</a> <a id="16379" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16295" class="Bound">n</a><a id="16380" class="Symbol">)</a> <a id="16382" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16388" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16392" class="Symbol">(</a><a id="16393" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16295" class="Bound">n</a> <a id="16395" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16397" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16288" class="Bound">m</a><a id="16398" class="Symbol">)</a>
  <a id="16402" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16410" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16414" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16295" class="Bound">n</a> <a id="16416" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16418" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16288" class="Bound">m</a>
  <a id="16422" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:

    ∀ (m n : ℕ) → m + n ≡ n + m

Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)

For the base case, we must show:

    m + zero ≡ zero + m

Simplifying both sides with the base case of addition yields the equation:

    m + zero ≡ m

The remaining equation has the justification `⟨ +-identityʳ m ⟩`,
which invokes the first lemma.

For the inductive case, we must show:

    m + suc n ≡ suc n + m

Simplifying both sides with the inductive case of addition yields the equation:

    m + suc n ≡ suc (n + m)

We show this in two steps.  First, we have:

    m + suc n ≡ suc (m + n)

which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have

    suc (m + n) ≡ suc (n + m)

which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proof.

Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.


## Our first corollary: rearranging {#sections}

We can apply associativity to rearrange parentheses however we like.
Here is an example:
{% raw %}<pre class="Agda"><a id="+-rearrange"></a><a id="17968" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17968" class="Function">+-rearrange</a> <a id="17980" class="Symbol">:</a> <a id="17982" class="Symbol">∀</a> <a id="17984" class="Symbol">(</a><a id="17985" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17985" class="Bound">m</a> <a id="17987" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17987" class="Bound">n</a> <a id="17989" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17989" class="Bound">p</a> <a id="17991" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17991" class="Bound">q</a> <a id="17993" class="Symbol">:</a> <a id="17995" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17996" class="Symbol">)</a> <a id="17998" class="Symbol">→</a> <a id="18000" class="Symbol">(</a><a id="18001" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17985" class="Bound">m</a> <a id="18003" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18005" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17987" class="Bound">n</a><a id="18006" class="Symbol">)</a> <a id="18008" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18010" class="Symbol">(</a><a id="18011" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17989" class="Bound">p</a> <a id="18013" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18015" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17991" class="Bound">q</a><a id="18016" class="Symbol">)</a> <a id="18018" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="18020" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17985" class="Bound">m</a> <a id="18022" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18024" class="Symbol">(</a><a id="18025" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17987" class="Bound">n</a> <a id="18027" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18029" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17989" class="Bound">p</a><a id="18030" class="Symbol">)</a> <a id="18032" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18034" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17991" class="Bound">q</a>
<a id="18036" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17968" class="Function">+-rearrange</a> <a id="18048" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18048" class="Bound">m</a> <a id="18050" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18050" class="Bound">n</a> <a id="18052" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18052" class="Bound">p</a> <a id="18054" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18054" class="Bound">q</a> <a id="18056" class="Symbol">=</a>
  <a id="18060" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="18070" class="Symbol">(</a><a id="18071" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18048" class="Bound">m</a> <a id="18073" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18075" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18050" class="Bound">n</a><a id="18076" class="Symbol">)</a> <a id="18078" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18080" class="Symbol">(</a><a id="18081" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18052" class="Bound">p</a> <a id="18083" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18085" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18054" class="Bound">q</a><a id="18086" class="Symbol">)</a>
  <a id="18090" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18093" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7687" class="Function">+-assoc</a> <a id="18101" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18048" class="Bound">m</a> <a id="18103" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18050" class="Bound">n</a> <a id="18105" class="Symbol">(</a><a id="18106" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18052" class="Bound">p</a> <a id="18108" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18110" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18054" class="Bound">q</a><a id="18111" class="Symbol">)</a> <a id="18113" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18119" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18048" class="Bound">m</a> <a id="18121" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18123" class="Symbol">(</a><a id="18124" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18050" class="Bound">n</a> <a id="18126" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18128" class="Symbol">(</a><a id="18129" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18052" class="Bound">p</a> <a id="18131" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18133" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18054" class="Bound">q</a><a id="18134" class="Symbol">))</a>
  <a id="18139" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18142" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="18147" class="Symbol">(</a><a id="18148" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18048" class="Bound">m</a> <a id="18150" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+_</a><a id="18152" class="Symbol">)</a> <a id="18154" class="Symbol">(</a><a id="18155" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="18159" class="Symbol">(</a><a id="18160" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7687" class="Function">+-assoc</a> <a id="18168" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18050" class="Bound">n</a> <a id="18170" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18052" class="Bound">p</a> <a id="18172" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18054" class="Bound">q</a><a id="18173" class="Symbol">))</a> <a id="18176" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18182" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18048" class="Bound">m</a> <a id="18184" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18186" class="Symbol">((</a><a id="18188" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18050" class="Bound">n</a> <a id="18190" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18192" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18052" class="Bound">p</a><a id="18193" class="Symbol">)</a> <a id="18195" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18197" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18054" class="Bound">q</a><a id="18198" class="Symbol">)</a>
  <a id="18202" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18205" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="18209" class="Symbol">(</a><a id="18210" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7687" class="Function">+-assoc</a> <a id="18218" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18048" class="Bound">m</a> <a id="18220" class="Symbol">(</a><a id="18221" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18050" class="Bound">n</a> <a id="18223" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18225" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18052" class="Bound">p</a><a id="18226" class="Symbol">)</a> <a id="18228" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18054" class="Bound">q</a><a id="18229" class="Symbol">)</a> <a id="18231" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18237" class="Symbol">(</a><a id="18238" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18048" class="Bound">m</a> <a id="18240" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18242" class="Symbol">(</a><a id="18243" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18050" class="Bound">n</a> <a id="18245" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18247" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18052" class="Bound">p</a><a id="18248" class="Symbol">))</a> <a id="18251" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18253" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18054" class="Bound">q</a>
  <a id="18257" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}No induction is required, we simply apply associativity twice.
A few points are worthy of note.

First, addition associates to the left, so `m + (n + p) + q`
stands for `(m + (n + p)) + q`.

Second, we use `sym` to interchange the sides of an equation.
Proposition `+-assoc n p q` shifts parentheses from right to left:

    (n + p) + q ≡ n + (p + q)

To shift them the other way, we use `sym (+-assoc n p q)`:

    n + (p + q) ≡ (n + p) + q

In general, if `e` provides evidence for `x ≡ y` then `sym e` provides
evidence for `y ≡ x`.

Third, Agda supports a variant of the _section_ notation introduced by
Richard Bird.  We write `(x +_)` for the function that applied to `y`
returns `x + y`.  Thus, applying the congruence `cong (m +_)` takes
the above equation into:

    m + (n + (p + q)) ≡ m + ((n + p) + q)

Similarly, we write `(_+ x)` for the function that applied to `y`
returns `y + x`; the same works for any infix operator.



## Creation, one last time

Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgments asserting associativity:

     -- In the beginning, we know nothing about associativity.

Now, we apply the rules to all the judgments we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments:

    -- On the first day, we know about associativity of 0.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

Then we repeat the process, so on the next day we know about all the
judgments from the day before, plus any judgments added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgments:

    -- On the second day, we know about associativity of 0 and 1.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again:

    -- On the third day, we know about associativity of 0, 1, and 2.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've got the hang of it by now:

    -- On the fourth day, we know about associativity of 0, 1, 2, and 3.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

The process continues.  On the _m_'th day we will know all the
judgments where the first number is less than _m_.

There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.

#### Exercise `finite-|-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier]({{ site.baseurl }}/Naturals/#finite-creation).

{% raw %}<pre class="Agda"><a id="21675" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Associativity with rewrite

There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations:
{% raw %}<pre class="Agda"><a id="+-assoc′"></a><a id="21891" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21891" class="Function">+-assoc′</a> <a id="21900" class="Symbol">:</a> <a id="21902" class="Symbol">∀</a> <a id="21904" class="Symbol">(</a><a id="21905" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21905" class="Bound">m</a> <a id="21907" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21907" class="Bound">n</a> <a id="21909" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21909" class="Bound">p</a> <a id="21911" class="Symbol">:</a> <a id="21913" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21914" class="Symbol">)</a> <a id="21916" class="Symbol">→</a> <a id="21918" class="Symbol">(</a><a id="21919" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21905" class="Bound">m</a> <a id="21921" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21923" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21907" class="Bound">n</a><a id="21924" class="Symbol">)</a> <a id="21926" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21928" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21909" class="Bound">p</a> <a id="21930" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="21932" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21905" class="Bound">m</a> <a id="21934" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21936" class="Symbol">(</a><a id="21937" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21907" class="Bound">n</a> <a id="21939" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21941" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21909" class="Bound">p</a><a id="21942" class="Symbol">)</a>
<a id="21944" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21891" class="Function">+-assoc′</a> <a id="21953" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="21961" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21961" class="Bound">n</a> <a id="21963" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21963" class="Bound">p</a>                          <a id="21990" class="Symbol">=</a>  <a id="21993" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="21998" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21891" class="Function">+-assoc′</a> <a id="22007" class="Symbol">(</a><a id="22008" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="22012" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22012" class="Bound">m</a><a id="22013" class="Symbol">)</a> <a id="22015" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22015" class="Bound">n</a> <a id="22017" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22017" class="Bound">p</a>  <a id="22020" class="Keyword">rewrite</a> <a id="22028" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21891" class="Function">+-assoc′</a> <a id="22037" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22012" class="Bound">m</a> <a id="22039" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22015" class="Bound">n</a> <a id="22041" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22017" class="Bound">p</a>  <a id="22044" class="Symbol">=</a>  <a id="22047" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially. The proof that a term is equal to itself is written `refl`.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.


## Commutativity with rewrite

Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations:
{% raw %}<pre class="Agda"><a id="+-identity′"></a><a id="22950" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22950" class="Function">+-identity′</a> <a id="22962" class="Symbol">:</a> <a id="22964" class="Symbol">∀</a> <a id="22966" class="Symbol">(</a><a id="22967" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22967" class="Bound">n</a> <a id="22969" class="Symbol">:</a> <a id="22971" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22972" class="Symbol">)</a> <a id="22974" class="Symbol">→</a> <a id="22976" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22967" class="Bound">n</a> <a id="22978" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22980" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="22985" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="22987" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22967" class="Bound">n</a>
<a id="22989" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22950" class="Function">+-identity′</a> <a id="23001" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23006" class="Symbol">=</a> <a id="23008" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="23013" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22950" class="Function">+-identity′</a> <a id="23025" class="Symbol">(</a><a id="23026" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23030" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23030" class="Bound">n</a><a id="23031" class="Symbol">)</a> <a id="23033" class="Keyword">rewrite</a> <a id="23041" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22950" class="Function">+-identity′</a> <a id="23053" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23030" class="Bound">n</a> <a id="23055" class="Symbol">=</a> <a id="23057" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="23063" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23063" class="Function">+-suc′</a> <a id="23070" class="Symbol">:</a> <a id="23072" class="Symbol">∀</a> <a id="23074" class="Symbol">(</a><a id="23075" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23075" class="Bound">m</a> <a id="23077" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23077" class="Bound">n</a> <a id="23079" class="Symbol">:</a> <a id="23081" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23082" class="Symbol">)</a> <a id="23084" class="Symbol">→</a> <a id="23086" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23075" class="Bound">m</a> <a id="23088" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23090" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23094" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23077" class="Bound">n</a> <a id="23096" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23098" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23102" class="Symbol">(</a><a id="23103" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23075" class="Bound">m</a> <a id="23105" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23107" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23077" class="Bound">n</a><a id="23108" class="Symbol">)</a>
<a id="23110" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23063" class="Function">+-suc′</a> <a id="23117" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23122" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23122" class="Bound">n</a> <a id="23124" class="Symbol">=</a> <a id="23126" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="23131" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23063" class="Function">+-suc′</a> <a id="23138" class="Symbol">(</a><a id="23139" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23143" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23143" class="Bound">m</a><a id="23144" class="Symbol">)</a> <a id="23146" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23146" class="Bound">n</a> <a id="23148" class="Keyword">rewrite</a> <a id="23156" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23063" class="Function">+-suc′</a> <a id="23163" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23143" class="Bound">m</a> <a id="23165" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23146" class="Bound">n</a> <a id="23167" class="Symbol">=</a> <a id="23169" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="23175" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23175" class="Function">+-comm′</a> <a id="23183" class="Symbol">:</a> <a id="23185" class="Symbol">∀</a> <a id="23187" class="Symbol">(</a><a id="23188" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23188" class="Bound">m</a> <a id="23190" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23190" class="Bound">n</a> <a id="23192" class="Symbol">:</a> <a id="23194" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23195" class="Symbol">)</a> <a id="23197" class="Symbol">→</a> <a id="23199" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23188" class="Bound">m</a> <a id="23201" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23203" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23190" class="Bound">n</a> <a id="23205" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23207" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23190" class="Bound">n</a> <a id="23209" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23211" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23188" class="Bound">m</a>
<a id="23213" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23175" class="Function">+-comm′</a> <a id="23221" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23221" class="Bound">m</a> <a id="23223" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23228" class="Keyword">rewrite</a> <a id="23236" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22950" class="Function">+-identity′</a> <a id="23248" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23221" class="Bound">m</a> <a id="23250" class="Symbol">=</a> <a id="23252" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="23257" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23175" class="Function">+-comm′</a> <a id="23265" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23265" class="Bound">m</a> <a id="23267" class="Symbol">(</a><a id="23268" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23272" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23272" class="Bound">n</a><a id="23273" class="Symbol">)</a> <a id="23275" class="Keyword">rewrite</a> <a id="23283" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23063" class="Function">+-suc′</a> <a id="23290" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23265" class="Bound">m</a> <a id="23292" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23272" class="Bound">n</a> <a id="23294" class="Symbol">|</a> <a id="23296" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23175" class="Function">+-comm′</a> <a id="23304" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23265" class="Bound">m</a> <a id="23306" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23272" class="Bound">n</a> <a id="23308" class="Symbol">=</a> <a id="23310" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.


## Building proofs interactively

It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

The empty braces are called a _hole_, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text:

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgment.

We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `C-c C-,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in.
Typing `C-c C-l` renumbers the remaining hole to 0:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

Going into the new hole 0 and typing `C-c C-,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

Going into the remaining hole and typing `C-c C-,` will display the text:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.

{% raw %}<pre class="Agda"><a id="26850" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

{% raw %}<pre class="Agda"><a id="27075" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

{% raw %}<pre class="Agda"><a id="27276" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `*-comm` {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

{% raw %}<pre class="Agda"><a id="27533" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `0∸n≡0` {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

{% raw %}<pre class="Agda"><a id="27687" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `∸-|-assoc` {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

{% raw %}<pre class="Agda"><a id="27885" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `+*^` (stretch)

Show the following three laws

    m ^ (n + p) ≡ (m ^ n) * (m ^ p)
    (m * n) ^ p ≡ (m ^ p) * (n ^ p)
    m ^ (n * p) ≡ (m ^ n) ^ p

for all `m`, `n`, and `p`.


#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype of bitstrings representing natural numbers
{% raw %}<pre class="Agda"><a id="28283" class="Keyword">data</a> <a id="Bin"></a><a id="28288" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28288" class="Datatype">Bin</a> <a id="28292" class="Symbol">:</a> <a id="28294" class="PrimitiveType">Set</a> <a id="28298" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="28306" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28306" class="InductiveConstructor">nil</a> <a id="28310" class="Symbol">:</a> <a id="28312" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28288" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="28318" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28318" class="InductiveConstructor Operator">x0_</a> <a id="28322" class="Symbol">:</a> <a id="28324" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28288" class="Datatype">Bin</a> <a id="28328" class="Symbol">→</a> <a id="28330" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28288" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="28336" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28336" class="InductiveConstructor Operator">x1_</a> <a id="28340" class="Symbol">:</a> <a id="28342" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28288" class="Datatype">Bin</a> <a id="28346" class="Symbol">→</a> <a id="28348" href="plfa.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28288" class="Datatype">Bin</a>
</pre>{% endraw %}and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings:

    from (inc x) ≡ suc (from x)
    to (from x) ≡ x
    from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample.

{% raw %}<pre class="Agda"><a id="28682" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="28819" class="Keyword">import</a> <a id="28826" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="28846" class="Keyword">using</a> <a id="28852" class="Symbol">(</a><a id="28853" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="28860" class="Symbol">;</a> <a id="28862" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="28873" class="Symbol">;</a> <a id="28875" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="28880" class="Symbol">;</a> <a id="28882" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="28888" class="Symbol">)</a>
</pre>{% endraw %}
## Unicode

This chapter uses the following unicode:

    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
