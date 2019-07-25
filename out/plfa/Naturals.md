---
src       : "src/plfa/Naturals.lagda.md"
title     : "Naturals: Natural numbers"
layout    : page
prev      : /Preface/
permalink : /Naturals/
next      : /Induction/
---

{% raw %}<pre class="Agda"><a id="140" class="Keyword">module</a> <a id="147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}" class="Module">plfa.Naturals</a> <a id="161" class="Keyword">where</a>
</pre>{% endraw %}
The night sky holds more stars than I can count, though fewer than five
thousand are visible to the naked eye.  The observable universe
contains about seventy sextillion stars.

But the number of stars is finite, while natural numbers are infinite.
Count all the stars, and you will still have as many natural numbers
left over as you started with.


## The naturals are an inductive datatype

Everyone is familiar with the natural numbers

    0
    1
    2
    3
    ...

and so on. We write `ℕ` for the *type* of natural numbers, and say that
`0`, `1`, `2`, `3`, and so on are *values* of type `ℕ`, indicated by
writing `0 : ℕ`, `1 : ℕ`, `2 : ℕ`, `3 : ℕ`, and so on.

The set of natural numbers is infinite, yet we can write down
its definition in just a few lines.  Here is the definition
as a pair of inference rules:

    --------
    zero : ℕ

    m : ℕ
    ---------
    suc m : ℕ

And here is the definition in Agda:
{% raw %}<pre class="Agda"><a id="1102" class="Keyword">data</a> <a id="ℕ"></a><a id="1107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1107" class="Datatype">ℕ</a> <a id="1109" class="Symbol">:</a> <a id="1111" class="PrimitiveType">Set</a> <a id="1115" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="1123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1123" class="InductiveConstructor">zero</a> <a id="1128" class="Symbol">:</a> <a id="1130" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="1134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a>  <a id="1139" class="Symbol">:</a> <a id="1141" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a> <a id="1143" class="Symbol">→</a> <a id="1145" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a>
</pre>{% endraw %}
Here `ℕ` is the name of the *datatype* we are defining,
and `zero` and `suc` (short for *successor*) are the
*constructors* of the datatype.

Both definitions above tell us the same two things:

* _Base case_: `zero` is a natural number.
* _Inductive case_: if `m` is a natural number, then `suc m` is also a
  natural number.

Further, these two rules give the *only* ways of creating natural numbers.
Hence, the possible natural numbers are:

    zero
    suc zero
    suc (suc zero)
    suc (suc (suc zero))
    ...

We write `0` as shorthand for `zero`; and `1` is shorthand
for `suc zero`, the successor of zero, that is, the natural that comes
after zero; and `2` is shorthand for `suc (suc zero)`, which is the
same as `suc 1`, the successor of one; and `3` is shorthand for the
successor of two; and so on.

#### Exercise `seven` {#seven}

Write out `7` in longhand.

{% raw %}<pre class="Agda"><a id="2032" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Unpacking the inference rules

Let's unpack the inference rules.  Each inference rule consists of
zero or more _judgments_ written above a horizontal line, called the
_hypotheses_, and a single judgment written below, called the
_conclusion_.  The first rule is the base case. It has no hypotheses,
and the conclusion asserts that `zero` is a natural.  The second rule
is the inductive case. It has one hypothesis, which assumes that `m`
is a natural, and the conclusion asserts that `suc m`
is a also a natural.


## Unpacking the Agda definition

Let's unpack the Agda definition. The keyword `data` tells us this is an
inductive definition, that is, that we are defining a new datatype
with constructors.  The phrase

    ℕ : Set

tells us that `ℕ` is the name of the new datatype, and that it is a
`Set`, which is the way in Agda of saying that it is a type.  The
keyword `where` separates the declaration of the datatype from the
declaration of its constructors. Each constructor is declared on a
separate line, which is indented to indicate that it belongs to the
corresponding `data` declaration.  The lines

    zero : ℕ
    suc  : ℕ → ℕ

give _signatures_ specifying the types of the constructors `zero` and `suc`.
They tell us that `zero` is a natural number and that `suc` takes a natural
number as argument and returns a natural number.

You may have noticed that `ℕ` and `→` don't appear on your keyboard.
They are symbols in _unicode_.  At the end of each chapter is a list
of all unicode symbols introduced in the chapter, including
instructions on how to type them in the Emacs text editor.  Here
_type_ refers to typing with fingers as opposed to data types!


## The story of creation

Let's look again at the rules that define the natural numbers:

* _Base case_: `zero` is a natural number.
* _Inductive case_: if `m` is a natural number, then `suc m` is also a
  natural number.

Hold on! The second line defines natural numbers in terms of natural
numbers. How can that possibly be allowed?  Isn't this as useless a
definition as "Brexit means Brexit"?

In fact, it is possible to assign our definition a meaning without
resorting to unpermitted circularities.  Furthermore, we can do so
while only working with _finite_ sets and never referring to the
_infinite_ set of natural numbers.

We will think of it as a creation story.  To start with, we know about
no natural numbers at all:

    -- In the beginning, there are no natural numbers.

Now, we apply the rules to all the natural numbers we know about.  The
base case tells us that `zero` is a natural number, so we add it to the set
of known natural numbers.  The inductive case tells us that if `m` is a
natural number (on the day before today) then `suc m` is also a
natural number (today).  We didn't know about any natural numbers
before today, so the inductive case doesn't apply:

    -- On the first day, there is one natural number.
    zero : ℕ

Then we repeat the process. On the next day we know about all the
numbers from the day before, plus any numbers added by the rules.  The
base case tells us that `zero` is a natural number, but we already knew
that. But now the inductive case tells us that since `zero` was a natural
number yesterday, then `suc zero` is a natural number today:

    -- On the second day, there are two natural numbers.
    zero : ℕ
    suc zero : ℕ

And we repeat the process again. Now the inductive case
tells us that since `zero` and `suc zero` are both natural numbers, then
`suc zero` and `suc (suc zero)` are natural numbers. We already knew about
the first of these, but the second is new:

    -- On the third day, there are three natural numbers.
    zero : ℕ
    suc zero : ℕ
    suc (suc zero) : ℕ

You've got the hang of it by now:

    -- On the fourth day, there are four natural numbers.
    zero : ℕ
    suc zero : ℕ
    suc (suc zero) : ℕ
    suc (suc (suc zero)) : ℕ

The process continues.  On the _n_'th day there will be _n_ distinct
natural numbers. Every natural number will appear on some given day.
In particular, the number _n_ first appears on day _n+1_. And we
never actually define the set of numbers in terms of itself. Instead,
we define the set of numbers on day _n+1_ in terms of the set of
numbers on day _n_.

A process like this one is called _inductive_. We start with nothing, and
build up a potentially infinite set by applying rules that convert one
finite set into another finite set.

The rule defining zero is called a _base case_, because it introduces
a natural number even when we know no other natural numbers.  The rule
defining successor is called an _inductive case_, because it
introduces more natural numbers once we already know some.  Note the
crucial role of the base case.  If we only had inductive rules, then
we would have no numbers in the beginning, and still no numbers on the
second day, and on the third, and so on.  An inductive definition lacking
a base case is useless, as in the phrase "Brexit means Brexit".


## Philosophy and history

A philosopher might observe that our reference to the first day,
second day, and so on, implicitly involves an understanding of natural
numbers.  In this sense, our definition might indeed be regarded as in
some sense circular, but we need not let this disturb us.
Everyone possesses a good informal understanding of the natural
numbers, which we may take as a foundation for their formal
description.

While the natural numbers have been understood for as long as people
can count, the inductive definition of the natural numbers is relatively
recent.  It can be traced back to Richard Dedekind's paper "_Was sind
und was sollen die Zahlen?_" (What are and what should be the
numbers?), published in 1888, and Giuseppe Peano's book "_Arithmetices
principia, nova methodo exposita_" (The principles of arithmetic
presented by a new method), published the following year.


## A pragma

In Agda, any text following `--` or enclosed between `{-`
and `-}` is considered a _comment_.  Comments have no effect on the
code, with the exception of one special kind of comment, called a
_pragma_, which is enclosed between `{-#` and `#-}`.

Including the line
{% raw %}<pre class="Agda"><a id="8242" class="Symbol">{-#</a> <a id="8246" class="Keyword">BUILTIN</a> <a id="8254" class="Pragma">NATURAL</a> <a id="8262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1107" class="Datatype">ℕ</a> <a id="8264" class="Symbol">#-}</a>
</pre>{% endraw %}tells Agda that `ℕ` corresponds to the natural numbers, and hence one
is permitted to type `0` as shorthand for `zero`, `1` as shorthand for
`suc zero`, `2` as shorthand for `suc (suc zero)`, and so on.  The
declaration is not permitted unless the type given has exactly two
constructors, one with no arguments (corresponding to zero) and
one with a single argument of the same type given in the pragma
(corresponding to successor).

As well as enabling the above shorthand, the pragma also enables a
more efficient internal representation of naturals using the Haskell
type for arbitrary-precision integers.  Representing the natural _n_
with `zero` and `suc` requires space proportional to _n_, whereas
representing it as an arbitrary-precision integer in Haskell only
requires space proportional to the logarithm of _n_.


## Imports

Shortly we will want to write some equations that hold between
terms involving natural numbers.  To support doing so, we import
the definition of equality and notations for reasoning
about it from the Agda standard library:

{% raw %}<pre class="Agda"><a id="9339" class="Keyword">import</a> <a id="9346" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="9384" class="Symbol">as</a> <a id="9387" class="Module">Eq</a>
<a id="9390" class="Keyword">open</a> <a id="9395" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="9398" class="Keyword">using</a> <a id="9404" class="Symbol">(</a><a id="9405" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="9408" class="Symbol">;</a> <a id="9410" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="9414" class="Symbol">)</a>
<a id="9416" class="Keyword">open</a> <a id="9421" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="9436" class="Keyword">using</a> <a id="9442" class="Symbol">(</a><a id="9443" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="9449" class="Symbol">;</a> <a id="9451" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="9456" class="Symbol">;</a> <a id="9458" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="9460" class="Symbol">)</a>
</pre>{% endraw %}
The first line brings the standard library module that defines
equality into scope and gives it the name `Eq`. The second line
opens that module, that is, adds all the names specified in the
`using` clause into the current scope. In this case the names added
are `_≡_`, the equality operator, and `refl`, the name for evidence
that two terms are equal.  The third line takes a module that
specifies operators to support reasoning about equivalence, and adds
all the names specified in the `using` clause into the current scope.
In this case, the names added are `begin_`, `_≡⟨⟩_`, and `_∎`.  We
will see how these are used below.  We take these as givens for now,
but will see how they are defined in
Chapter [Equality]({{ site.baseurl }}/Equality/).

Agda uses underbars to indicate where terms appear in infix or mixfix
operators. Thus, `_≡_` and `_≡⟨⟩_` are infix (each operator is written
between two terms), while `begin_` is prefix (it is written before a
term), and `_∎` is postfix (it is written after a term).

Parentheses and semicolons are among the few characters that cannot
appear in names, so we do not need extra spaces in the `using` list.


## Operations on naturals are recursive functions {#plus}

Now that we have the natural numbers, what can we do with them?
For instance, can we define arithmetic operations such as
addition and multiplication?

As a child I spent much time memorising tables of addition and
multiplication.  At first the rules seemed tricky and I would often
make mistakes.  It came as a shock to me to discover _recursion_,
a simple technique by which every one of the infinite possible
instances of addition and multiplication can be specified in
just a couple of lines.

Here is the definition of addition in Agda:
{% raw %}<pre class="Agda"><a id="_+_"></a><a id="11231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#11231" class="Function Operator">_+_</a> <a id="11235" class="Symbol">:</a> <a id="11237" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a> <a id="11239" class="Symbol">→</a> <a id="11241" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a> <a id="11243" class="Symbol">→</a> <a id="11245" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a>
<a id="11247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1123" class="InductiveConstructor">zero</a> <a id="11252" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="11254" href="plfa.Naturals.html#11254" class="Bound">n</a> <a id="11256" class="Symbol">=</a> <a id="11258" href="plfa.Naturals.html#11254" class="Bound">n</a>
<a id="11260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a> <a id="11264" href="plfa.Naturals.html#11264" class="Bound">m</a> <a id="11266" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="11268" href="plfa.Naturals.html#11268" class="Bound">n</a> <a id="11270" class="Symbol">=</a> <a id="11272" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="11276" class="Symbol">(</a><a id="11277" href="plfa.Naturals.html#11264" class="Bound">m</a> <a id="11279" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="11281" href="plfa.Naturals.html#11268" class="Bound">n</a><a id="11282" class="Symbol">)</a>
</pre>{% endraw %}
Let's unpack this definition.  Addition is an infix operator.  It is
written with underbars where the argument go, hence its name is
`_+_`.  The first line is a signature specifying the type of the operator.
The type `ℕ → ℕ → ℕ`, indicates that addition accepts two naturals
and returns a natural.  Infix notation is just a shorthand for application;
the terms `m + n` and `_+_ m n` are equivalent.

The definition has a base case and an inductive case, corresponding to
those for the natural numbers.  The base case says that adding zero to
a number, `zero + n`, returns that number, `n`.  The inductive case
says that adding the successor of a number to another number,
`(suc m) + n`, returns the successor of adding the two numbers, `suc (m + n)`.
We say we use _pattern matching_ when constructors appear on the
left-hand side of an equation.

If we write `zero` as `0` and `suc m` as `1 + m`, the definition turns
into two familiar equations:

     0       + n  ≡  n
     (1 + m) + n  ≡  1 + (m + n)

The first follows because zero is an identity for addition, and the
second because addition is associative.  In its most general form,
associativity is written

     (m + n) + p  ≡  m + (n + p)

meaning that the location of parentheses is irrelevant.  We get the
second equation from the third by taking `m` to be `1`, `n` to be `m`,
and `p` to be `n`.  We write `=` for definitions, while we
write `≡` for assertions that two already defined things are the same.

The definition is _recursive_, in that the last line defines addition
in terms of addition.  As with the inductive definition of the
naturals, the apparent circularity is not a problem.  It works because
addition of larger numbers is defined in terms of addition of smaller
numbers.  Such a definition is called _well founded_.

For example, let's add two and three:
{% raw %}<pre class="Agda"><a id="13131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#13131" class="Function">_</a> <a id="13133" class="Symbol">:</a> <a id="13135" class="Number">2</a> <a id="13137" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="13139" class="Number">3</a> <a id="13141" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13143" class="Number">5</a>
<a id="13145" class="Symbol">_</a> <a id="13147" class="Symbol">=</a>
  <a id="13151" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="13161" class="Number">2</a> <a id="13163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#11231" class="Function Operator">+</a> <a id="13165" class="Number">3</a>
  <a id="13169" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>    <a id="13176" class="Comment">-- is shorthand for</a>
    <a id="13200" class="Symbol">(</a><a id="13201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a> <a id="13205" class="Symbol">(</a><a id="13206" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13210" href="plfa.Naturals.html#1123" class="InductiveConstructor">zero</a><a id="13214" class="Symbol">))</a> <a id="13217" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="13219" class="Symbol">(</a><a id="13220" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13224" class="Symbol">(</a><a id="13225" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13229" class="Symbol">(</a><a id="13230" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13234" href="plfa.Naturals.html#1123" class="InductiveConstructor">zero</a><a id="13238" class="Symbol">)))</a>
  <a id="13244" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>    <a id="13251" class="Comment">-- inductive case</a>
    <a id="13273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a> <a id="13277" class="Symbol">((</a><a id="13279" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13283" href="plfa.Naturals.html#1123" class="InductiveConstructor">zero</a><a id="13287" class="Symbol">)</a> <a id="13289" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="13291" class="Symbol">(</a><a id="13292" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13296" class="Symbol">(</a><a id="13297" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13301" class="Symbol">(</a><a id="13302" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13306" href="plfa.Naturals.html#1123" class="InductiveConstructor">zero</a><a id="13310" class="Symbol">))))</a>
  <a id="13317" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>    <a id="13324" class="Comment">-- inductive case</a>
    <a id="13346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a> <a id="13350" class="Symbol">(</a><a id="13351" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13355" class="Symbol">(</a><a id="13356" href="plfa.Naturals.html#1123" class="InductiveConstructor">zero</a> <a id="13361" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="13363" class="Symbol">(</a><a id="13364" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13368" class="Symbol">(</a><a id="13369" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13373" class="Symbol">(</a><a id="13374" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13378" href="plfa.Naturals.html#1123" class="InductiveConstructor">zero</a><a id="13382" class="Symbol">)))))</a>
  <a id="13390" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>    <a id="13397" class="Comment">-- base case</a>
    <a id="13414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a> <a id="13418" class="Symbol">(</a><a id="13419" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13423" class="Symbol">(</a><a id="13424" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13428" class="Symbol">(</a><a id="13429" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13433" class="Symbol">(</a><a id="13434" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13438" href="plfa.Naturals.html#1123" class="InductiveConstructor">zero</a><a id="13442" class="Symbol">))))</a>
  <a id="13449" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>    <a id="13456" class="Comment">-- is longhand for</a>
    <a id="13479" class="Number">5</a>
  <a id="13483" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}We can write the same derivation more compactly by only
expanding shorthand as needed:
{% raw %}<pre class="Agda"><a id="13580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#13580" class="Function">_</a> <a id="13582" class="Symbol">:</a> <a id="13584" class="Number">2</a> <a id="13586" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="13588" class="Number">3</a> <a id="13590" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13592" class="Number">5</a>
<a id="13594" class="Symbol">_</a> <a id="13596" class="Symbol">=</a>
  <a id="13600" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="13610" class="Number">2</a> <a id="13612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#11231" class="Function Operator">+</a> <a id="13614" class="Number">3</a>
  <a id="13618" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="13626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a> <a id="13630" class="Symbol">(</a><a id="13631" class="Number">1</a> <a id="13633" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="13635" class="Number">3</a><a id="13636" class="Symbol">)</a>
  <a id="13640" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="13648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a> <a id="13652" class="Symbol">(</a><a id="13653" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13657" class="Symbol">(</a><a id="13658" class="Number">0</a> <a id="13660" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="13662" class="Number">3</a><a id="13663" class="Symbol">))</a>
  <a id="13668" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="13676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a> <a id="13680" class="Symbol">(</a><a id="13681" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="13685" class="Number">3</a><a id="13686" class="Symbol">)</a>
  <a id="13690" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="13698" class="Number">5</a>
  <a id="13702" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The first line matches the inductive case by taking `m = 1` and `n = 3`,
the second line matches the inductive case by taking `m = 0` and `n = 3`,
and the third line matches the base case by taking `n = 3`.

Both derivations consist of a signature (written with a colon, `:`),
giving a type, and a binding (written with an equal sign, `=`),
giving a term of the given type.  Here we use the dummy name `_`.  The
dummy name can be reused, and is convenient for examples.  Names other
than `_` must be used only once in a module.

Here the type is `2 + 3 ≡ 5` and the term provides _evidence_ for the
corresponding equation, here written in tabular form as a chain of
equations.  The chain starts with `begin` and finishes with `∎`
(pronounced "qed" or "tombstone", the latter from its appearance), and
consists of a series of terms separated by `≡⟨⟩`.

In fact, both proofs are longer than need be, and Agda is satisfied
with the following:
{% raw %}<pre class="Agda"><a id="14652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#14652" class="Function">_</a> <a id="14654" class="Symbol">:</a> <a id="14656" class="Number">2</a> <a id="14658" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="14660" class="Number">3</a> <a id="14662" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14664" class="Number">5</a>
<a id="14666" class="Symbol">_</a> <a id="14668" class="Symbol">=</a> <a id="14670" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}Agda knows how to
compute the value of `2 + 3`, and so can immediately
check it is the same as `5`.  A binary relation is said to be _reflexive_
if every value relates to itself.  Evidence that a value is equal to
itself is written `refl`.

In the chains of equations, all Agda checks is that each term
simplifies to the same value. If we jumble the equations, omit lines, or
add extraneous lines it will still be accepted.  It's up to us to write
the equations in an order that makes sense to the reader.

Here `2 + 3 ≡ 5` is a type, and the chains of equations (and also
`refl`) are terms of the given type; alternatively, one can think of
each term as _evidence_ for the assertion `2 + 3 ≡ 5`.  This duality
of interpretation---of a type as a proposition, and of a term as
evidence---is central to how we formalise concepts in Agda, and will
be a running theme throughout this book.

Note that when we use the word _evidence_ it is nothing equivocal.  It
is not like testimony in a court which must be weighed to determine
whether the witness is trustworthy.  Rather, it is ironclad.  The
other word for evidence, which we will use interchangeably, is _proof_.

#### Exercise `+-example` {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.

{% raw %}<pre class="Agda"><a id="15961" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Multiplication

Once we have defined addition, we can define multiplication
as repeated addition:
{% raw %}<pre class="Agda"><a id="_*_"></a><a id="16095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#16095" class="Function Operator">_*_</a> <a id="16099" class="Symbol">:</a> <a id="16101" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a> <a id="16103" class="Symbol">→</a> <a id="16105" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a> <a id="16107" class="Symbol">→</a> <a id="16109" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a>
<a id="16111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1123" class="InductiveConstructor">zero</a>    <a id="16119" href="plfa.Naturals.html#16095" class="Function Operator">*</a> <a id="16121" href="plfa.Naturals.html#16121" class="Bound">n</a>  <a id="16124" class="Symbol">=</a>  <a id="16127" href="plfa.Naturals.html#1123" class="InductiveConstructor">zero</a>
<a id="16132" class="Symbol">(</a><a id="16133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a> <a id="16137" href="plfa.Naturals.html#16137" class="Bound">m</a><a id="16138" class="Symbol">)</a> <a id="16140" href="plfa.Naturals.html#16095" class="Function Operator">*</a> <a id="16142" href="plfa.Naturals.html#16142" class="Bound">n</a>  <a id="16145" class="Symbol">=</a>  <a id="16148" href="plfa.Naturals.html#16142" class="Bound">n</a> <a id="16150" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="16152" class="Symbol">(</a><a id="16153" href="plfa.Naturals.html#16137" class="Bound">m</a> <a id="16155" href="plfa.Naturals.html#16095" class="Function Operator">*</a> <a id="16157" href="plfa.Naturals.html#16142" class="Bound">n</a><a id="16158" class="Symbol">)</a>
</pre>{% endraw %}Computing `m * n` returns the sum of `m` copies of `n`.

Again, rewriting turns the definition into two familiar equations:

    0       * n  ≡  0
    (1 + m) * n  ≡  n + (m * n)

The first follows because zero times anything is zero, and the second
follows because multiplication distributes over addition.
In its most general form, distribution of multiplication over addition
is written

    (m + n) * p  ≡  (m * p) + (n * p)

We get the second equation from the third by taking `m` to be `1`, `n`
to be `m`, and `p` to be `n`, and then using the fact that one is an
identity for multiplication, so `1 * n ≡ n`.

Again, the definition is well-founded in that multiplication of
larger numbers is defined in terms of multiplication of smaller numbers.

For example, let's multiply two and three:
{% raw %}<pre class="Agda"><a id="16965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#16965" class="Function">_</a> <a id="16967" class="Symbol">=</a>
  <a id="16971" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="16981" class="Number">2</a> <a id="16983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#16095" class="Function Operator">*</a> <a id="16985" class="Number">3</a>
  <a id="16989" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>    <a id="16996" class="Comment">-- inductive case</a>
    <a id="17018" class="Number">3</a> <a id="17020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#11231" class="Function Operator">+</a> <a id="17022" class="Symbol">(</a><a id="17023" class="Number">1</a> <a id="17025" href="plfa.Naturals.html#16095" class="Function Operator">*</a> <a id="17027" class="Number">3</a><a id="17028" class="Symbol">)</a>
  <a id="17032" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>    <a id="17039" class="Comment">-- inductive case</a>
    <a id="17061" class="Number">3</a> <a id="17063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#11231" class="Function Operator">+</a> <a id="17065" class="Symbol">(</a><a id="17066" class="Number">3</a> <a id="17068" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="17070" class="Symbol">(</a><a id="17071" class="Number">0</a> <a id="17073" href="plfa.Naturals.html#16095" class="Function Operator">*</a> <a id="17075" class="Number">3</a><a id="17076" class="Symbol">))</a>
  <a id="17081" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>    <a id="17088" class="Comment">-- base case</a>
    <a id="17105" class="Number">3</a> <a id="17107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#11231" class="Function Operator">+</a> <a id="17109" class="Symbol">(</a><a id="17110" class="Number">3</a> <a id="17112" href="plfa.Naturals.html#11231" class="Function Operator">+</a> <a id="17114" class="Number">0</a><a id="17115" class="Symbol">)</a>
  <a id="17119" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>    <a id="17126" class="Comment">-- simplify</a>
    <a id="17142" class="Number">6</a>
  <a id="17146" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The first line matches the inductive case by taking `m = 1` and `n = 3`,
The second line matches the inductive case by taking `m = 0` and `n = 3`,
and the third line matches the base case by taking `n = 3`.
Here we have omitted the signature declaring `_ : 2 * 3 ≡ 6`, since
it can easily be inferred from the corresponding term.


#### Exercise `*-example` {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.

{% raw %}<pre class="Agda"><a id="17602" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations:

    m ^ 0        =  1
    m ^ (1 + n)  =  m * (m ^ n)

Check that `3 ^ 4` is `81`.

{% raw %}<pre class="Agda"><a id="17830" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}


## Monus

We can also define subtraction.  Since there are no negative
natural numbers, if we subtract a larger number from a smaller
number we will take the result to be zero.  This adaption of
subtraction to naturals is called _monus_ (a twist on _minus_).

Monus is our first use of a definition that uses pattern
matching against both arguments:
{% raw %}<pre class="Agda"><a id="_∸_"></a><a id="18214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#18214" class="Function Operator">_∸_</a> <a id="18218" class="Symbol">:</a> <a id="18220" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a> <a id="18222" class="Symbol">→</a> <a id="18224" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a> <a id="18226" class="Symbol">→</a> <a id="18228" href="plfa.Naturals.html#1107" class="Datatype">ℕ</a>
<a id="18230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#18230" class="Bound">m</a>     <a id="18236" href="plfa.Naturals.html#18214" class="Function Operator">∸</a> <a id="18238" href="plfa.Naturals.html#1123" class="InductiveConstructor">zero</a>   <a id="18245" class="Symbol">=</a>  <a id="18248" href="plfa.Naturals.html#18230" class="Bound">m</a>
<a id="18250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1123" class="InductiveConstructor">zero</a>  <a id="18256" href="plfa.Naturals.html#18214" class="Function Operator">∸</a> <a id="18258" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="18262" href="plfa.Naturals.html#18262" class="Bound">n</a>  <a id="18265" class="Symbol">=</a>  <a id="18268" href="plfa.Naturals.html#1123" class="InductiveConstructor">zero</a>
<a id="18273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#1134" class="InductiveConstructor">suc</a> <a id="18277" href="plfa.Naturals.html#18277" class="Bound">m</a> <a id="18279" href="plfa.Naturals.html#18214" class="Function Operator">∸</a> <a id="18281" href="plfa.Naturals.html#1134" class="InductiveConstructor">suc</a> <a id="18285" href="plfa.Naturals.html#18285" class="Bound">n</a>  <a id="18288" class="Symbol">=</a>  <a id="18291" href="plfa.Naturals.html#18277" class="Bound">m</a> <a id="18293" href="plfa.Naturals.html#18214" class="Function Operator">∸</a> <a id="18295" href="plfa.Naturals.html#18285" class="Bound">n</a>
</pre>{% endraw %}We can do a simple analysis to show that all the cases are covered.

  * Consider the second argument.
    + If it is `zero`, then the first equation applies.
    + If it is `suc n`, then consider the first argument.
      - If it is `zero`, then the second equation applies.
      - If it is `suc m`, then the third equation applies.

Again, the recursive definition is well-founded because
monus on bigger numbers is defined in terms of monus on
smaller numbers.

For example, let's subtract two from three:
{% raw %}<pre class="Agda"><a id="18815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#18815" class="Function">_</a> <a id="18817" class="Symbol">=</a>
  <a id="18821" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
     <a id="18832" class="Number">3</a> <a id="18834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#18214" class="Function Operator">∸</a> <a id="18836" class="Number">2</a>
  <a id="18840" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
     <a id="18849" class="Number">2</a> <a id="18851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#18214" class="Function Operator">∸</a> <a id="18853" class="Number">1</a>
  <a id="18857" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
     <a id="18866" class="Number">1</a> <a id="18868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#18214" class="Function Operator">∸</a> <a id="18870" class="Number">0</a>
  <a id="18874" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
     <a id="18883" class="Number">1</a>
  <a id="18887" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}We did not use the second equation at all, but it will be required
if we try to subtract a larger number from a smaller one:
{% raw %}<pre class="Agda"><a id="19022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#19022" class="Function">_</a> <a id="19024" class="Symbol">=</a>
  <a id="19028" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
     <a id="19039" class="Number">2</a> <a id="19041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#18214" class="Function Operator">∸</a> <a id="19043" class="Number">3</a>
  <a id="19047" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
     <a id="19056" class="Number">1</a> <a id="19058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#18214" class="Function Operator">∸</a> <a id="19060" class="Number">2</a>
  <a id="19064" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
     <a id="19073" class="Number">0</a> <a id="19075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#18214" class="Function Operator">∸</a> <a id="19077" class="Number">1</a>
  <a id="19081" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
     <a id="19090" class="Number">0</a>
  <a id="19094" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.

{% raw %}<pre class="Agda"><a id="19247" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Precedence

We often use _precedence_ to avoid writing too many parentheses.
Application _binds more tightly than_ (or _has precedence over_) any
operator, and so we may write `suc m + n` to mean `(suc m) + n`.
As another example, we say that multiplication binds more tightly than
addition, and so write `n + m * n` to mean `n + (m * n)`.
We also sometimes say that addition _associates to the left_, and
so write `m + n + p` to mean `(m + n) + p`.

In Agda the precedence and associativity of infix operators
needs to be declared:
{% raw %}<pre class="Agda"><a id="19816" class="Keyword">infixl</a> <a id="19823" class="Number">6</a>  <a id="19826" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#11231" class="Primitive Operator">_+_</a>  <a id="19831" href="plfa.Naturals.html#18214" class="Primitive Operator">_∸_</a>
<a id="19835" class="Keyword">infixl</a> <a id="19842" class="Number">7</a>  <a id="19845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#16095" class="Primitive Operator">_*_</a>
</pre>{% endraw %}This states operators `_+_` and `_∸_` have precedence level 6,
and operator `_*_` has precedence level 7.
Addition and monus bind less tightly than multiplication
because they have lower precedence.
Writing `infixl` indicates that all three
operators associate to the left.  One can also write `infixr` to
indicate that an operator associates to the right, or just `infix` to
indicate that parentheses are always required to disambiguate.


## Currying

We have chosen to represent a function of two arguments in terms
of a function of the first argument that returns a function of the
second argument.  This trick goes by the name _currying_.

Agda, like other functional languages such as Haskell and ML,
is designed to make currying easy to use.  Function
arrows associate to the right and application associates to the left

`ℕ → ℕ → ℕ` stands for `ℕ → (ℕ → ℕ)`

and

`_+_ 2 3` stands for `(_+_ 2) 3`.

The term `_+_ 2` by itself stands for the function that adds two to
its argument, hence applying it to three yields five.

Currying is named for Haskell Curry, after whom the programming
language Haskell is also named.  Curry's work dates to the 1930's.
When I first learned about currying, I was told it was misattributed,
since the same idea was previously proposed by Moses Schönfinkel in
the 1920's.  I was told a joke: "It should be called schönfinkeling,
but currying is tastier". Only later did I learn that the explanation
of the misattribution was itself a misattribution.  The idea actually
appears in the _Begriffschrift_ of Gottlob Frege, published in 1879.

## The story of creation, revisited

Just as our inductive definition defines the naturals in terms of the
naturals, so does our recursive definition define addition in terms
of addition.

Again, it is possible to assign our definition a meaning without
resorting to unpermitted circularities.  We do so by reducing our
definition to equivalent inference rules for judgments about equality:

    n : ℕ
    --------------
    zero + n  =  n

    m + n  =  p
    ---------------------
    (suc m) + n  =  suc p

Here we assume we have already defined the infinite set of natural
numbers, specifying the meaning of the judgment `n : ℕ`.  The first
inference rule is the base case.  It asserts that if `n` is a natural number
then adding zero to it gives `n`.  The second inference rule is the inductive
case. It asserts that if adding `m` and `n` gives `p`, then adding `suc m` and
`n` gives `suc p`.

Again we resort to a creation story, where this time we are
concerned with judgments about addition:

    -- In the beginning, we know nothing about addition.

Now, we apply the rules to all the judgment we know about.
The base case tells us that `zero + n = n` for every natural `n`,
so we add all those equations.  The inductive case tells us that if
`m + n = p` (on the day before today) then `suc m + n = suc p`
(today).  We didn't know any equations about addition before today,
so that rule doesn't give us any new equations:

    -- On the first day, we know about addition of 0.
    0 + 0 = 0     0 + 1 = 1    0 + 2 = 2     ...

Then we repeat the process, so on the next day we know about all the
equations from the day before, plus any equations added by the rules.
The base case tells us nothing new, but now the inductive case adds
more equations:

    -- On the second day, we know about addition of 0 and 1.
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...

And we repeat the process again:

    -- On the third day, we know about addition of 0, 1, and 2.
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
    2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...

You've got the hang of it by now:

    -- On the fourth day, we know about addition of 0, 1, 2, and 3.
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
    2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...
    3 + 0 = 3     3 + 1 = 4     3 + 2 = 5     3 + 3 = 6     ...

The process continues.  On the _m_'th day we will know all the
equations where the first number is less than _m_.

As we can see, the reasoning that justifies inductive and recursive
definitions is quite similar.  They might be considered two sides of
the same coin.


## The story of creation, finitely {#finite-creation}

The above story was told in a stratified way.  First, we create
the infinite set of naturals.  We take that set as given when
creating instances of addition, so even on day one we have an
infinite set of instances.

Instead, we could choose to create both the naturals and the instances
of addition at the same time. Then on any day there would be only
a finite set of instances:

    -- In the beginning, we know nothing.

Now, we apply the rules to all the judgment we know about.  Only the
base case for naturals applies:

    -- On the first day, we know zero.
    0 : ℕ

Again, we apply all the rules we know.  This gives us a new natural,
and our first equation about addition.

    -- On the second day, we know one and all sums that yield zero.
    0 : ℕ
    1 : ℕ    0 + 0 = 0

Then we repeat the process.  We get one more equation about addition
from the base case, and also get an equation from the inductive case,
applied to equation of the previous day:

    -- On the third day, we know two and all sums that yield one.
    0 : ℕ
    1 : ℕ    0 + 0 = 0
    2 : ℕ    0 + 1 = 1   1 + 0 = 1

You've got the hang of it by now:

    -- On the fourth day, we know three and all sums that yield two.
    0 : ℕ
    1 : ℕ    0 + 0 = 0
    2 : ℕ    0 + 1 = 1   1 + 0 = 1
    3 : ℕ    0 + 2 = 2   1 + 1 = 2    2 + 0 = 2

On the _n_'th day there will be _n_ distinct natural numbers, and
_n × (n-1) / 2_ equations about addition.  The number _n_ and all equations
for addition of numbers less than _n_ first appear by day _n+1_.
This gives an entirely finitist view of infinite sets of data and
equations relating the data.


## Writing definitions interactively

Agda is designed to be used with the Emacs text editor, and the two
in combination provide features that help to create definitions
and proofs interactively.

Begin by typing:

    _+_ : ℕ → ℕ → ℕ
    m + n = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code. If you type `C-c C-l` (pressing
the control key while hitting the `c` key followed by the `l` key)
the question mark will be replaced:

    _+_ : ℕ → ℕ → ℕ
    m + n = { }0

The empty braces are called a *hole*, and 0 is a number used for
referring to the hole.  The hole will display highlighted in green.
Emacs will also create a window displaying the text

    ?0 : ℕ

to indicate that hole 0 is to be filled in with a term of type `ℕ`.
Typing `C-c C-f` will move you into the next hole.

We wish to define addition by recursion on the first argument.
Move the cursor into the hole and type `C-c C-c`.   You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code:

    _+_ : ℕ → ℕ → ℕ
    zero + n = { }0
    suc m + n = { }1

There are now two holes, and the window at the bottom tells you the
required type of each:

    ?0 : ℕ
    ?1 : ℕ

Going into hole 0 and type `C-c C-,` will display information on the
required type of the hole, and what free variables are available:

    Goal: ℕ
    ————————————————————————————————————————————————————————————
    n : ℕ

This strongly suggests filling the hole with `n`.  After the hole is
filled, you can type `C-c C-space`, which will remove the hole:

    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    suc m + n = { }1

Again, going into hole 1 and type `C-c C-,` will display information on the
required type of the hole, and what free variables are available:

    Goal: ℕ
    ————————————————————————————————————————————————————————————
    n : ℕ
    m : ℕ

Going into the hole and type `C-c C-r` will fill it in with a constructor
(if there is a unique choice) or tell you what constructors you might use,
if there is a choice.  In this case, it displays the following:

    Don't know which constructor to introduce of zero or suc

Filling the hole with `suc ?` and typing `C-c C-space` results in the following:

    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    suc m + n = suc { }1

Going into the new hole and typing `C-c C-,` gives similar information to before:

    Goal: ℕ
    ————————————————————————————————————————————————————————————
    n : ℕ
    m : ℕ

We can fill the hole with `m + n` and type `C-c C-space` to complete the program:

    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    suc m + n = suc (m + n)

Exploiting interaction to this degree is probably not helpful for a program this
simple, but the same techniques can help with more complex programs.  Even for
a program this simple, using `C-c C-c` to split cases can be helpful.


## More pragmas

Including the lines
{% raw %}<pre class="Agda"><a id="28976" class="Symbol">{-#</a> <a id="28980" class="Keyword">BUILTIN</a> <a id="28988" class="Pragma">NATPLUS</a> <a id="28996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#11231" class="Primitive Operator">_+_</a> <a id="29000" class="Symbol">#-}</a>
<a id="29004" class="Symbol">{-#</a> <a id="29008" class="Keyword">BUILTIN</a> <a id="29016" class="Pragma">NATTIMES</a> <a id="29025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#16095" class="Primitive Operator">_*_</a> <a id="29029" class="Symbol">#-}</a>
<a id="29033" class="Symbol">{-#</a> <a id="29037" class="Keyword">BUILTIN</a> <a id="29045" class="Pragma">NATMINUS</a> <a id="29054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#18214" class="Primitive Operator">_∸_</a> <a id="29058" class="Symbol">#-}</a>
</pre>{% endraw %}tells Agda that these three operators correspond to the usual ones,
and enables it to perform these computations using the corresponding
Haskell operators on the arbitrary-precision integer type.
Representing naturals with `zero` and `suc` requires time proportional
to _m_ to add _m_ and _n_, whereas representing naturals as integers
in Haskell requires time proportional to the larger of the logarithms
of _m_ and _n_.  Similarly, representing naturals with `zero`
and `suc` requires time proportional to the product of _m_ and _n_ to
multiply _m_ and _n_, whereas representing naturals as integers in
Haskell requires time proportional to the sum of the logarithms of
_m_ and _n_.


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring:
{% raw %}<pre class="Agda"><a id="29927" class="Keyword">data</a> <a id="Bin"></a><a id="29932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#29932" class="Datatype">Bin</a> <a id="29936" class="Symbol">:</a> <a id="29938" class="PrimitiveType">Set</a> <a id="29942" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="29950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#29950" class="InductiveConstructor">nil</a> <a id="29954" class="Symbol">:</a> <a id="29956" href="plfa.Naturals.html#29932" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="29962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#29962" class="InductiveConstructor Operator">x0_</a> <a id="29966" class="Symbol">:</a> <a id="29968" href="plfa.Naturals.html#29932" class="Datatype">Bin</a> <a id="29972" class="Symbol">→</a> <a id="29974" href="plfa.Naturals.html#29932" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="29980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Naturals.md %}{% raw %}#29980" class="InductiveConstructor Operator">x1_</a> <a id="29984" class="Symbol">:</a> <a id="29986" href="plfa.Naturals.html#29932" class="Datatype">Bin</a> <a id="29990" class="Symbol">→</a> <a id="29992" href="plfa.Naturals.html#29932" class="Datatype">Bin</a>
</pre>{% endraw %}For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as:

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have:

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

{% raw %}<pre class="Agda"><a id="30904" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

At the end of each chapter, we will show where to find relevant
definitions in the standard library.  The naturals, constructors for
them, and basic operators upon them, are defined in the standard
library module `Data.Nat`:

{% raw %}<pre class="Agda"><a id="31184" class="Comment">-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)</a>
</pre>{% endraw %}
Normally, we will show an import as running code, so Agda will
complain if we attempt to import a definition that is not available.
This time, however, we have only shown the import as a comment.  Both
this chapter and the standard library invoke the `NATURAL` pragma, the
former on `ℕ`, and the latter on the equivalent type `Data.Nat.ℕ`.
Such a pragma can only be invoked once, as invoking it twice would
raise confusion as to whether `2` is a value of type `ℕ` or type
`Data.Nat.ℕ`.  Similar confusions arise if other pragmas are invoked
twice. For this reason, we will usually avoid pragmas in future chapters.
Information on pragmas can be found in the Agda documentation.


## Unicode

This chapter uses the following unicode:

    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)
    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∸  U+2238  DOT MINUS (\.-)
    ≡  U+2261  IDENTICAL TO (\==)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)

Each line consists of the Unicode character (`ℕ`), the corresponding
code point (`U+2115`), the name of the character (`DOUBLE-STRUCK CAPITAL N`),
and the sequence to type into Emacs to generate the character (`\bN`).

The command `\r` gives access to a wide variety of rightward arrows.
After typing `\r`, one can access the many available arrows by using
the left, right, up, and down keys to navigate.  The command remembers
where you navigated to the last time, and starts with the same
character next time.  The command `\l` works similarly for left arrows.

In place of left, right, up, and down keys, one may also use control characters:

    C-b  left (backward one character)
    C-f  right (forward one character)
    C-p  up (to the previous line)
    C-n  down (to the next line)

We write `C-b` to stand for control-b, and similarly.  One can also navigate
left and right by typing the digits that appear in the displayed list.
