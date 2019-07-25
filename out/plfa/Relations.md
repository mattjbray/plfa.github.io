---
src       : "src/plfa/Relations.lagda.md"
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

{% raw %}<pre class="Agda"><a id="161" class="Keyword">module</a> <a id="168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="183" class="Keyword">where</a>
</pre>{% endraw %}
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

{% raw %}<pre class="Agda"><a id="348" class="Keyword">import</a> <a id="355" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="393" class="Symbol">as</a> <a id="396" class="Module">Eq</a>
<a id="399" class="Keyword">open</a> <a id="404" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="407" class="Keyword">using</a> <a id="413" class="Symbol">(</a><a id="414" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="417" class="Symbol">;</a> <a id="419" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="423" class="Symbol">;</a> <a id="425" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="429" class="Symbol">)</a>
<a id="431" class="Keyword">open</a> <a id="436" class="Keyword">import</a> <a id="443" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="452" class="Keyword">using</a> <a id="458" class="Symbol">(</a><a id="459" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="460" class="Symbol">;</a> <a id="462" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="466" class="Symbol">;</a> <a id="468" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="471" class="Symbol">;</a> <a id="473" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="476" class="Symbol">)</a>
<a id="478" class="Keyword">open</a> <a id="483" class="Keyword">import</a> <a id="490" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="510" class="Keyword">using</a> <a id="516" class="Symbol">(</a><a id="517" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="523" class="Symbol">)</a>
</pre>{% endraw %}

## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
{% raw %}<pre class="Agda"><a id="1184" class="Keyword">data</a> <a id="_≤_"></a><a id="1189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1189" class="Datatype Operator">_≤_</a> <a id="1193" class="Symbol">:</a> <a id="1195" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1197" class="Symbol">→</a> <a id="1199" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1201" class="Symbol">→</a> <a id="1203" class="PrimitiveType">Set</a> <a id="1207" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1216" class="InductiveConstructor">z≤n</a> <a id="1220" class="Symbol">:</a> <a id="1222" class="Symbol">∀</a> <a id="1224" class="Symbol">{</a><a id="1225" href="plfa.Relations.html#1225" class="Bound">n</a> <a id="1227" class="Symbol">:</a> <a id="1229" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1230" class="Symbol">}</a>
      <a id="1238" class="Comment">--------</a>
    <a id="1251" class="Symbol">→</a> <a id="1253" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1189" class="Datatype Operator">≤</a> <a id="1260" href="plfa.Relations.html#1225" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1265" class="InductiveConstructor">s≤s</a> <a id="1269" class="Symbol">:</a> <a id="1271" class="Symbol">∀</a> <a id="1273" class="Symbol">{</a><a id="1274" href="plfa.Relations.html#1274" class="Bound">m</a> <a id="1276" href="plfa.Relations.html#1276" class="Bound">n</a> <a id="1278" class="Symbol">:</a> <a id="1280" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1281" class="Symbol">}</a>
    <a id="1287" class="Symbol">→</a> <a id="1289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1274" class="Bound">m</a> <a id="1291" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="1293" href="plfa.Relations.html#1276" class="Bound">n</a>
      <a id="1301" class="Comment">-------------</a>
    <a id="1319" class="Symbol">→</a> <a id="1321" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1274" class="Bound">m</a> <a id="1327" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="1329" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1333" href="plfa.Relations.html#1276" class="Bound">n</a>
</pre>{% endraw %}Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`:

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof:
{% raw %}<pre class="Agda"><a id="2595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#2595" class="Function">_</a> <a id="2597" class="Symbol">:</a> <a id="2599" class="Number">2</a> <a id="2601" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="2603" class="Number">4</a>
<a id="2605" class="Symbol">_</a> <a id="2607" class="Symbol">=</a> <a id="2609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1265" class="InductiveConstructor">s≤s</a> <a id="2613" class="Symbol">(</a><a id="2614" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="2618" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a><a id="2621" class="Symbol">)</a>
</pre>{% endraw %}



## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
{% raw %}<pre class="Agda"><a id="3600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3600" class="Function">_</a> <a id="3602" class="Symbol">:</a> <a id="3604" class="Number">2</a> <a id="3606" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="3608" class="Number">4</a>
<a id="3610" class="Symbol">_</a> <a id="3612" class="Symbol">=</a> <a id="3614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1265" class="InductiveConstructor">s≤s</a> <a id="3618" class="Symbol">{</a><a id="3619" class="Number">1</a><a id="3620" class="Symbol">}</a> <a id="3622" class="Symbol">{</a><a id="3623" class="Number">3</a><a id="3624" class="Symbol">}</a> <a id="3626" class="Symbol">(</a><a id="3627" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="3631" class="Symbol">{</a><a id="3632" class="Number">0</a><a id="3633" class="Symbol">}</a> <a id="3635" class="Symbol">{</a><a id="3636" class="Number">2</a><a id="3637" class="Symbol">}</a> <a id="3639" class="Symbol">(</a><a id="3640" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a> <a id="3644" class="Symbol">{</a><a id="3645" class="Number">2</a><a id="3646" class="Symbol">}))</a>
</pre>{% endraw %}One may also identify implicit arguments by name:
{% raw %}<pre class="Agda"><a id="3708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3708" class="Function">_</a> <a id="3710" class="Symbol">:</a> <a id="3712" class="Number">2</a> <a id="3714" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="3716" class="Number">4</a>
<a id="3718" class="Symbol">_</a> <a id="3720" class="Symbol">=</a> <a id="3722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1265" class="InductiveConstructor">s≤s</a> <a id="3726" class="Symbol">{</a><a id="3727" class="Argument">m</a> <a id="3729" class="Symbol">=</a> <a id="3731" class="Number">1</a><a id="3732" class="Symbol">}</a> <a id="3734" class="Symbol">{</a><a id="3735" class="Argument">n</a> <a id="3737" class="Symbol">=</a> <a id="3739" class="Number">3</a><a id="3740" class="Symbol">}</a> <a id="3742" class="Symbol">(</a><a id="3743" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="3747" class="Symbol">{</a><a id="3748" class="Argument">m</a> <a id="3750" class="Symbol">=</a> <a id="3752" class="Number">0</a><a id="3753" class="Symbol">}</a> <a id="3755" class="Symbol">{</a><a id="3756" class="Argument">n</a> <a id="3758" class="Symbol">=</a> <a id="3760" class="Number">2</a><a id="3761" class="Symbol">}</a> <a id="3763" class="Symbol">(</a><a id="3764" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a> <a id="3768" class="Symbol">{</a><a id="3769" class="Argument">n</a> <a id="3771" class="Symbol">=</a> <a id="3773" class="Number">2</a><a id="3774" class="Symbol">}))</a>
</pre>{% endraw %}In the latter format, you may only supply some implicit arguments:
{% raw %}<pre class="Agda"><a id="3853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3853" class="Function">_</a> <a id="3855" class="Symbol">:</a> <a id="3857" class="Number">2</a> <a id="3859" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="3861" class="Number">4</a>
<a id="3863" class="Symbol">_</a> <a id="3865" class="Symbol">=</a> <a id="3867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1265" class="InductiveConstructor">s≤s</a> <a id="3871" class="Symbol">{</a><a id="3872" class="Argument">n</a> <a id="3874" class="Symbol">=</a> <a id="3876" class="Number">3</a><a id="3877" class="Symbol">}</a> <a id="3879" class="Symbol">(</a><a id="3880" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="3884" class="Symbol">{</a><a id="3885" class="Argument">n</a> <a id="3887" class="Symbol">=</a> <a id="3889" class="Number">2</a><a id="3890" class="Symbol">}</a> <a id="3892" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a><a id="3895" class="Symbol">)</a>
</pre>{% endraw %}It is not permitted to swap implicit arguments, even when named.


## Precedence

We declare the precedence for comparison as follows:
{% raw %}<pre class="Agda"><a id="4040" class="Keyword">infix</a> <a id="4046" class="Number">4</a> <a id="4048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1189" class="Datatype Operator">_≤_</a>
</pre>{% endraw %}We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}/Decidable/).


## Inversion

In our defintions, we go from smaller things to larger things.
For instance, form `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
{% raw %}<pre class="Agda"><a id="inv-s≤s"></a><a id="5065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5065" class="Function">inv-s≤s</a> <a id="5073" class="Symbol">:</a> <a id="5075" class="Symbol">∀</a> <a id="5077" class="Symbol">{</a><a id="5078" href="plfa.Relations.html#5078" class="Bound">m</a> <a id="5080" href="plfa.Relations.html#5080" class="Bound">n</a> <a id="5082" class="Symbol">:</a> <a id="5084" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5085" class="Symbol">}</a>
  <a id="5089" class="Symbol">→</a> <a id="5091" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5078" class="Bound">m</a> <a id="5097" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="5099" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5103" href="plfa.Relations.html#5080" class="Bound">n</a>
    <a id="5109" class="Comment">-------------</a>
  <a id="5125" class="Symbol">→</a> <a id="5127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5078" class="Bound">m</a> <a id="5129" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="5131" href="plfa.Relations.html#5080" class="Bound">n</a>
<a id="5133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5065" class="Function">inv-s≤s</a> <a id="5141" class="Symbol">(</a><a id="5142" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="5146" href="plfa.Relations.html#5146" class="Bound">m≤n</a><a id="5149" class="Symbol">)</a> <a id="5151" class="Symbol">=</a> <a id="5153" href="plfa.Relations.html#5146" class="Bound">m≤n</a>
</pre>{% endraw %}Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.

Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
{% raw %}<pre class="Agda"><a id="inv-z≤n"></a><a id="5437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5437" class="Function">inv-z≤n</a> <a id="5445" class="Symbol">:</a> <a id="5447" class="Symbol">∀</a> <a id="5449" class="Symbol">{</a><a id="5450" href="plfa.Relations.html#5450" class="Bound">m</a> <a id="5452" class="Symbol">:</a> <a id="5454" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5455" class="Symbol">}</a>
  <a id="5459" class="Symbol">→</a> <a id="5461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5450" class="Bound">m</a> <a id="5463" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="5465" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
    <a id="5474" class="Comment">--------</a>
  <a id="5485" class="Symbol">→</a> <a id="5487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5450" class="Bound">m</a> <a id="5489" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5491" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
<a id="5496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5437" class="Function">inv-z≤n</a> <a id="5504" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a> <a id="5508" class="Symbol">=</a> <a id="5510" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

{% raw %}<pre class="Agda"><a id="7001" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
Give an example of a partial order that is not a total order.

{% raw %}<pre class="Agda"><a id="7096" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
{% raw %}<pre class="Agda"><a id="≤-refl"></a><a id="7396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7396" class="Function">≤-refl</a> <a id="7403" class="Symbol">:</a> <a id="7405" class="Symbol">∀</a> <a id="7407" class="Symbol">{</a><a id="7408" href="plfa.Relations.html#7408" class="Bound">n</a> <a id="7410" class="Symbol">:</a> <a id="7412" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7413" class="Symbol">}</a>
    <a id="7419" class="Comment">-----</a>
  <a id="7427" class="Symbol">→</a> <a id="7429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7408" class="Bound">n</a> <a id="7431" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="7433" href="plfa.Relations.html#7408" class="Bound">n</a>
<a id="7435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7396" class="Function">≤-refl</a> <a id="7442" class="Symbol">{</a><a id="7443" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="7447" class="Symbol">}</a> <a id="7449" class="Symbol">=</a> <a id="7451" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="7455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7396" class="Function">≤-refl</a> <a id="7462" class="Symbol">{</a><a id="7463" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7467" href="plfa.Relations.html#7467" class="Bound">n</a><a id="7468" class="Symbol">}</a> <a id="7470" class="Symbol">=</a> <a id="7472" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="7476" href="plfa.Relations.html#7396" class="Function">≤-refl</a>
</pre>{% endraw %}The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
{% raw %}<pre class="Agda"><a id="≤-trans"></a><a id="8113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8113" class="Function">≤-trans</a> <a id="8121" class="Symbol">:</a> <a id="8123" class="Symbol">∀</a> <a id="8125" class="Symbol">{</a><a id="8126" href="plfa.Relations.html#8126" class="Bound">m</a> <a id="8128" href="plfa.Relations.html#8128" class="Bound">n</a> <a id="8130" href="plfa.Relations.html#8130" class="Bound">p</a> <a id="8132" class="Symbol">:</a> <a id="8134" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8135" class="Symbol">}</a>
  <a id="8139" class="Symbol">→</a> <a id="8141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8126" class="Bound">m</a> <a id="8143" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="8145" href="plfa.Relations.html#8128" class="Bound">n</a>
  <a id="8149" class="Symbol">→</a> <a id="8151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8128" class="Bound">n</a> <a id="8153" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="8155" href="plfa.Relations.html#8130" class="Bound">p</a>
    <a id="8161" class="Comment">-----</a>
  <a id="8169" class="Symbol">→</a> <a id="8171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8126" class="Bound">m</a> <a id="8173" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="8175" href="plfa.Relations.html#8130" class="Bound">p</a>
<a id="8177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8113" class="Function">≤-trans</a> <a id="8185" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>       <a id="8195" class="Symbol">_</a>          <a id="8206" class="Symbol">=</a>  <a id="8209" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="8213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8113" class="Function">≤-trans</a> <a id="8221" class="Symbol">(</a><a id="8222" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="8226" href="plfa.Relations.html#8226" class="Bound">m≤n</a><a id="8229" class="Symbol">)</a> <a id="8231" class="Symbol">(</a><a id="8232" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="8236" href="plfa.Relations.html#8236" class="Bound">n≤p</a><a id="8239" class="Symbol">)</a>  <a id="8242" class="Symbol">=</a>  <a id="8245" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="8249" class="Symbol">(</a><a id="8250" href="plfa.Relations.html#8113" class="Function">≤-trans</a> <a id="8258" href="plfa.Relations.html#8226" class="Bound">m≤n</a> <a id="8262" href="plfa.Relations.html#8236" class="Bound">n≤p</a><a id="8265" class="Symbol">)</a>
</pre>{% endraw %}Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit:
{% raw %}<pre class="Agda"><a id="≤-trans′"></a><a id="9226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9226" class="Function">≤-trans′</a> <a id="9235" class="Symbol">:</a> <a id="9237" class="Symbol">∀</a> <a id="9239" class="Symbol">(</a><a id="9240" href="plfa.Relations.html#9240" class="Bound">m</a> <a id="9242" href="plfa.Relations.html#9242" class="Bound">n</a> <a id="9244" href="plfa.Relations.html#9244" class="Bound">p</a> <a id="9246" class="Symbol">:</a> <a id="9248" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9249" class="Symbol">)</a>
  <a id="9253" class="Symbol">→</a> <a id="9255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9240" class="Bound">m</a> <a id="9257" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="9259" href="plfa.Relations.html#9242" class="Bound">n</a>
  <a id="9263" class="Symbol">→</a> <a id="9265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9242" class="Bound">n</a> <a id="9267" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="9269" href="plfa.Relations.html#9244" class="Bound">p</a>
    <a id="9275" class="Comment">-----</a>
  <a id="9283" class="Symbol">→</a> <a id="9285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9240" class="Bound">m</a> <a id="9287" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="9289" href="plfa.Relations.html#9244" class="Bound">p</a>
<a id="9291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9226" class="Function">≤-trans′</a> <a id="9300" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="9308" class="Symbol">_</a>       <a id="9316" class="Symbol">_</a>       <a id="9324" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>       <a id="9334" class="Symbol">_</a>          <a id="9345" class="Symbol">=</a>  <a id="9348" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="9352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9226" class="Function">≤-trans′</a> <a id="9361" class="Symbol">(</a><a id="9362" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9366" href="plfa.Relations.html#9366" class="Bound">m</a><a id="9367" class="Symbol">)</a> <a id="9369" class="Symbol">(</a><a id="9370" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9374" href="plfa.Relations.html#9374" class="Bound">n</a><a id="9375" class="Symbol">)</a> <a id="9377" class="Symbol">(</a><a id="9378" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9382" href="plfa.Relations.html#9382" class="Bound">p</a><a id="9383" class="Symbol">)</a> <a id="9385" class="Symbol">(</a><a id="9386" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="9390" href="plfa.Relations.html#9390" class="Bound">m≤n</a><a id="9393" class="Symbol">)</a> <a id="9395" class="Symbol">(</a><a id="9396" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="9400" href="plfa.Relations.html#9400" class="Bound">n≤p</a><a id="9403" class="Symbol">)</a>  <a id="9406" class="Symbol">=</a>  <a id="9409" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="9413" class="Symbol">(</a><a id="9414" href="plfa.Relations.html#9226" class="Function">≤-trans′</a> <a id="9423" href="plfa.Relations.html#9366" class="Bound">m</a> <a id="9425" href="plfa.Relations.html#9374" class="Bound">n</a> <a id="9427" href="plfa.Relations.html#9382" class="Bound">p</a> <a id="9429" href="plfa.Relations.html#9390" class="Bound">m≤n</a> <a id="9433" href="plfa.Relations.html#9400" class="Bound">n≤p</a><a id="9436" class="Symbol">)</a>
</pre>{% endraw %}One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
{% raw %}<pre class="Agda"><a id="≤-antisym"></a><a id="10181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10181" class="Function">≤-antisym</a> <a id="10191" class="Symbol">:</a> <a id="10193" class="Symbol">∀</a> <a id="10195" class="Symbol">{</a><a id="10196" href="plfa.Relations.html#10196" class="Bound">m</a> <a id="10198" href="plfa.Relations.html#10198" class="Bound">n</a> <a id="10200" class="Symbol">:</a> <a id="10202" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10203" class="Symbol">}</a>
  <a id="10207" class="Symbol">→</a> <a id="10209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10196" class="Bound">m</a> <a id="10211" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="10213" href="plfa.Relations.html#10198" class="Bound">n</a>
  <a id="10217" class="Symbol">→</a> <a id="10219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10198" class="Bound">n</a> <a id="10221" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="10223" href="plfa.Relations.html#10196" class="Bound">m</a>
    <a id="10229" class="Comment">-----</a>
  <a id="10237" class="Symbol">→</a> <a id="10239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10196" class="Bound">m</a> <a id="10241" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10243" href="plfa.Relations.html#10198" class="Bound">n</a>
<a id="10245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10181" class="Function">≤-antisym</a> <a id="10255" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>       <a id="10265" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>        <a id="10276" class="Symbol">=</a>  <a id="10279" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="10284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10181" class="Function">≤-antisym</a> <a id="10294" class="Symbol">(</a><a id="10295" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="10299" href="plfa.Relations.html#10299" class="Bound">m≤n</a><a id="10302" class="Symbol">)</a> <a id="10304" class="Symbol">(</a><a id="10305" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="10309" href="plfa.Relations.html#10309" class="Bound">n≤m</a><a id="10312" class="Symbol">)</a>  <a id="10315" class="Symbol">=</a>  <a id="10318" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="10323" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10327" class="Symbol">(</a><a id="10328" href="plfa.Relations.html#10181" class="Function">≤-antisym</a> <a id="10338" href="plfa.Relations.html#10299" class="Bound">m≤n</a> <a id="10342" href="plfa.Relations.html#10309" class="Bound">n≤m</a><a id="10345" class="Symbol">)</a>
</pre>{% endraw %}Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

{% raw %}<pre class="Agda"><a id="11140" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
{% raw %}<pre class="Agda"><a id="11394" class="Keyword">data</a> <a id="Total"></a><a id="11399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11399" class="Datatype">Total</a> <a id="11405" class="Symbol">(</a><a id="11406" href="plfa.Relations.html#11406" class="Bound">m</a> <a id="11408" href="plfa.Relations.html#11408" class="Bound">n</a> <a id="11410" class="Symbol">:</a> <a id="11412" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11413" class="Symbol">)</a> <a id="11415" class="Symbol">:</a> <a id="11417" class="PrimitiveType">Set</a> <a id="11421" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="11430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11430" class="InductiveConstructor">forward</a> <a id="11438" class="Symbol">:</a>
      <a id="11446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11406" class="Bound">m</a> <a id="11448" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="11450" href="plfa.Relations.html#11408" class="Bound">n</a>
      <a id="11458" class="Comment">---------</a>
    <a id="11472" class="Symbol">→</a> <a id="11474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11399" class="Datatype">Total</a> <a id="11480" href="plfa.Relations.html#11406" class="Bound">m</a> <a id="11482" href="plfa.Relations.html#11408" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="11487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11487" class="InductiveConstructor">flipped</a> <a id="11495" class="Symbol">:</a>
      <a id="11503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11408" class="Bound">n</a> <a id="11505" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="11507" href="plfa.Relations.html#11406" class="Bound">m</a>
      <a id="11515" class="Comment">---------</a>
    <a id="11529" class="Symbol">→</a> <a id="11531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11399" class="Datatype">Total</a> <a id="11537" href="plfa.Relations.html#11406" class="Bound">m</a> <a id="11539" href="plfa.Relations.html#11408" class="Bound">n</a>
</pre>{% endraw %}Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}/Connectives/).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
{% raw %}<pre class="Agda"><a id="12028" class="Keyword">data</a> <a id="Total′"></a><a id="12033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12033" class="Datatype">Total′</a> <a id="12040" class="Symbol">:</a> <a id="12042" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12044" class="Symbol">→</a> <a id="12046" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12048" class="Symbol">→</a> <a id="12050" class="PrimitiveType">Set</a> <a id="12054" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="12063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12063" class="InductiveConstructor">forward′</a> <a id="12072" class="Symbol">:</a> <a id="12074" class="Symbol">∀</a> <a id="12076" class="Symbol">{</a><a id="12077" href="plfa.Relations.html#12077" class="Bound">m</a> <a id="12079" href="plfa.Relations.html#12079" class="Bound">n</a> <a id="12081" class="Symbol">:</a> <a id="12083" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12084" class="Symbol">}</a>
    <a id="12090" class="Symbol">→</a> <a id="12092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12077" class="Bound">m</a> <a id="12094" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="12096" href="plfa.Relations.html#12079" class="Bound">n</a>
      <a id="12104" class="Comment">----------</a>
    <a id="12119" class="Symbol">→</a> <a id="12121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12033" class="Datatype">Total′</a> <a id="12128" href="plfa.Relations.html#12077" class="Bound">m</a> <a id="12130" href="plfa.Relations.html#12079" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="12135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12135" class="InductiveConstructor">flipped′</a> <a id="12144" class="Symbol">:</a> <a id="12146" class="Symbol">∀</a> <a id="12148" class="Symbol">{</a><a id="12149" href="plfa.Relations.html#12149" class="Bound">m</a> <a id="12151" href="plfa.Relations.html#12151" class="Bound">n</a> <a id="12153" class="Symbol">:</a> <a id="12155" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12156" class="Symbol">}</a>
    <a id="12162" class="Symbol">→</a> <a id="12164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12151" class="Bound">n</a> <a id="12166" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="12168" href="plfa.Relations.html#12149" class="Bound">m</a>
      <a id="12176" class="Comment">----------</a>
    <a id="12191" class="Symbol">→</a> <a id="12193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12033" class="Datatype">Total′</a> <a id="12200" href="plfa.Relations.html#12149" class="Bound">m</a> <a id="12202" href="plfa.Relations.html#12151" class="Bound">n</a>
</pre>{% endraw %}Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
{% raw %}<pre class="Agda"><a id="≤-total"></a><a id="12721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12721" class="Function">≤-total</a> <a id="12729" class="Symbol">:</a> <a id="12731" class="Symbol">∀</a> <a id="12733" class="Symbol">(</a><a id="12734" href="plfa.Relations.html#12734" class="Bound">m</a> <a id="12736" href="plfa.Relations.html#12736" class="Bound">n</a> <a id="12738" class="Symbol">:</a> <a id="12740" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12741" class="Symbol">)</a> <a id="12743" class="Symbol">→</a> <a id="12745" href="plfa.Relations.html#11399" class="Datatype">Total</a> <a id="12751" href="plfa.Relations.html#12734" class="Bound">m</a> <a id="12753" href="plfa.Relations.html#12736" class="Bound">n</a>
<a id="12755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12721" class="Function">≤-total</a> <a id="12763" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="12771" href="plfa.Relations.html#12771" class="Bound">n</a>                         <a id="12797" class="Symbol">=</a>  <a id="12800" href="plfa.Relations.html#11430" class="InductiveConstructor">forward</a> <a id="12808" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="12812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12721" class="Function">≤-total</a> <a id="12820" class="Symbol">(</a><a id="12821" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="12825" href="plfa.Relations.html#12825" class="Bound">m</a><a id="12826" class="Symbol">)</a> <a id="12828" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="12854" class="Symbol">=</a>  <a id="12857" href="plfa.Relations.html#11487" class="InductiveConstructor">flipped</a> <a id="12865" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="12869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12721" class="Function">≤-total</a> <a id="12877" class="Symbol">(</a><a id="12878" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="12882" href="plfa.Relations.html#12882" class="Bound">m</a><a id="12883" class="Symbol">)</a> <a id="12885" class="Symbol">(</a><a id="12886" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="12890" href="plfa.Relations.html#12890" class="Bound">n</a><a id="12891" class="Symbol">)</a> <a id="12893" class="Keyword">with</a> <a id="12898" href="plfa.Relations.html#12721" class="Function">≤-total</a> <a id="12906" href="plfa.Relations.html#12882" class="Bound">m</a> <a id="12908" href="plfa.Relations.html#12890" class="Bound">n</a>
<a id="12910" class="Symbol">...</a>                        <a id="12937" class="Symbol">|</a> <a id="12939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11430" class="InductiveConstructor">forward</a> <a id="12947" href="plfa.Relations.html#12947" class="Bound">m≤n</a>  <a id="12952" class="Symbol">=</a>  <a id="12955" href="plfa.Relations.html#11430" class="InductiveConstructor">forward</a> <a id="12963" class="Symbol">(</a><a id="12964" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="12968" href="plfa.Relations.html#12947" class="Bound">m≤n</a><a id="12971" class="Symbol">)</a>
<a id="12973" class="Symbol">...</a>                        <a id="13000" class="Symbol">|</a> <a id="13002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11487" class="InductiveConstructor">flipped</a> <a id="13010" href="plfa.Relations.html#13010" class="Bound">n≤m</a>  <a id="13015" class="Symbol">=</a>  <a id="13018" href="plfa.Relations.html#11487" class="InductiveConstructor">flipped</a> <a id="13026" class="Symbol">(</a><a id="13027" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="13031" href="plfa.Relations.html#13010" class="Bound">n≤m</a><a id="13034" class="Symbol">)</a>
</pre>{% endraw %}In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in https://agda.github.io/agda-stdlib/v1.1/Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
{% raw %}<pre class="Agda"><a id="≤-total′"></a><a id="14526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14526" class="Function">≤-total′</a> <a id="14535" class="Symbol">:</a> <a id="14537" class="Symbol">∀</a> <a id="14539" class="Symbol">(</a><a id="14540" href="plfa.Relations.html#14540" class="Bound">m</a> <a id="14542" href="plfa.Relations.html#14542" class="Bound">n</a> <a id="14544" class="Symbol">:</a> <a id="14546" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14547" class="Symbol">)</a> <a id="14549" class="Symbol">→</a> <a id="14551" href="plfa.Relations.html#11399" class="Datatype">Total</a> <a id="14557" href="plfa.Relations.html#14540" class="Bound">m</a> <a id="14559" href="plfa.Relations.html#14542" class="Bound">n</a>
<a id="14561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14526" class="Function">≤-total′</a> <a id="14570" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="14578" href="plfa.Relations.html#14578" class="Bound">n</a>        <a id="14587" class="Symbol">=</a>  <a id="14590" href="plfa.Relations.html#11430" class="InductiveConstructor">forward</a> <a id="14598" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="14602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14526" class="Function">≤-total′</a> <a id="14611" class="Symbol">(</a><a id="14612" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14616" href="plfa.Relations.html#14616" class="Bound">m</a><a id="14617" class="Symbol">)</a> <a id="14619" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="14628" class="Symbol">=</a>  <a id="14631" href="plfa.Relations.html#11487" class="InductiveConstructor">flipped</a> <a id="14639" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="14643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14526" class="Function">≤-total′</a> <a id="14652" class="Symbol">(</a><a id="14653" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14657" href="plfa.Relations.html#14657" class="Bound">m</a><a id="14658" class="Symbol">)</a> <a id="14660" class="Symbol">(</a><a id="14661" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14665" href="plfa.Relations.html#14665" class="Bound">n</a><a id="14666" class="Symbol">)</a>  <a id="14669" class="Symbol">=</a>  <a id="14672" href="plfa.Relations.html#14704" class="Function">helper</a> <a id="14679" class="Symbol">(</a><a id="14680" href="plfa.Relations.html#14526" class="Function">≤-total′</a> <a id="14689" href="plfa.Relations.html#14657" class="Bound">m</a> <a id="14691" href="plfa.Relations.html#14665" class="Bound">n</a><a id="14692" class="Symbol">)</a>
  <a id="14696" class="Keyword">where</a>
  <a id="14704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14704" class="Function">helper</a> <a id="14711" class="Symbol">:</a> <a id="14713" href="plfa.Relations.html#11399" class="Datatype">Total</a> <a id="14719" href="plfa.Relations.html#14657" class="Bound">m</a> <a id="14721" href="plfa.Relations.html#14665" class="Bound">n</a> <a id="14723" class="Symbol">→</a> <a id="14725" href="plfa.Relations.html#11399" class="Datatype">Total</a> <a id="14731" class="Symbol">(</a><a id="14732" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14736" href="plfa.Relations.html#14657" class="Bound">m</a><a id="14737" class="Symbol">)</a> <a id="14739" class="Symbol">(</a><a id="14740" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14744" href="plfa.Relations.html#14665" class="Bound">n</a><a id="14745" class="Symbol">)</a>
  <a id="14749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14704" class="Function">helper</a> <a id="14756" class="Symbol">(</a><a id="14757" href="plfa.Relations.html#11430" class="InductiveConstructor">forward</a> <a id="14765" href="plfa.Relations.html#14765" class="Bound">m≤n</a><a id="14768" class="Symbol">)</a>  <a id="14771" class="Symbol">=</a>  <a id="14774" href="plfa.Relations.html#11430" class="InductiveConstructor">forward</a> <a id="14782" class="Symbol">(</a><a id="14783" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="14787" href="plfa.Relations.html#14765" class="Bound">m≤n</a><a id="14790" class="Symbol">)</a>
  <a id="14794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14704" class="Function">helper</a> <a id="14801" class="Symbol">(</a><a id="14802" href="plfa.Relations.html#11487" class="InductiveConstructor">flipped</a> <a id="14810" href="plfa.Relations.html#14810" class="Bound">n≤m</a><a id="14813" class="Symbol">)</a>  <a id="14816" class="Symbol">=</a>  <a id="14819" href="plfa.Relations.html#11487" class="InductiveConstructor">flipped</a> <a id="14827" class="Symbol">(</a><a id="14828" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="14832" href="plfa.Relations.html#14810" class="Bound">n≤m</a><a id="14835" class="Symbol">)</a>
</pre>{% endraw %}This is also our first use of a `where` clause in https://agda.github.io/agda-stdlib/v1.1/Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
{% raw %}<pre class="Agda"><a id="≤-total″"></a><a id="15457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15457" class="Function">≤-total″</a> <a id="15466" class="Symbol">:</a> <a id="15468" class="Symbol">∀</a> <a id="15470" class="Symbol">(</a><a id="15471" href="plfa.Relations.html#15471" class="Bound">m</a> <a id="15473" href="plfa.Relations.html#15473" class="Bound">n</a> <a id="15475" class="Symbol">:</a> <a id="15477" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15478" class="Symbol">)</a> <a id="15480" class="Symbol">→</a> <a id="15482" href="plfa.Relations.html#11399" class="Datatype">Total</a> <a id="15488" href="plfa.Relations.html#15471" class="Bound">m</a> <a id="15490" href="plfa.Relations.html#15473" class="Bound">n</a>
<a id="15492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15457" class="Function">≤-total″</a> <a id="15501" href="plfa.Relations.html#15501" class="Bound">m</a>       <a id="15509" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="15535" class="Symbol">=</a>  <a id="15538" href="plfa.Relations.html#11487" class="InductiveConstructor">flipped</a> <a id="15546" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="15550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15457" class="Function">≤-total″</a> <a id="15559" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="15567" class="Symbol">(</a><a id="15568" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15572" href="plfa.Relations.html#15572" class="Bound">n</a><a id="15573" class="Symbol">)</a>                   <a id="15593" class="Symbol">=</a>  <a id="15596" href="plfa.Relations.html#11430" class="InductiveConstructor">forward</a> <a id="15604" href="plfa.Relations.html#1216" class="InductiveConstructor">z≤n</a>
<a id="15608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15457" class="Function">≤-total″</a> <a id="15617" class="Symbol">(</a><a id="15618" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15622" href="plfa.Relations.html#15622" class="Bound">m</a><a id="15623" class="Symbol">)</a> <a id="15625" class="Symbol">(</a><a id="15626" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15630" href="plfa.Relations.html#15630" class="Bound">n</a><a id="15631" class="Symbol">)</a> <a id="15633" class="Keyword">with</a> <a id="15638" href="plfa.Relations.html#15457" class="Function">≤-total″</a> <a id="15647" href="plfa.Relations.html#15622" class="Bound">m</a> <a id="15649" href="plfa.Relations.html#15630" class="Bound">n</a>
<a id="15651" class="Symbol">...</a>                        <a id="15678" class="Symbol">|</a> <a id="15680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11430" class="InductiveConstructor">forward</a> <a id="15688" href="plfa.Relations.html#15688" class="Bound">m≤n</a>   <a id="15694" class="Symbol">=</a>  <a id="15697" href="plfa.Relations.html#11430" class="InductiveConstructor">forward</a> <a id="15705" class="Symbol">(</a><a id="15706" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="15710" href="plfa.Relations.html#15688" class="Bound">m≤n</a><a id="15713" class="Symbol">)</a>
<a id="15715" class="Symbol">...</a>                        <a id="15742" class="Symbol">|</a> <a id="15744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11487" class="InductiveConstructor">flipped</a> <a id="15752" href="plfa.Relations.html#15752" class="Bound">n≤m</a>   <a id="15758" class="Symbol">=</a>  <a id="15761" href="plfa.Relations.html#11487" class="InductiveConstructor">flipped</a> <a id="15769" class="Symbol">(</a><a id="15770" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="15774" href="plfa.Relations.html#15752" class="Bound">n≤m</a><a id="15777" class="Symbol">)</a>
</pre>{% endraw %}It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
{% raw %}<pre class="Agda"><a id="+-monoʳ-≤"></a><a id="16366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16366" class="Function">+-monoʳ-≤</a> <a id="16376" class="Symbol">:</a> <a id="16378" class="Symbol">∀</a> <a id="16380" class="Symbol">(</a><a id="16381" href="plfa.Relations.html#16381" class="Bound">n</a> <a id="16383" href="plfa.Relations.html#16383" class="Bound">p</a> <a id="16385" href="plfa.Relations.html#16385" class="Bound">q</a> <a id="16387" class="Symbol">:</a> <a id="16389" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16390" class="Symbol">)</a>
  <a id="16394" class="Symbol">→</a> <a id="16396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16383" class="Bound">p</a> <a id="16398" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="16400" href="plfa.Relations.html#16385" class="Bound">q</a>
    <a id="16406" class="Comment">-------------</a>
  <a id="16422" class="Symbol">→</a> <a id="16424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16381" class="Bound">n</a> <a id="16426" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16428" href="plfa.Relations.html#16383" class="Bound">p</a> <a id="16430" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="16432" href="plfa.Relations.html#16381" class="Bound">n</a> <a id="16434" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16436" href="plfa.Relations.html#16385" class="Bound">q</a>
<a id="16438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16366" class="Function">+-monoʳ-≤</a> <a id="16448" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="16456" href="plfa.Relations.html#16456" class="Bound">p</a> <a id="16458" href="plfa.Relations.html#16458" class="Bound">q</a> <a id="16460" href="plfa.Relations.html#16460" class="Bound">p≤q</a>  <a id="16465" class="Symbol">=</a>  <a id="16468" href="plfa.Relations.html#16460" class="Bound">p≤q</a>
<a id="16472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16366" class="Function">+-monoʳ-≤</a> <a id="16482" class="Symbol">(</a><a id="16483" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16487" href="plfa.Relations.html#16487" class="Bound">n</a><a id="16488" class="Symbol">)</a> <a id="16490" href="plfa.Relations.html#16490" class="Bound">p</a> <a id="16492" href="plfa.Relations.html#16492" class="Bound">q</a> <a id="16494" href="plfa.Relations.html#16494" class="Bound">p≤q</a>  <a id="16499" class="Symbol">=</a>  <a id="16502" href="plfa.Relations.html#1265" class="InductiveConstructor">s≤s</a> <a id="16506" class="Symbol">(</a><a id="16507" href="plfa.Relations.html#16366" class="Function">+-monoʳ-≤</a> <a id="16517" href="plfa.Relations.html#16487" class="Bound">n</a> <a id="16519" href="plfa.Relations.html#16490" class="Bound">p</a> <a id="16521" href="plfa.Relations.html#16492" class="Bound">q</a> <a id="16523" href="plfa.Relations.html#16494" class="Bound">p≤q</a><a id="16526" class="Symbol">)</a>
</pre>{% endraw %}The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
{% raw %}<pre class="Agda"><a id="+-monoˡ-≤"></a><a id="17166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17166" class="Function">+-monoˡ-≤</a> <a id="17176" class="Symbol">:</a> <a id="17178" class="Symbol">∀</a> <a id="17180" class="Symbol">(</a><a id="17181" href="plfa.Relations.html#17181" class="Bound">m</a> <a id="17183" href="plfa.Relations.html#17183" class="Bound">n</a> <a id="17185" href="plfa.Relations.html#17185" class="Bound">p</a> <a id="17187" class="Symbol">:</a> <a id="17189" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17190" class="Symbol">)</a>
  <a id="17194" class="Symbol">→</a> <a id="17196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17181" class="Bound">m</a> <a id="17198" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="17200" href="plfa.Relations.html#17183" class="Bound">n</a>
    <a id="17206" class="Comment">-------------</a>
  <a id="17222" class="Symbol">→</a> <a id="17224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17181" class="Bound">m</a> <a id="17226" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17228" href="plfa.Relations.html#17185" class="Bound">p</a> <a id="17230" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="17232" href="plfa.Relations.html#17183" class="Bound">n</a> <a id="17234" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17236" href="plfa.Relations.html#17185" class="Bound">p</a>
<a id="17238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17166" class="Function">+-monoˡ-≤</a> <a id="17248" href="plfa.Relations.html#17248" class="Bound">m</a> <a id="17250" href="plfa.Relations.html#17250" class="Bound">n</a> <a id="17252" href="plfa.Relations.html#17252" class="Bound">p</a> <a id="17254" href="plfa.Relations.html#17254" class="Bound">m≤n</a>  <a id="17259" class="Keyword">rewrite</a> <a id="17267" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="17274" href="plfa.Relations.html#17248" class="Bound">m</a> <a id="17276" href="plfa.Relations.html#17252" class="Bound">p</a> <a id="17278" class="Symbol">|</a> <a id="17280" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="17287" href="plfa.Relations.html#17250" class="Bound">n</a> <a id="17289" href="plfa.Relations.html#17252" class="Bound">p</a>  <a id="17292" class="Symbol">=</a> <a id="17294" href="plfa.Relations.html#16366" class="Function">+-monoʳ-≤</a> <a id="17304" href="plfa.Relations.html#17252" class="Bound">p</a> <a id="17306" href="plfa.Relations.html#17248" class="Bound">m</a> <a id="17308" href="plfa.Relations.html#17250" class="Bound">n</a> <a id="17310" href="plfa.Relations.html#17254" class="Bound">m≤n</a>
</pre>{% endraw %}Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
{% raw %}<pre class="Agda"><a id="+-mono-≤"></a><a id="17508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17508" class="Function">+-mono-≤</a> <a id="17517" class="Symbol">:</a> <a id="17519" class="Symbol">∀</a> <a id="17521" class="Symbol">(</a><a id="17522" href="plfa.Relations.html#17522" class="Bound">m</a> <a id="17524" href="plfa.Relations.html#17524" class="Bound">n</a> <a id="17526" href="plfa.Relations.html#17526" class="Bound">p</a> <a id="17528" href="plfa.Relations.html#17528" class="Bound">q</a> <a id="17530" class="Symbol">:</a> <a id="17532" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17533" class="Symbol">)</a>
  <a id="17537" class="Symbol">→</a> <a id="17539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17522" class="Bound">m</a> <a id="17541" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="17543" href="plfa.Relations.html#17524" class="Bound">n</a>
  <a id="17547" class="Symbol">→</a> <a id="17549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17526" class="Bound">p</a> <a id="17551" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="17553" href="plfa.Relations.html#17528" class="Bound">q</a>
    <a id="17559" class="Comment">-------------</a>
  <a id="17575" class="Symbol">→</a> <a id="17577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17522" class="Bound">m</a> <a id="17579" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17581" href="plfa.Relations.html#17526" class="Bound">p</a> <a id="17583" href="plfa.Relations.html#1189" class="Datatype Operator">≤</a> <a id="17585" href="plfa.Relations.html#17524" class="Bound">n</a> <a id="17587" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17589" href="plfa.Relations.html#17528" class="Bound">q</a>
<a id="17591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17508" class="Function">+-mono-≤</a> <a id="17600" href="plfa.Relations.html#17600" class="Bound">m</a> <a id="17602" href="plfa.Relations.html#17602" class="Bound">n</a> <a id="17604" href="plfa.Relations.html#17604" class="Bound">p</a> <a id="17606" href="plfa.Relations.html#17606" class="Bound">q</a> <a id="17608" href="plfa.Relations.html#17608" class="Bound">m≤n</a> <a id="17612" href="plfa.Relations.html#17612" class="Bound">p≤q</a>  <a id="17617" class="Symbol">=</a>  <a id="17620" href="plfa.Relations.html#8113" class="Function">≤-trans</a> <a id="17628" class="Symbol">(</a><a id="17629" href="plfa.Relations.html#17166" class="Function">+-monoˡ-≤</a> <a id="17639" href="plfa.Relations.html#17600" class="Bound">m</a> <a id="17641" href="plfa.Relations.html#17602" class="Bound">n</a> <a id="17643" href="plfa.Relations.html#17604" class="Bound">p</a> <a id="17645" href="plfa.Relations.html#17608" class="Bound">m≤n</a><a id="17648" class="Symbol">)</a> <a id="17650" class="Symbol">(</a><a id="17651" href="plfa.Relations.html#16366" class="Function">+-monoʳ-≤</a> <a id="17661" href="plfa.Relations.html#17602" class="Bound">n</a> <a id="17663" href="plfa.Relations.html#17604" class="Bound">p</a> <a id="17665" href="plfa.Relations.html#17606" class="Bound">q</a> <a id="17667" href="plfa.Relations.html#17612" class="Bound">p≤q</a><a id="17670" class="Symbol">)</a>
</pre>{% endraw %}Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

{% raw %}<pre class="Agda"><a id="17979" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
{% raw %}<pre class="Agda"><a id="18112" class="Keyword">infix</a> <a id="18118" class="Number">4</a> <a id="18120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18130" class="Datatype Operator">_&lt;_</a>

<a id="18125" class="Keyword">data</a> <a id="_&lt;_"></a><a id="18130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18130" class="Datatype Operator">_&lt;_</a> <a id="18134" class="Symbol">:</a> <a id="18136" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18138" class="Symbol">→</a> <a id="18140" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18142" class="Symbol">→</a> <a id="18144" class="PrimitiveType">Set</a> <a id="18148" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="18157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18157" class="InductiveConstructor">z&lt;s</a> <a id="18161" class="Symbol">:</a> <a id="18163" class="Symbol">∀</a> <a id="18165" class="Symbol">{</a><a id="18166" href="plfa.Relations.html#18166" class="Bound">n</a> <a id="18168" class="Symbol">:</a> <a id="18170" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18171" class="Symbol">}</a>
      <a id="18179" class="Comment">------------</a>
    <a id="18196" class="Symbol">→</a> <a id="18198" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18130" class="Datatype Operator">&lt;</a> <a id="18205" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18209" href="plfa.Relations.html#18166" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="18214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18214" class="InductiveConstructor">s&lt;s</a> <a id="18218" class="Symbol">:</a> <a id="18220" class="Symbol">∀</a> <a id="18222" class="Symbol">{</a><a id="18223" href="plfa.Relations.html#18223" class="Bound">m</a> <a id="18225" href="plfa.Relations.html#18225" class="Bound">n</a> <a id="18227" class="Symbol">:</a> <a id="18229" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18230" class="Symbol">}</a>
    <a id="18236" class="Symbol">→</a> <a id="18238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18223" class="Bound">m</a> <a id="18240" href="plfa.Relations.html#18130" class="Datatype Operator">&lt;</a> <a id="18242" href="plfa.Relations.html#18225" class="Bound">n</a>
      <a id="18250" class="Comment">-------------</a>
    <a id="18268" class="Symbol">→</a> <a id="18270" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18223" class="Bound">m</a> <a id="18276" href="plfa.Relations.html#18130" class="Datatype Operator">&lt;</a> <a id="18278" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18282" href="plfa.Relations.html#18225" class="Bound">n</a>
</pre>{% endraw %}The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}/Negation/).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

{% raw %}<pre class="Agda"><a id="19451" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}/Negation/).)

{% raw %}<pre class="Agda"><a id="19939" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

{% raw %}<pre class="Agda"><a id="20148" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

{% raw %}<pre class="Agda"><a id="20291" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

{% raw %}<pre class="Agda"><a id="20551" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
{% raw %}<pre class="Agda"><a id="20790" class="Keyword">data</a> <a id="even"></a><a id="20795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20795" class="Datatype">even</a> <a id="20800" class="Symbol">:</a> <a id="20802" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="20804" class="Symbol">→</a> <a id="20806" class="PrimitiveType">Set</a>
<a id="20810" class="Keyword">data</a> <a id="odd"></a><a id="20815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20815" class="Datatype">odd</a>  <a id="20820" class="Symbol">:</a> <a id="20822" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="20824" class="Symbol">→</a> <a id="20826" class="PrimitiveType">Set</a>

<a id="20831" class="Keyword">data</a> <a id="20836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20795" class="Datatype">even</a> <a id="20841" class="Keyword">where</a>

  <a id="even.zero"></a><a id="20850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20850" class="InductiveConstructor">zero</a> <a id="20855" class="Symbol">:</a>
      <a id="20863" class="Comment">---------</a>
      <a id="20879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20795" class="Datatype">even</a> <a id="20884" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="20892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20892" class="InductiveConstructor">suc</a>  <a id="20897" class="Symbol">:</a> <a id="20899" class="Symbol">∀</a> <a id="20901" class="Symbol">{</a><a id="20902" href="plfa.Relations.html#20902" class="Bound">n</a> <a id="20904" class="Symbol">:</a> <a id="20906" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="20907" class="Symbol">}</a>
    <a id="20913" class="Symbol">→</a> <a id="20915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20815" class="Datatype">odd</a> <a id="20919" href="plfa.Relations.html#20902" class="Bound">n</a>
      <a id="20927" class="Comment">------------</a>
    <a id="20944" class="Symbol">→</a> <a id="20946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20795" class="Datatype">even</a> <a id="20951" class="Symbol">(</a><a id="20952" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="20956" href="plfa.Relations.html#20902" class="Bound">n</a><a id="20957" class="Symbol">)</a>

<a id="20960" class="Keyword">data</a> <a id="20965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20815" class="Datatype">odd</a> <a id="20969" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="20978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20978" class="InductiveConstructor">suc</a>   <a id="20984" class="Symbol">:</a> <a id="20986" class="Symbol">∀</a> <a id="20988" class="Symbol">{</a><a id="20989" href="plfa.Relations.html#20989" class="Bound">n</a> <a id="20991" class="Symbol">:</a> <a id="20993" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="20994" class="Symbol">}</a>
    <a id="21000" class="Symbol">→</a> <a id="21002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20795" class="Datatype">even</a> <a id="21007" href="plfa.Relations.html#20989" class="Bound">n</a>
      <a id="21015" class="Comment">-----------</a>
    <a id="21031" class="Symbol">→</a> <a id="21033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20815" class="Datatype">odd</a> <a id="21037" class="Symbol">(</a><a id="21038" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21042" href="plfa.Relations.html#20989" class="Bound">n</a><a id="21043" class="Symbol">)</a>
</pre>{% endraw %}A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even:
{% raw %}<pre class="Agda"><a id="e+e≡e"></a><a id="22203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22203" class="Function">e+e≡e</a> <a id="22209" class="Symbol">:</a> <a id="22211" class="Symbol">∀</a> <a id="22213" class="Symbol">{</a><a id="22214" href="plfa.Relations.html#22214" class="Bound">m</a> <a id="22216" href="plfa.Relations.html#22216" class="Bound">n</a> <a id="22218" class="Symbol">:</a> <a id="22220" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22221" class="Symbol">}</a>
  <a id="22225" class="Symbol">→</a> <a id="22227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20795" class="Datatype">even</a> <a id="22232" href="plfa.Relations.html#22214" class="Bound">m</a>
  <a id="22236" class="Symbol">→</a> <a id="22238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20795" class="Datatype">even</a> <a id="22243" href="plfa.Relations.html#22216" class="Bound">n</a>
    <a id="22249" class="Comment">------------</a>
  <a id="22264" class="Symbol">→</a> <a id="22266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20795" class="Datatype">even</a> <a id="22271" class="Symbol">(</a><a id="22272" href="plfa.Relations.html#22214" class="Bound">m</a> <a id="22274" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22276" href="plfa.Relations.html#22216" class="Bound">n</a><a id="22277" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="22280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22280" class="Function">o+e≡o</a> <a id="22286" class="Symbol">:</a> <a id="22288" class="Symbol">∀</a> <a id="22290" class="Symbol">{</a><a id="22291" href="plfa.Relations.html#22291" class="Bound">m</a> <a id="22293" href="plfa.Relations.html#22293" class="Bound">n</a> <a id="22295" class="Symbol">:</a> <a id="22297" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22298" class="Symbol">}</a>
  <a id="22302" class="Symbol">→</a> <a id="22304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20815" class="Datatype">odd</a> <a id="22308" href="plfa.Relations.html#22291" class="Bound">m</a>
  <a id="22312" class="Symbol">→</a> <a id="22314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20795" class="Datatype">even</a> <a id="22319" href="plfa.Relations.html#22293" class="Bound">n</a>
    <a id="22325" class="Comment">-----------</a>
  <a id="22339" class="Symbol">→</a> <a id="22341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20815" class="Datatype">odd</a> <a id="22345" class="Symbol">(</a><a id="22346" href="plfa.Relations.html#22291" class="Bound">m</a> <a id="22348" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22350" href="plfa.Relations.html#22293" class="Bound">n</a><a id="22351" class="Symbol">)</a>

<a id="22354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22203" class="Function">e+e≡e</a> <a id="22360" href="plfa.Relations.html#20850" class="InductiveConstructor">zero</a>     <a id="22369" href="plfa.Relations.html#22369" class="Bound">en</a>  <a id="22373" class="Symbol">=</a>  <a id="22376" href="plfa.Relations.html#22369" class="Bound">en</a>
<a id="22379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22203" class="Function">e+e≡e</a> <a id="22385" class="Symbol">(</a><a id="22386" href="plfa.Relations.html#20892" class="InductiveConstructor">suc</a> <a id="22390" href="plfa.Relations.html#22390" class="Bound">om</a><a id="22392" class="Symbol">)</a> <a id="22394" href="plfa.Relations.html#22394" class="Bound">en</a>  <a id="22398" class="Symbol">=</a>  <a id="22401" href="plfa.Relations.html#20892" class="InductiveConstructor">suc</a> <a id="22405" class="Symbol">(</a><a id="22406" href="plfa.Relations.html#22280" class="Function">o+e≡o</a> <a id="22412" href="plfa.Relations.html#22390" class="Bound">om</a> <a id="22415" href="plfa.Relations.html#22394" class="Bound">en</a><a id="22417" class="Symbol">)</a>

<a id="22420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22280" class="Function">o+e≡o</a> <a id="22426" class="Symbol">(</a><a id="22427" href="plfa.Relations.html#20978" class="InductiveConstructor">suc</a> <a id="22431" href="plfa.Relations.html#22431" class="Bound">em</a><a id="22433" class="Symbol">)</a> <a id="22435" href="plfa.Relations.html#22435" class="Bound">en</a>  <a id="22439" class="Symbol">=</a>  <a id="22442" href="plfa.Relations.html#20978" class="InductiveConstructor">suc</a> <a id="22446" class="Symbol">(</a><a id="22447" href="plfa.Relations.html#22203" class="Function">e+e≡e</a> <a id="22453" href="plfa.Relations.html#22431" class="Bound">em</a> <a id="22456" href="plfa.Relations.html#22435" class="Bound">en</a><a id="22458" class="Symbol">)</a>
</pre>{% endraw %}Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

{% raw %}<pre class="Agda"><a id="23596" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)

{% raw %}<pre class="Agda"><a id="24888" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="25024" class="Keyword">import</a> <a id="25031" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="25040" class="Keyword">using</a> <a id="25046" class="Symbol">(</a><a id="25047" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="25050" class="Symbol">;</a> <a id="25052" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="25055" class="Symbol">;</a> <a id="25057" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="25060" class="Symbol">)</a>
<a id="25062" class="Keyword">import</a> <a id="25069" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="25089" class="Keyword">using</a> <a id="25095" class="Symbol">(</a><a id="25096" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="25102" class="Symbol">;</a> <a id="25104" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="25111" class="Symbol">;</a> <a id="25113" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="25122" class="Symbol">;</a> <a id="25124" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="25131" class="Symbol">;</a>
                                  <a id="25167" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="25176" class="Symbol">;</a> <a id="25178" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="25187" class="Symbol">;</a> <a id="25189" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="25197" class="Symbol">)</a>
</pre>{% endraw %}In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}/Connectives/)),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
