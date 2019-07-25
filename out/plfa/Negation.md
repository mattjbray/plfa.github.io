---
src       : "src/plfa/Negation.lagda.md"
title     : "Negation: Negation, with intuitionistic and classical logic"
layout    : page
prev      : /Connectives/
permalink : /Negation/
next      : /Quantifiers/
---

{% raw %}<pre class="Agda"><a id="180" class="Keyword">module</a> <a id="187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}" class="Module">plfa.Negation</a> <a id="201" class="Keyword">where</a>
</pre>{% endraw %}
This chapter introduces negation, and discusses intuitionistic
and classical logic.

## Imports

{% raw %}<pre class="Agda"><a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="363" class="Keyword">using</a> <a id="369" class="Symbol">(</a><a id="370" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="373" class="Symbol">;</a> <a id="375" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="379" class="Symbol">)</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="402" class="Keyword">using</a> <a id="408" class="Symbol">(</a><a id="409" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="410" class="Symbol">;</a> <a id="412" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="416" class="Symbol">;</a> <a id="418" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="421" class="Symbol">)</a>
<a id="423" class="Keyword">open</a> <a id="428" class="Keyword">import</a> <a id="435" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="446" class="Keyword">using</a> <a id="452" class="Symbol">(</a><a id="453" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="454" class="Symbol">;</a> <a id="456" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="462" class="Symbol">)</a>
<a id="464" class="Keyword">open</a> <a id="469" class="Keyword">import</a> <a id="476" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="485" class="Keyword">using</a> <a id="491" class="Symbol">(</a><a id="492" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="495" class="Symbol">;</a> <a id="497" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="501" class="Symbol">;</a> <a id="503" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="507" class="Symbol">)</a>
<a id="509" class="Keyword">open</a> <a id="514" class="Keyword">import</a> <a id="521" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="534" class="Keyword">using</a> <a id="540" class="Symbol">(</a><a id="541" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="544" class="Symbol">)</a>
<a id="546" class="Keyword">open</a> <a id="551" class="Keyword">import</a> <a id="558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="575" class="Keyword">using</a> <a id="581" class="Symbol">(</a><a id="582" href="plfa.Isomorphism.html#3985" class="Record Operator">_≃_</a><a id="585" class="Symbol">;</a> <a id="587" href="plfa.Isomorphism.html#2678" class="Postulate">extensionality</a><a id="601" class="Symbol">)</a>
</pre>{% endraw %}

## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false:
{% raw %}<pre class="Agda"><a id="¬_"></a><a id="781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#781" class="Function Operator">¬_</a> <a id="784" class="Symbol">:</a> <a id="786" class="PrimitiveType">Set</a> <a id="790" class="Symbol">→</a> <a id="792" class="PrimitiveType">Set</a>
<a id="796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#781" class="Function Operator">¬</a> <a id="798" href="plfa.Negation.html#798" class="Bound">A</a> <a id="800" class="Symbol">=</a> <a id="802" href="plfa.Negation.html#798" class="Bound">A</a> <a id="804" class="Symbol">→</a> <a id="806" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}This is a form of _proof by contradiction_: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ{ x → N }

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction:
{% raw %}<pre class="Agda"><a id="¬-elim"></a><a id="1362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1362" class="Function">¬-elim</a> <a id="1369" class="Symbol">:</a> <a id="1371" class="Symbol">∀</a> <a id="1373" class="Symbol">{</a><a id="1374" href="plfa.Negation.html#1374" class="Bound">A</a> <a id="1376" class="Symbol">:</a> <a id="1378" class="PrimitiveType">Set</a><a id="1381" class="Symbol">}</a>
  <a id="1385" class="Symbol">→</a> <a id="1387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#781" class="Function Operator">¬</a> <a id="1389" href="plfa.Negation.html#1374" class="Bound">A</a>
  <a id="1393" class="Symbol">→</a> <a id="1395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1374" class="Bound">A</a>
    <a id="1401" class="Comment">---</a>
  <a id="1407" class="Symbol">→</a> <a id="1409" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
<a id="1411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1362" class="Function">¬-elim</a> <a id="1418" href="plfa.Negation.html#1418" class="Bound">¬x</a> <a id="1421" href="plfa.Negation.html#1421" class="Bound">x</a> <a id="1423" class="Symbol">=</a> <a id="1425" href="plfa.Negation.html#1418" class="Bound">¬x</a> <a id="1428" href="plfa.Negation.html#1421" class="Bound">x</a>
</pre>{% endraw %}Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else:
{% raw %}<pre class="Agda"><a id="1813" class="Keyword">infix</a> <a id="1819" class="Number">3</a> <a id="1821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#781" class="Function Operator">¬_</a>
</pre>{% endraw %}Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.

In _classical_ logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use _intuitionistic_ logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`:
{% raw %}<pre class="Agda"><a id="¬¬-intro"></a><a id="2110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2110" class="Function">¬¬-intro</a> <a id="2119" class="Symbol">:</a> <a id="2121" class="Symbol">∀</a> <a id="2123" class="Symbol">{</a><a id="2124" href="plfa.Negation.html#2124" class="Bound">A</a> <a id="2126" class="Symbol">:</a> <a id="2128" class="PrimitiveType">Set</a><a id="2131" class="Symbol">}</a>
  <a id="2135" class="Symbol">→</a> <a id="2137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2124" class="Bound">A</a>
    <a id="2143" class="Comment">-----</a>
  <a id="2151" class="Symbol">→</a> <a id="2153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#781" class="Function Operator">¬</a> <a id="2155" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="2157" href="plfa.Negation.html#2124" class="Bound">A</a>
<a id="2159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2110" class="Function">¬¬-intro</a> <a id="2168" href="plfa.Negation.html#2168" class="Bound">x</a>  <a id="2171" class="Symbol">=</a>  <a id="2174" class="Symbol">λ{</a><a id="2176" href="plfa.Negation.html#2176" class="Bound">¬x</a> <a id="2179" class="Symbol">→</a> <a id="2181" href="plfa.Negation.html#2176" class="Bound">¬x</a> <a id="2184" href="plfa.Negation.html#2168" class="Bound">x</a><a id="2185" class="Symbol">}</a>
</pre>{% endraw %}Let `x` be evidence of `A`. We show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.

An equivalent way to write the above is as follows:
{% raw %}<pre class="Agda"><a id="¬¬-intro′"></a><a id="2492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2492" class="Function">¬¬-intro′</a> <a id="2502" class="Symbol">:</a> <a id="2504" class="Symbol">∀</a> <a id="2506" class="Symbol">{</a><a id="2507" href="plfa.Negation.html#2507" class="Bound">A</a> <a id="2509" class="Symbol">:</a> <a id="2511" class="PrimitiveType">Set</a><a id="2514" class="Symbol">}</a>
  <a id="2518" class="Symbol">→</a> <a id="2520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2507" class="Bound">A</a>
    <a id="2526" class="Comment">-----</a>
  <a id="2534" class="Symbol">→</a> <a id="2536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#781" class="Function Operator">¬</a> <a id="2538" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="2540" href="plfa.Negation.html#2507" class="Bound">A</a>
<a id="2542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2492" class="Function">¬¬-intro′</a> <a id="2552" href="plfa.Negation.html#2552" class="Bound">x</a> <a id="2554" href="plfa.Negation.html#2554" class="Bound">¬x</a> <a id="2557" class="Symbol">=</a> <a id="2559" href="plfa.Negation.html#2554" class="Bound">¬x</a> <a id="2562" href="plfa.Negation.html#2552" class="Bound">x</a>
</pre>{% endraw %}Here we have simply converted the argument of the lambda term
to an additional argument of the function.  We will usually
use this latter style, as it is more compact.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`:
{% raw %}<pre class="Agda"><a id="¬¬¬-elim"></a><a id="2828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2828" class="Function">¬¬¬-elim</a> <a id="2837" class="Symbol">:</a> <a id="2839" class="Symbol">∀</a> <a id="2841" class="Symbol">{</a><a id="2842" href="plfa.Negation.html#2842" class="Bound">A</a> <a id="2844" class="Symbol">:</a> <a id="2846" class="PrimitiveType">Set</a><a id="2849" class="Symbol">}</a>
  <a id="2853" class="Symbol">→</a> <a id="2855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#781" class="Function Operator">¬</a> <a id="2857" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="2859" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="2861" href="plfa.Negation.html#2842" class="Bound">A</a>
    <a id="2867" class="Comment">-------</a>
  <a id="2877" class="Symbol">→</a> <a id="2879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#781" class="Function Operator">¬</a> <a id="2881" href="plfa.Negation.html#2842" class="Bound">A</a>
<a id="2883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2828" class="Function">¬¬¬-elim</a> <a id="2892" href="plfa.Negation.html#2892" class="Bound">¬¬¬x</a>  <a id="2898" class="Symbol">=</a>  <a id="2901" class="Symbol">λ</a> <a id="2903" href="plfa.Negation.html#2903" class="Bound">x</a> <a id="2905" class="Symbol">→</a> <a id="2907" href="plfa.Negation.html#2892" class="Bound">¬¬¬x</a> <a id="2912" class="Symbol">(</a><a id="2913" href="plfa.Negation.html#2110" class="Function">¬¬-intro</a> <a id="2922" href="plfa.Negation.html#2903" class="Bound">x</a><a id="2923" class="Symbol">)</a>
</pre>{% endraw %}Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.

Another law of logic is _contraposition_,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`:
{% raw %}<pre class="Agda"><a id="contraposition"></a><a id="3385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3385" class="Function">contraposition</a> <a id="3400" class="Symbol">:</a> <a id="3402" class="Symbol">∀</a> <a id="3404" class="Symbol">{</a><a id="3405" href="plfa.Negation.html#3405" class="Bound">A</a> <a id="3407" href="plfa.Negation.html#3407" class="Bound">B</a> <a id="3409" class="Symbol">:</a> <a id="3411" class="PrimitiveType">Set</a><a id="3414" class="Symbol">}</a>
  <a id="3418" class="Symbol">→</a> <a id="3420" class="Symbol">(</a><a id="3421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3405" class="Bound">A</a> <a id="3423" class="Symbol">→</a> <a id="3425" href="plfa.Negation.html#3407" class="Bound">B</a><a id="3426" class="Symbol">)</a>
    <a id="3432" class="Comment">-----------</a>
  <a id="3446" class="Symbol">→</a> <a id="3448" class="Symbol">(</a><a id="3449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#781" class="Function Operator">¬</a> <a id="3451" href="plfa.Negation.html#3407" class="Bound">B</a> <a id="3453" class="Symbol">→</a> <a id="3455" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="3457" href="plfa.Negation.html#3405" class="Bound">A</a><a id="3458" class="Symbol">)</a>
<a id="3460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3385" class="Function">contraposition</a> <a id="3475" href="plfa.Negation.html#3475" class="Bound">f</a> <a id="3477" href="plfa.Negation.html#3477" class="Bound">¬y</a> <a id="3480" href="plfa.Negation.html#3480" class="Bound">x</a> <a id="3482" class="Symbol">=</a> <a id="3484" href="plfa.Negation.html#3477" class="Bound">¬y</a> <a id="3487" class="Symbol">(</a><a id="3488" href="plfa.Negation.html#3475" class="Bound">f</a> <a id="3490" href="plfa.Negation.html#3480" class="Bound">x</a><a id="3491" class="Symbol">)</a>
</pre>{% endraw %}Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence `¬ A`
must hold. Let `x` be evidence of `A`.  Then from `A → B` and `A` we
may conclude `B`, evidenced by `f x`, and from `B` and `¬ B` we may
conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown `¬ A`.

Using negation, it is straightforward to define inequality:
{% raw %}<pre class="Agda"><a id="_≢_"></a><a id="3907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3907" class="Function Operator">_≢_</a> <a id="3911" class="Symbol">:</a> <a id="3913" class="Symbol">∀</a> <a id="3915" class="Symbol">{</a><a id="3916" href="plfa.Negation.html#3916" class="Bound">A</a> <a id="3918" class="Symbol">:</a> <a id="3920" class="PrimitiveType">Set</a><a id="3923" class="Symbol">}</a> <a id="3925" class="Symbol">→</a> <a id="3927" href="plfa.Negation.html#3916" class="Bound">A</a> <a id="3929" class="Symbol">→</a> <a id="3931" href="plfa.Negation.html#3916" class="Bound">A</a> <a id="3933" class="Symbol">→</a> <a id="3935" class="PrimitiveType">Set</a>
<a id="3939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3939" class="Bound">x</a> <a id="3941" href="plfa.Negation.html#3907" class="Function Operator">≢</a> <a id="3943" href="plfa.Negation.html#3943" class="Bound">y</a>  <a id="3946" class="Symbol">=</a>  <a id="3949" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="3951" class="Symbol">(</a><a id="3952" href="plfa.Negation.html#3939" class="Bound">x</a> <a id="3954" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3956" href="plfa.Negation.html#3943" class="Bound">y</a><a id="3957" class="Symbol">)</a>
</pre>{% endraw %}It is trivial to show distinct numbers are not equal:
{% raw %}<pre class="Agda"><a id="4021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4021" class="Function">_</a> <a id="4023" class="Symbol">:</a> <a id="4025" class="Number">1</a> <a id="4027" href="plfa.Negation.html#3907" class="Function Operator">≢</a> <a id="4029" class="Number">2</a>
<a id="4031" class="Symbol">_</a> <a id="4033" class="Symbol">=</a> <a id="4035" class="Symbol">λ()</a>
</pre>{% endraw %}This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number:
{% raw %}<pre class="Agda"><a id="peano"></a><a id="4428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4428" class="Function">peano</a> <a id="4434" class="Symbol">:</a> <a id="4436" class="Symbol">∀</a> <a id="4438" class="Symbol">{</a><a id="4439" href="plfa.Negation.html#4439" class="Bound">m</a> <a id="4441" class="Symbol">:</a> <a id="4443" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="4444" class="Symbol">}</a> <a id="4446" class="Symbol">→</a> <a id="4448" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="4453" href="plfa.Negation.html#3907" class="Function Operator">≢</a> <a id="4455" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4459" href="plfa.Negation.html#4439" class="Bound">m</a>
<a id="4461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4428" class="Function">peano</a> <a id="4467" class="Symbol">=</a> <a id="4469" class="Symbol">λ()</a>
</pre>{% endraw %}The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  ≡  1,  if n ≡ 0
           ≡  0,  if n ≢ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.  We can write
this proof two different ways:
{% raw %}<pre class="Agda"><a id="id"></a><a id="4955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4955" class="Function">id</a> <a id="4958" class="Symbol">:</a> <a id="4960" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a> <a id="4962" class="Symbol">→</a> <a id="4964" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
<a id="4966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4955" class="Function">id</a> <a id="4969" href="plfa.Negation.html#4969" class="Bound">x</a> <a id="4971" class="Symbol">=</a> <a id="4973" href="plfa.Negation.html#4969" class="Bound">x</a>

<a id="id′"></a><a id="4976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4976" class="Function">id′</a> <a id="4980" class="Symbol">:</a> <a id="4982" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a> <a id="4984" class="Symbol">→</a> <a id="4986" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
<a id="4988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4976" class="Function">id′</a> <a id="4992" class="Symbol">()</a>
</pre>{% endraw %}But, using extensionality, we can prove these equal:
{% raw %}<pre class="Agda"><a id="id≡id′"></a><a id="5056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5056" class="Function">id≡id′</a> <a id="5063" class="Symbol">:</a> <a id="5065" href="plfa.Negation.html#4955" class="Function">id</a> <a id="5068" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5070" href="plfa.Negation.html#4976" class="Function">id′</a>
<a id="5074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5056" class="Function">id≡id′</a> <a id="5081" class="Symbol">=</a> <a id="5083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2678" class="Postulate">extensionality</a> <a id="5098" class="Symbol">(λ())</a>
</pre>{% endraw %}By extensionality, `id ≡ id′` holds if for every
`x` in their domain we have `id x ≡ id′ x`. But there
is no `x` in their domain, so the equality holds trivially.

Indeed, we can show any two proofs of a negation are equal:
{% raw %}<pre class="Agda"><a id="assimilation"></a><a id="5336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5336" class="Function">assimilation</a> <a id="5349" class="Symbol">:</a> <a id="5351" class="Symbol">∀</a> <a id="5353" class="Symbol">{</a><a id="5354" href="plfa.Negation.html#5354" class="Bound">A</a> <a id="5356" class="Symbol">:</a> <a id="5358" class="PrimitiveType">Set</a><a id="5361" class="Symbol">}</a> <a id="5363" class="Symbol">(</a><a id="5364" href="plfa.Negation.html#5364" class="Bound">¬x</a> <a id="5367" href="plfa.Negation.html#5367" class="Bound">¬x′</a> <a id="5371" class="Symbol">:</a> <a id="5373" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="5375" href="plfa.Negation.html#5354" class="Bound">A</a><a id="5376" class="Symbol">)</a> <a id="5378" class="Symbol">→</a> <a id="5380" href="plfa.Negation.html#5364" class="Bound">¬x</a> <a id="5383" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5385" href="plfa.Negation.html#5367" class="Bound">¬x′</a>
<a id="5389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5336" class="Function">assimilation</a> <a id="5402" href="plfa.Negation.html#5402" class="Bound">¬x</a> <a id="5405" href="plfa.Negation.html#5405" class="Bound">¬x′</a> <a id="5409" class="Symbol">=</a> <a id="5411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2678" class="Postulate">extensionality</a> <a id="5426" class="Symbol">(λ</a> <a id="5429" href="plfa.Negation.html#5429" class="Bound">x</a> <a id="5431" class="Symbol">→</a> <a id="5433" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="5440" class="Symbol">(</a><a id="5441" href="plfa.Negation.html#5402" class="Bound">¬x</a> <a id="5444" href="plfa.Negation.html#5429" class="Bound">x</a><a id="5445" class="Symbol">))</a>
</pre>{% endraw %}Evidence for `¬ A` implies that any evidence of `A`
immediately leads to a contradiction.  But extensionality
quantifies over all `x` such that `A` holds, hence any
such `x` immediately leads to a contradiction,
again causing the equality to hold trivially.


#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality]({{ site.baseurl }}/Relations/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.

{% raw %}<pre class="Agda"><a id="5908" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `trichotomy`

Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}/Relations/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

{% raw %}<pre class="Agda"><a id="6307" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

{% raw %}<pre class="Agda"><a id="6579" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?


## Intuitive and Classical logic

In Gilbert and Sullivan's _The Gondoliers_, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails "Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?"  To which the response is "Without any doubt of any kind
whatever."

Logic comes in many varieties, and one distinction is between
_classical_ and _intuitionistic_. Intuitionists, concerned
by assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
_which_ of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.

Intuitionists also reject the law of the excluded middle, which
asserts `A ⊎ ¬ A` for every `A`, since the law gives no clue as to
_which_ of `A` or `¬ A` holds. Heyting formalised a variant of
Hilbert's classical logic that captures the intuitionistic notion of
provability. In particular, the law of the excluded middle is provable
in Hilbert's logic, but not in Heyting's.  Further, if the law of the
excluded middle is added as an axiom to Heyting's logic, then it
becomes equivalent to Hilbert's.  Kolmogorov showed the two logics
were closely related: he gave a double-negation translation, such that
a formula is provable in classical logic if and only if its
translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.

(Parts of the above are adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)

## Excluded middle is irrefutable

The law of the excluded middle can be formulated as follows:
{% raw %}<pre class="Agda"><a id="9115" class="Keyword">postulate</a>
  <a id="em"></a><a id="9127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9127" class="Postulate">em</a> <a id="9130" class="Symbol">:</a> <a id="9132" class="Symbol">∀</a> <a id="9134" class="Symbol">{</a><a id="9135" href="plfa.Negation.html#9135" class="Bound">A</a> <a id="9137" class="Symbol">:</a> <a id="9139" class="PrimitiveType">Set</a><a id="9142" class="Symbol">}</a> <a id="9144" class="Symbol">→</a> <a id="9146" href="plfa.Negation.html#9135" class="Bound">A</a> <a id="9148" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="9150" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="9152" href="plfa.Negation.html#9135" class="Bound">A</a>
</pre>{% endraw %}As we noted, the law of the excluded middle does not hold in
intuitionistic logic.  However, we can show that it is _irrefutable_,
meaning that the negation of its negation is provable (and hence that
its negation is never provable):
{% raw %}<pre class="Agda"><a id="em-irrefutable"></a><a id="9396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9396" class="Function">em-irrefutable</a> <a id="9411" class="Symbol">:</a> <a id="9413" class="Symbol">∀</a> <a id="9415" class="Symbol">{</a><a id="9416" href="plfa.Negation.html#9416" class="Bound">A</a> <a id="9418" class="Symbol">:</a> <a id="9420" class="PrimitiveType">Set</a><a id="9423" class="Symbol">}</a> <a id="9425" class="Symbol">→</a> <a id="9427" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="9429" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="9431" class="Symbol">(</a><a id="9432" href="plfa.Negation.html#9416" class="Bound">A</a> <a id="9434" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="9436" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="9438" href="plfa.Negation.html#9416" class="Bound">A</a><a id="9439" class="Symbol">)</a>
<a id="9441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9396" class="Function">em-irrefutable</a> <a id="9456" class="Symbol">=</a> <a id="9458" class="Symbol">λ</a> <a id="9460" href="plfa.Negation.html#9460" class="Bound">k</a> <a id="9462" class="Symbol">→</a> <a id="9464" href="plfa.Negation.html#9460" class="Bound">k</a> <a id="9466" class="Symbol">(</a><a id="9467" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="9472" class="Symbol">(λ</a> <a id="9475" href="plfa.Negation.html#9475" class="Bound">x</a> <a id="9477" class="Symbol">→</a> <a id="9479" href="plfa.Negation.html#9460" class="Bound">k</a> <a id="9481" class="Symbol">(</a><a id="9482" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="9487" href="plfa.Negation.html#9475" class="Bound">x</a><a id="9488" class="Symbol">)))</a>
</pre>{% endraw %}The best way to explain this code is to develop it interactively:

    em-irrefutable k = ?

Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that given a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly:

    em-irrefutable k = k ?

We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct:

    em-irrefutable k = k (inj₂ λ{ x → ? })

The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, the only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly:

    em-irrefutable k = k (inj₂ λ{ x → k ? })

This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct:

    em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

There are no holes left! This completes the proof.

The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)

Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."

The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.

The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?

"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."

The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.

"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"

The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."

And the devil handed back to the man the same valise that the man had
just handed to him.

(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, _International Conference on Functional Programming_, 2003.)


#### Exercise `Classical` (stretch)

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

{% raw %}<pre class="Agda"><a id="12877" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it:
{% raw %}<pre class="Agda"><a id="Stable"></a><a id="13020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13020" class="Function">Stable</a> <a id="13027" class="Symbol">:</a> <a id="13029" class="PrimitiveType">Set</a> <a id="13033" class="Symbol">→</a> <a id="13035" class="PrimitiveType">Set</a>
<a id="13039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13020" class="Function">Stable</a> <a id="13046" href="plfa.Negation.html#13046" class="Bound">A</a> <a id="13048" class="Symbol">=</a> <a id="13050" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="13052" href="plfa.Negation.html#781" class="Function Operator">¬</a> <a id="13054" href="plfa.Negation.html#13046" class="Bound">A</a> <a id="13056" class="Symbol">→</a> <a id="13058" href="plfa.Negation.html#13046" class="Bound">A</a>
</pre>{% endraw %}Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

{% raw %}<pre class="Agda"><a id="13169" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="13305" class="Keyword">import</a> <a id="13312" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="13329" class="Keyword">using</a> <a id="13335" class="Symbol">(</a><a id="13336" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="13338" class="Symbol">)</a>
<a id="13340" class="Keyword">import</a> <a id="13347" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="13373" class="Keyword">using</a> <a id="13379" class="Symbol">(</a><a id="13380" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#880" class="Function">contraposition</a><a id="13394" class="Symbol">)</a>
</pre>{% endraw %}
## Unicode

This chapter uses the following unicode:

    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
