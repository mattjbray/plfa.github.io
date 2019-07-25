---
src       : "src/plfa/Connectives.lagda.md"
title     : "Connectives: Conjunction, disjunction, and implication"
layout    : page
prev      : /Isomorphism/
permalink : /Connectives/
next      : /Negation/
---

{% raw %}<pre class="Agda"><a id="175" class="Keyword">module</a> <a id="182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}" class="Module">plfa.Connectives</a> <a id="199" class="Keyword">where</a>
</pre>{% endraw %}
<!-- The ⊥ ⊎ A ≅ A exercise requires a (inj₁ ()) pattern,
     which the reader will not have seen. Restore this
     exercise, and possibly also associativity? Take the
     exercises from the final sections on distributivity
     and exponentials? -->

This chapter introduces the basic logical connectives, by observing a
correspondence between connectives of logic and data types, a
principle known as _Propositions as Types_:

  * _conjunction_ is _product_,
  * _disjunction_ is _sum_,
  * _true_ is _unit type_,
  * _false_ is _empty type_,
  * _implication_ is _function space_.


## Imports

{% raw %}<pre class="Agda"><a id="815" class="Keyword">import</a> <a id="822" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="860" class="Symbol">as</a> <a id="863" class="Module">Eq</a>
<a id="866" class="Keyword">open</a> <a id="871" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="874" class="Keyword">using</a> <a id="880" class="Symbol">(</a><a id="881" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="884" class="Symbol">;</a> <a id="886" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="890" class="Symbol">)</a>
<a id="892" class="Keyword">open</a> <a id="897" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="912" class="Keyword">open</a> <a id="917" class="Keyword">import</a> <a id="924" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="933" class="Keyword">using</a> <a id="939" class="Symbol">(</a><a id="940" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="941" class="Symbol">)</a>
<a id="943" class="Keyword">open</a> <a id="948" class="Keyword">import</a> <a id="955" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="964" class="Keyword">using</a> <a id="970" class="Symbol">(</a><a id="971" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="974" class="Symbol">)</a>
<a id="976" class="Keyword">open</a> <a id="981" class="Keyword">import</a> <a id="988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="1005" class="Keyword">using</a> <a id="1011" class="Symbol">(</a><a id="1012" href="plfa.Isomorphism.html#3985" class="Record Operator">_≃_</a><a id="1015" class="Symbol">;</a> <a id="1017" href="plfa.Isomorphism.html#8806" class="Record Operator">_≲_</a><a id="1020" class="Symbol">;</a> <a id="1022" href="plfa.Isomorphism.html#2678" class="Postulate">extensionality</a><a id="1036" class="Symbol">)</a>
<a id="1038" class="Keyword">open</a> <a id="1043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8041" class="Module">plfa.Isomorphism.≃-Reasoning</a>
</pre>{% endraw %}

## Conjunction is product

Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{% raw %}<pre class="Agda"><a id="1272" class="Keyword">data</a> <a id="_×_"></a><a id="1277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1277" class="Datatype Operator">_×_</a> <a id="1281" class="Symbol">(</a><a id="1282" href="plfa.Connectives.html#1282" class="Bound">A</a> <a id="1284" href="plfa.Connectives.html#1284" class="Bound">B</a> <a id="1286" class="Symbol">:</a> <a id="1288" class="PrimitiveType">Set</a><a id="1291" class="Symbol">)</a> <a id="1293" class="Symbol">:</a> <a id="1295" class="PrimitiveType">Set</a> <a id="1299" class="Keyword">where</a>

  <a id="_×_.⟨_,_⟩"></a><a id="1308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="1314" class="Symbol">:</a>
      <a id="1322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1282" class="Bound">A</a>
    <a id="1328" class="Symbol">→</a> <a id="1330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1284" class="Bound">B</a>
      <a id="1338" class="Comment">-----</a>
    <a id="1348" class="Symbol">→</a> <a id="1350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1282" class="Bound">A</a> <a id="1352" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="1354" href="plfa.Connectives.html#1284" class="Bound">B</a>
</pre>{% endraw %}Evidence that `A × B` holds is of the form `⟨ M , N ⟩`, where `M`
provides evidence that `A` holds and `N` provides evidence that `B`
holds.

Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds:
{% raw %}<pre class="Agda"><a id="proj₁"></a><a id="1593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1593" class="Function">proj₁</a> <a id="1599" class="Symbol">:</a> <a id="1601" class="Symbol">∀</a> <a id="1603" class="Symbol">{</a><a id="1604" href="plfa.Connectives.html#1604" class="Bound">A</a> <a id="1606" href="plfa.Connectives.html#1606" class="Bound">B</a> <a id="1608" class="Symbol">:</a> <a id="1610" class="PrimitiveType">Set</a><a id="1613" class="Symbol">}</a>
  <a id="1617" class="Symbol">→</a> <a id="1619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1604" class="Bound">A</a> <a id="1621" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="1623" href="plfa.Connectives.html#1606" class="Bound">B</a>
    <a id="1629" class="Comment">-----</a>
  <a id="1637" class="Symbol">→</a> <a id="1639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1604" class="Bound">A</a>
<a id="1641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1593" class="Function">proj₁</a> <a id="1647" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="1649" href="plfa.Connectives.html#1649" class="Bound">x</a> <a id="1651" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="1653" href="plfa.Connectives.html#1653" class="Bound">y</a> <a id="1655" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="1657" class="Symbol">=</a> <a id="1659" href="plfa.Connectives.html#1649" class="Bound">x</a>

<a id="proj₂"></a><a id="1662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1662" class="Function">proj₂</a> <a id="1668" class="Symbol">:</a> <a id="1670" class="Symbol">∀</a> <a id="1672" class="Symbol">{</a><a id="1673" href="plfa.Connectives.html#1673" class="Bound">A</a> <a id="1675" href="plfa.Connectives.html#1675" class="Bound">B</a> <a id="1677" class="Symbol">:</a> <a id="1679" class="PrimitiveType">Set</a><a id="1682" class="Symbol">}</a>
  <a id="1686" class="Symbol">→</a> <a id="1688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1673" class="Bound">A</a> <a id="1690" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="1692" href="plfa.Connectives.html#1675" class="Bound">B</a>
    <a id="1698" class="Comment">-----</a>
  <a id="1706" class="Symbol">→</a> <a id="1708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1675" class="Bound">B</a>
<a id="1710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1662" class="Function">proj₂</a> <a id="1716" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="1718" href="plfa.Connectives.html#1718" class="Bound">x</a> <a id="1720" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="1722" href="plfa.Connectives.html#1722" class="Bound">y</a> <a id="1724" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="1726" class="Symbol">=</a> <a id="1728" href="plfa.Connectives.html#1722" class="Bound">y</a>
</pre>{% endraw %}If `L` provides evidence that `A × B` holds, then `proj₁ L` provides evidence
that `A` holds, and `proj₂ L` provides evidence that `B` holds.

Equivalently, we could also declare conjunction as a record type:
{% raw %}<pre class="Agda"><a id="1947" class="Keyword">record</a> <a id="_×′_"></a><a id="1954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1954" class="Record Operator">_×′_</a> <a id="1959" class="Symbol">(</a><a id="1960" href="plfa.Connectives.html#1960" class="Bound">A</a> <a id="1962" href="plfa.Connectives.html#1962" class="Bound">B</a> <a id="1964" class="Symbol">:</a> <a id="1966" class="PrimitiveType">Set</a><a id="1969" class="Symbol">)</a> <a id="1971" class="Symbol">:</a> <a id="1973" class="PrimitiveType">Set</a> <a id="1977" class="Keyword">where</a>
  <a id="1985" class="Keyword">field</a>
    <a id="_×′_.proj₁′"></a><a id="1995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1995" class="Field">proj₁′</a> <a id="2002" class="Symbol">:</a> <a id="2004" href="plfa.Connectives.html#1960" class="Bound">A</a>
    <a id="_×′_.proj₂′"></a><a id="2010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2010" class="Field">proj₂′</a> <a id="2017" class="Symbol">:</a> <a id="2019" href="plfa.Connectives.html#1962" class="Bound">B</a>
<a id="2021" class="Keyword">open</a> <a id="2026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1954" class="Module Operator">_×′_</a>
</pre>{% endraw %}Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B`.

When `⟨_,_⟩` appears in a term on the right-hand side of an equation
we refer to it as a _constructor_, and when it appears in a pattern on
the left-hand side of an equation we refer to it as a _destructor_.
We may also refer to `proj₁` and `proj₂` as destructors, since they
play a similar role.

Other terminology refers to `⟨_,_⟩` as _introducing_ a conjunction, and
to `proj₁` and `proj₂` as _eliminating_ a conjunction; indeed, the
former is sometimes given the name `×-I` and the latter two the names
`×-E₁` and `×-E₂`.  As we read the rules from top to bottom,
introduction and elimination do what they say on the tin: the first
_introduces_ a formula for the connective, which appears in the
conclusion but not in the hypotheses; the second _eliminates_ a
formula for the connective, which appears in a hypothesis but not in
the conclusion. An introduction rule describes under what conditions
we say the connective holds---how to _define_ the connective. An
elimination rule describes what we may conclude when the connective
holds---how to _use_ the connective.

(The paragraph above was adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)

In this case, applying each destructor and reassembling the results with the
constructor is the identity over products:
{% raw %}<pre class="Agda"><a id="η-×"></a><a id="3544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#3544" class="Function">η-×</a> <a id="3548" class="Symbol">:</a> <a id="3550" class="Symbol">∀</a> <a id="3552" class="Symbol">{</a><a id="3553" href="plfa.Connectives.html#3553" class="Bound">A</a> <a id="3555" href="plfa.Connectives.html#3555" class="Bound">B</a> <a id="3557" class="Symbol">:</a> <a id="3559" class="PrimitiveType">Set</a><a id="3562" class="Symbol">}</a> <a id="3564" class="Symbol">(</a><a id="3565" href="plfa.Connectives.html#3565" class="Bound">w</a> <a id="3567" class="Symbol">:</a> <a id="3569" href="plfa.Connectives.html#3553" class="Bound">A</a> <a id="3571" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="3573" href="plfa.Connectives.html#3555" class="Bound">B</a><a id="3574" class="Symbol">)</a> <a id="3576" class="Symbol">→</a> <a id="3578" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="3580" href="plfa.Connectives.html#1593" class="Function">proj₁</a> <a id="3586" href="plfa.Connectives.html#3565" class="Bound">w</a> <a id="3588" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="3590" href="plfa.Connectives.html#1662" class="Function">proj₂</a> <a id="3596" href="plfa.Connectives.html#3565" class="Bound">w</a> <a id="3598" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="3600" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3602" href="plfa.Connectives.html#3565" class="Bound">w</a>
<a id="3604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#3544" class="Function">η-×</a> <a id="3608" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="3610" href="plfa.Connectives.html#3610" class="Bound">x</a> <a id="3612" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="3614" href="plfa.Connectives.html#3614" class="Bound">y</a> <a id="3616" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="3618" class="Symbol">=</a> <a id="3620" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}The pattern matching on the left-hand side is essential, since
replacing `w` by `⟨ x , y ⟩` allows both sides of the
propositional equality to simplify to the same term.

We set the precedence of conjunction so that it binds less
tightly than anything save disjunction:
{% raw %}<pre class="Agda"><a id="3903" class="Keyword">infixr</a> <a id="3910" class="Number">2</a> <a id="3912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1277" class="Datatype Operator">_×_</a>
</pre>{% endraw %}Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)`.

Given two types `A` and `B`, we refer to `A × B` as the
_product_ of `A` and `B`.  In set theory, it is also sometimes
called the _Cartesian product_, and in computing it corresponds
to a _record_ type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members:
{% raw %}<pre class="Agda"><a id="4460" class="Keyword">data</a> <a id="Bool"></a><a id="4465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4465" class="Datatype">Bool</a> <a id="4470" class="Symbol">:</a> <a id="4472" class="PrimitiveType">Set</a> <a id="4476" class="Keyword">where</a>
  <a id="Bool.true"></a><a id="4484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4484" class="InductiveConstructor">true</a>  <a id="4490" class="Symbol">:</a> <a id="4492" href="plfa.Connectives.html#4465" class="Datatype">Bool</a>
  <a id="Bool.false"></a><a id="4499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4499" class="InductiveConstructor">false</a> <a id="4505" class="Symbol">:</a> <a id="4507" href="plfa.Connectives.html#4465" class="Datatype">Bool</a>

<a id="4513" class="Keyword">data</a> <a id="Tri"></a><a id="4518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4518" class="Datatype">Tri</a> <a id="4522" class="Symbol">:</a> <a id="4524" class="PrimitiveType">Set</a> <a id="4528" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="4536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4536" class="InductiveConstructor">aa</a> <a id="4539" class="Symbol">:</a> <a id="4541" href="plfa.Connectives.html#4518" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="4547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4547" class="InductiveConstructor">bb</a> <a id="4550" class="Symbol">:</a> <a id="4552" href="plfa.Connectives.html#4518" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="4558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4558" class="InductiveConstructor">cc</a> <a id="4561" class="Symbol">:</a> <a id="4563" href="plfa.Connectives.html#4518" class="Datatype">Tri</a>
</pre>{% endraw %}Then the type `Bool × Tri` has six members:

    ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
    ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
{% raw %}<pre class="Agda"><a id="×-count"></a><a id="4823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4823" class="Function">×-count</a> <a id="4831" class="Symbol">:</a> <a id="4833" href="plfa.Connectives.html#4465" class="Datatype">Bool</a> <a id="4838" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="4840" href="plfa.Connectives.html#4518" class="Datatype">Tri</a> <a id="4844" class="Symbol">→</a> <a id="4846" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="4848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4823" class="Function">×-count</a> <a id="4856" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="4858" href="plfa.Connectives.html#4484" class="InductiveConstructor">true</a>  <a id="4864" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="4866" href="plfa.Connectives.html#4536" class="InductiveConstructor">aa</a> <a id="4869" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a>  <a id="4872" class="Symbol">=</a>  <a id="4875" class="Number">1</a>
<a id="4877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4823" class="Function">×-count</a> <a id="4885" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="4887" href="plfa.Connectives.html#4484" class="InductiveConstructor">true</a>  <a id="4893" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="4895" href="plfa.Connectives.html#4547" class="InductiveConstructor">bb</a> <a id="4898" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a>  <a id="4901" class="Symbol">=</a>  <a id="4904" class="Number">2</a>
<a id="4906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4823" class="Function">×-count</a> <a id="4914" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="4916" href="plfa.Connectives.html#4484" class="InductiveConstructor">true</a>  <a id="4922" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="4924" href="plfa.Connectives.html#4558" class="InductiveConstructor">cc</a> <a id="4927" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a>  <a id="4930" class="Symbol">=</a>  <a id="4933" class="Number">3</a>
<a id="4935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4823" class="Function">×-count</a> <a id="4943" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="4945" href="plfa.Connectives.html#4499" class="InductiveConstructor">false</a> <a id="4951" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="4953" href="plfa.Connectives.html#4536" class="InductiveConstructor">aa</a> <a id="4956" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a>  <a id="4959" class="Symbol">=</a>  <a id="4962" class="Number">4</a>
<a id="4964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4823" class="Function">×-count</a> <a id="4972" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="4974" href="plfa.Connectives.html#4499" class="InductiveConstructor">false</a> <a id="4980" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="4982" href="plfa.Connectives.html#4547" class="InductiveConstructor">bb</a> <a id="4985" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a>  <a id="4988" class="Symbol">=</a>  <a id="4991" class="Number">5</a>
<a id="4993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4823" class="Function">×-count</a> <a id="5001" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="5003" href="plfa.Connectives.html#4499" class="InductiveConstructor">false</a> <a id="5009" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="5011" href="plfa.Connectives.html#4558" class="InductiveConstructor">cc</a> <a id="5014" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a>  <a id="5017" class="Symbol">=</a>  <a id="5020" class="Number">6</a>
</pre>{% endraw %}
Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative _up to
isomorphism_.

For commutativity, the `to` function swaps a pair, taking `⟨ x , y ⟩` to
`⟨ y , x ⟩`, and the `from` function does the same (up to renaming).
Instantiating the patterns correctly in `from∘to` and `to∘from` is essential.
Replacing the definition of `from∘to` by `λ w → refl` will not work;
and similarly for `to∘from`:
{% raw %}<pre class="Agda"><a id="×-comm"></a><a id="5559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#5559" class="Function">×-comm</a> <a id="5566" class="Symbol">:</a> <a id="5568" class="Symbol">∀</a> <a id="5570" class="Symbol">{</a><a id="5571" href="plfa.Connectives.html#5571" class="Bound">A</a> <a id="5573" href="plfa.Connectives.html#5573" class="Bound">B</a> <a id="5575" class="Symbol">:</a> <a id="5577" class="PrimitiveType">Set</a><a id="5580" class="Symbol">}</a> <a id="5582" class="Symbol">→</a> <a id="5584" href="plfa.Connectives.html#5571" class="Bound">A</a> <a id="5586" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="5588" href="plfa.Connectives.html#5573" class="Bound">B</a> <a id="5590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="5592" href="plfa.Connectives.html#5573" class="Bound">B</a> <a id="5594" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="5596" href="plfa.Connectives.html#5571" class="Bound">A</a>
<a id="5598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#5559" class="Function">×-comm</a> <a id="5605" class="Symbol">=</a>
  <a id="5609" class="Keyword">record</a>
    <a id="5620" class="Symbol">{</a> <a id="5622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4025" class="Field">to</a>       <a id="5631" class="Symbol">=</a>  <a id="5634" class="Symbol">λ{</a> <a id="5637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="5639" href="plfa.Connectives.html#5639" class="Bound">x</a> <a id="5641" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="5643" href="plfa.Connectives.html#5643" class="Bound">y</a> <a id="5645" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="5647" class="Symbol">→</a> <a id="5649" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="5651" href="plfa.Connectives.html#5643" class="Bound">y</a> <a id="5653" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="5655" href="plfa.Connectives.html#5639" class="Bound">x</a> <a id="5657" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="5659" class="Symbol">}</a>
    <a id="5665" class="Symbol">;</a> <a id="5667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4042" class="Field">from</a>     <a id="5676" class="Symbol">=</a>  <a id="5679" class="Symbol">λ{</a> <a id="5682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="5684" href="plfa.Connectives.html#5684" class="Bound">y</a> <a id="5686" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="5688" href="plfa.Connectives.html#5688" class="Bound">x</a> <a id="5690" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="5692" class="Symbol">→</a> <a id="5694" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="5696" href="plfa.Connectives.html#5688" class="Bound">x</a> <a id="5698" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="5700" href="plfa.Connectives.html#5684" class="Bound">y</a> <a id="5702" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="5704" class="Symbol">}</a>
    <a id="5710" class="Symbol">;</a> <a id="5712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4059" class="Field">from∘to</a>  <a id="5721" class="Symbol">=</a>  <a id="5724" class="Symbol">λ{</a> <a id="5727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="5729" href="plfa.Connectives.html#5729" class="Bound">x</a> <a id="5731" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="5733" href="plfa.Connectives.html#5733" class="Bound">y</a> <a id="5735" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="5737" class="Symbol">→</a> <a id="5739" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="5744" class="Symbol">}</a>
    <a id="5750" class="Symbol">;</a> <a id="5752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4101" class="Field">to∘from</a>  <a id="5761" class="Symbol">=</a>  <a id="5764" class="Symbol">λ{</a> <a id="5767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="5769" href="plfa.Connectives.html#5769" class="Bound">y</a> <a id="5771" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="5773" href="plfa.Connectives.html#5773" class="Bound">x</a> <a id="5775" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="5777" class="Symbol">→</a> <a id="5779" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="5784" class="Symbol">}</a>
    <a id="5790" class="Symbol">}</a>
</pre>{% endraw %}
Being _commutative_ is different from being _commutative up to
isomorphism_.  Compare the two statements:

    m * n ≡ n * m
    A × B ≃ B × A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
_not_ the same as `Tri × Bool`.  But there is an isomorphism between
the two types.  For instance, `⟨ true , aa ⟩`, which is a member of the
former, corresponds to `⟨ aa , true ⟩`, which is a member of the latter.

For associativity, the `to` function reassociates two uses of pairing,
taking `⟨ ⟨ x , y ⟩ , z ⟩` to `⟨ x , ⟨ y , z ⟩ ⟩`, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification:
{% raw %}<pre class="Agda"><a id="×-assoc"></a><a id="6646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6646" class="Function">×-assoc</a> <a id="6654" class="Symbol">:</a> <a id="6656" class="Symbol">∀</a> <a id="6658" class="Symbol">{</a><a id="6659" href="plfa.Connectives.html#6659" class="Bound">A</a> <a id="6661" href="plfa.Connectives.html#6661" class="Bound">B</a> <a id="6663" href="plfa.Connectives.html#6663" class="Bound">C</a> <a id="6665" class="Symbol">:</a> <a id="6667" class="PrimitiveType">Set</a><a id="6670" class="Symbol">}</a> <a id="6672" class="Symbol">→</a> <a id="6674" class="Symbol">(</a><a id="6675" href="plfa.Connectives.html#6659" class="Bound">A</a> <a id="6677" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="6679" href="plfa.Connectives.html#6661" class="Bound">B</a><a id="6680" class="Symbol">)</a> <a id="6682" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="6684" href="plfa.Connectives.html#6663" class="Bound">C</a> <a id="6686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="6688" href="plfa.Connectives.html#6659" class="Bound">A</a> <a id="6690" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="6692" class="Symbol">(</a><a id="6693" href="plfa.Connectives.html#6661" class="Bound">B</a> <a id="6695" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="6697" href="plfa.Connectives.html#6663" class="Bound">C</a><a id="6698" class="Symbol">)</a>
<a id="6700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6646" class="Function">×-assoc</a> <a id="6708" class="Symbol">=</a>
  <a id="6712" class="Keyword">record</a>
    <a id="6723" class="Symbol">{</a> <a id="6725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4025" class="Field">to</a>      <a id="6733" class="Symbol">=</a> <a id="6735" class="Symbol">λ{</a> <a id="6738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="6740" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="6742" href="plfa.Connectives.html#6742" class="Bound">x</a> <a id="6744" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6746" href="plfa.Connectives.html#6746" class="Bound">y</a> <a id="6748" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6750" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6752" href="plfa.Connectives.html#6752" class="Bound">z</a> <a id="6754" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6756" class="Symbol">→</a> <a id="6758" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="6760" href="plfa.Connectives.html#6742" class="Bound">x</a> <a id="6762" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6764" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="6766" href="plfa.Connectives.html#6746" class="Bound">y</a> <a id="6768" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6770" href="plfa.Connectives.html#6752" class="Bound">z</a> <a id="6772" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6774" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6776" class="Symbol">}</a>
    <a id="6782" class="Symbol">;</a> <a id="6784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4042" class="Field">from</a>    <a id="6792" class="Symbol">=</a> <a id="6794" class="Symbol">λ{</a> <a id="6797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="6799" href="plfa.Connectives.html#6799" class="Bound">x</a> <a id="6801" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6803" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="6805" href="plfa.Connectives.html#6805" class="Bound">y</a> <a id="6807" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6809" href="plfa.Connectives.html#6809" class="Bound">z</a> <a id="6811" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6813" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6815" class="Symbol">→</a> <a id="6817" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="6819" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="6821" href="plfa.Connectives.html#6799" class="Bound">x</a> <a id="6823" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6825" href="plfa.Connectives.html#6805" class="Bound">y</a> <a id="6827" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6829" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6831" href="plfa.Connectives.html#6809" class="Bound">z</a> <a id="6833" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6835" class="Symbol">}</a>
    <a id="6841" class="Symbol">;</a> <a id="6843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4059" class="Field">from∘to</a> <a id="6851" class="Symbol">=</a> <a id="6853" class="Symbol">λ{</a> <a id="6856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="6858" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="6860" href="plfa.Connectives.html#6860" class="Bound">x</a> <a id="6862" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6864" href="plfa.Connectives.html#6864" class="Bound">y</a> <a id="6866" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6868" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6870" href="plfa.Connectives.html#6870" class="Bound">z</a> <a id="6872" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6874" class="Symbol">→</a> <a id="6876" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="6881" class="Symbol">}</a>
    <a id="6887" class="Symbol">;</a> <a id="6889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4101" class="Field">to∘from</a> <a id="6897" class="Symbol">=</a> <a id="6899" class="Symbol">λ{</a> <a id="6902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="6904" href="plfa.Connectives.html#6904" class="Bound">x</a> <a id="6906" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6908" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="6910" href="plfa.Connectives.html#6910" class="Bound">y</a> <a id="6912" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="6914" href="plfa.Connectives.html#6914" class="Bound">z</a> <a id="6916" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6918" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="6920" class="Symbol">→</a> <a id="6922" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="6927" class="Symbol">}</a>
    <a id="6933" class="Symbol">}</a>
</pre>{% endraw %}
Being _associative_ is not the same as being _associative
up to isomorphism_.  Compare the two statements:

    (m * n) * p ≡ m * (n * p)
    (A × B) × C ≃ A × (B × C)

For example, the type `(ℕ × Bool) × Tri` is _not_ the same as `ℕ ×
(Bool × Tri)`. But there is an isomorphism between the two types. For
instance `⟨ ⟨ 1 , true ⟩ , aa ⟩`, which is a member of the former,
corresponds to `⟨ 1 , ⟨ true , aa ⟩ ⟩`, which is a member of the latter.

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier]({{ site.baseurl }}/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.

{% raw %}<pre class="Agda"><a id="7541" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Truth is unit

Truth `⊤` always holds. We formalise this idea by
declaring a suitable inductive type:
{% raw %}<pre class="Agda"><a id="7679" class="Keyword">data</a> <a id="⊤"></a><a id="7684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#7684" class="Datatype">⊤</a> <a id="7686" class="Symbol">:</a> <a id="7688" class="PrimitiveType">Set</a> <a id="7692" class="Keyword">where</a>

  <a id="⊤.tt"></a><a id="7701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#7701" class="InductiveConstructor">tt</a> <a id="7704" class="Symbol">:</a>
    <a id="7710" class="Comment">--</a>
    <a id="7717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#7684" class="Datatype">⊤</a>
</pre>{% endraw %}Evidence that `⊤` holds is of the form `tt`.

There is an introduction rule, but no elimination rule.
Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.

The nullary case of `η-×` is `η-⊤`, which asserts that any
value of type `⊤` must be equal to `tt`:
{% raw %}<pre class="Agda"><a id="η-⊤"></a><a id="8083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#8083" class="Function">η-⊤</a> <a id="8087" class="Symbol">:</a> <a id="8089" class="Symbol">∀</a> <a id="8091" class="Symbol">(</a><a id="8092" href="plfa.Connectives.html#8092" class="Bound">w</a> <a id="8094" class="Symbol">:</a> <a id="8096" href="plfa.Connectives.html#7684" class="Datatype">⊤</a><a id="8097" class="Symbol">)</a> <a id="8099" class="Symbol">→</a> <a id="8101" href="plfa.Connectives.html#7701" class="InductiveConstructor">tt</a> <a id="8104" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8106" href="plfa.Connectives.html#8092" class="Bound">w</a>
<a id="8108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#8083" class="Function">η-⊤</a> <a id="8112" href="plfa.Connectives.html#7701" class="InductiveConstructor">tt</a> <a id="8115" class="Symbol">=</a> <a id="8117" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}The pattern matching on the left-hand side is essential.  Replacing
`w` by `tt` allows both sides of the propositional equality to
simplify to the same term.

We refer to `⊤` as the _unit_ type. And, indeed,
type `⊤` has exactly one member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:
{% raw %}<pre class="Agda"><a id="⊤-count"></a><a id="8461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#8461" class="Function">⊤-count</a> <a id="8469" class="Symbol">:</a> <a id="8471" href="plfa.Connectives.html#7684" class="Datatype">⊤</a> <a id="8473" class="Symbol">→</a> <a id="8475" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="8477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#8461" class="Function">⊤-count</a> <a id="8485" href="plfa.Connectives.html#7701" class="InductiveConstructor">tt</a> <a id="8488" class="Symbol">=</a> <a id="8490" class="Number">1</a>
</pre>{% endraw %}
For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product _up to isomorphism_.  For left
identity, the `to` function takes `⟨ tt , x ⟩` to `x`, and the `from`
function does the inverse.  The evidence of left inverse requires
matching against a suitable pattern to enable simplification:
{% raw %}<pre class="Agda"><a id="⊤-identityˡ"></a><a id="8831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#8831" class="Function">⊤-identityˡ</a> <a id="8843" class="Symbol">:</a> <a id="8845" class="Symbol">∀</a> <a id="8847" class="Symbol">{</a><a id="8848" href="plfa.Connectives.html#8848" class="Bound">A</a> <a id="8850" class="Symbol">:</a> <a id="8852" class="PrimitiveType">Set</a><a id="8855" class="Symbol">}</a> <a id="8857" class="Symbol">→</a> <a id="8859" href="plfa.Connectives.html#7684" class="Datatype">⊤</a> <a id="8861" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="8863" href="plfa.Connectives.html#8848" class="Bound">A</a> <a id="8865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="8867" href="plfa.Connectives.html#8848" class="Bound">A</a>
<a id="8869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#8831" class="Function">⊤-identityˡ</a> <a id="8881" class="Symbol">=</a>
  <a id="8885" class="Keyword">record</a>
    <a id="8896" class="Symbol">{</a> <a id="8898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4025" class="Field">to</a>      <a id="8906" class="Symbol">=</a> <a id="8908" class="Symbol">λ{</a> <a id="8911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="8913" href="plfa.Connectives.html#7701" class="InductiveConstructor">tt</a> <a id="8916" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="8918" href="plfa.Connectives.html#8918" class="Bound">x</a> <a id="8920" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="8922" class="Symbol">→</a> <a id="8924" href="plfa.Connectives.html#8918" class="Bound">x</a> <a id="8926" class="Symbol">}</a>
    <a id="8932" class="Symbol">;</a> <a id="8934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4042" class="Field">from</a>    <a id="8942" class="Symbol">=</a> <a id="8944" class="Symbol">λ{</a> <a id="8947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#8947" class="Bound">x</a> <a id="8949" class="Symbol">→</a> <a id="8951" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="8953" href="plfa.Connectives.html#7701" class="InductiveConstructor">tt</a> <a id="8956" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="8958" href="plfa.Connectives.html#8947" class="Bound">x</a> <a id="8960" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="8962" class="Symbol">}</a>
    <a id="8968" class="Symbol">;</a> <a id="8970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4059" class="Field">from∘to</a> <a id="8978" class="Symbol">=</a> <a id="8980" class="Symbol">λ{</a> <a id="8983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="8985" href="plfa.Connectives.html#7701" class="InductiveConstructor">tt</a> <a id="8988" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="8990" href="plfa.Connectives.html#8990" class="Bound">x</a> <a id="8992" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="8994" class="Symbol">→</a> <a id="8996" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="9001" class="Symbol">}</a>
    <a id="9007" class="Symbol">;</a> <a id="9009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4101" class="Field">to∘from</a> <a id="9017" class="Symbol">=</a> <a id="9019" class="Symbol">λ{</a> <a id="9022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#9022" class="Bound">x</a> <a id="9024" class="Symbol">→</a> <a id="9026" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="9031" class="Symbol">}</a>
    <a id="9037" class="Symbol">}</a>
</pre>{% endraw %}
Having an _identity_ is different from having an identity
_up to isomorphism_.  Compare the two statements:

    1 * m ≡ m
    ⊤ × A ≃ A

In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is _not_ the
same as `Bool`.  But there is an isomorphism between the two types.
For instance, `⟨ tt , true ⟩`, which is a member of the former,
corresponds to `true`, which is a member of the latter.

Right identity follows from commutativity of product and left identity:
{% raw %}<pre class="Agda"><a id="⊤-identityʳ"></a><a id="9623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#9623" class="Function">⊤-identityʳ</a> <a id="9635" class="Symbol">:</a> <a id="9637" class="Symbol">∀</a> <a id="9639" class="Symbol">{</a><a id="9640" href="plfa.Connectives.html#9640" class="Bound">A</a> <a id="9642" class="Symbol">:</a> <a id="9644" class="PrimitiveType">Set</a><a id="9647" class="Symbol">}</a> <a id="9649" class="Symbol">→</a> <a id="9651" class="Symbol">(</a><a id="9652" href="plfa.Connectives.html#9640" class="Bound">A</a> <a id="9654" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="9656" href="plfa.Connectives.html#7684" class="Datatype">⊤</a><a id="9657" class="Symbol">)</a> <a id="9659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="9661" href="plfa.Connectives.html#9640" class="Bound">A</a>
<a id="9663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#9623" class="Function">⊤-identityʳ</a> <a id="9675" class="Symbol">{</a><a id="9676" href="plfa.Connectives.html#9676" class="Bound">A</a><a id="9677" class="Symbol">}</a> <a id="9679" class="Symbol">=</a>
  <a id="9683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8117" class="Function Operator">≃-begin</a>
    <a id="9695" class="Symbol">(</a><a id="9696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#9676" class="Bound">A</a> <a id="9698" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="9700" href="plfa.Connectives.html#7684" class="Datatype">⊤</a><a id="9701" class="Symbol">)</a>
  <a id="9705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8201" class="Function Operator">≃⟨</a> <a id="9708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#5559" class="Function">×-comm</a> <a id="9715" href="plfa.Isomorphism.html#8201" class="Function Operator">⟩</a>
    <a id="9721" class="Symbol">(</a><a id="9722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#7684" class="Datatype">⊤</a> <a id="9724" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="9726" href="plfa.Connectives.html#9676" class="Bound">A</a><a id="9727" class="Symbol">)</a>
  <a id="9731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8201" class="Function Operator">≃⟨</a> <a id="9734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#8831" class="Function">⊤-identityˡ</a> <a id="9746" href="plfa.Isomorphism.html#8201" class="Function Operator">⟩</a>
    <a id="9752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#9676" class="Bound">A</a>
  <a id="9756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8320" class="Function Operator">≃-∎</a>
</pre>{% endraw %}Here we have used a chain of isomorphisms, analogous to that used for
equality.


## Disjunction is sum

Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{% raw %}<pre class="Agda"><a id="10037" class="Keyword">data</a> <a id="_⊎_"></a><a id="10042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10042" class="Datatype Operator">_⊎_</a> <a id="10046" class="Symbol">(</a><a id="10047" href="plfa.Connectives.html#10047" class="Bound">A</a> <a id="10049" href="plfa.Connectives.html#10049" class="Bound">B</a> <a id="10051" class="Symbol">:</a> <a id="10053" class="PrimitiveType">Set</a><a id="10056" class="Symbol">)</a> <a id="10058" class="Symbol">:</a> <a id="10060" class="PrimitiveType">Set</a> <a id="10064" class="Keyword">where</a>

  <a id="_⊎_.inj₁"></a><a id="10073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10073" class="InductiveConstructor">inj₁</a> <a id="10078" class="Symbol">:</a>
      <a id="10086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10047" class="Bound">A</a>
      <a id="10094" class="Comment">-----</a>
    <a id="10104" class="Symbol">→</a> <a id="10106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10047" class="Bound">A</a> <a id="10108" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="10110" href="plfa.Connectives.html#10049" class="Bound">B</a>

  <a id="_⊎_.inj₂"></a><a id="10115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10115" class="InductiveConstructor">inj₂</a> <a id="10120" class="Symbol">:</a>
      <a id="10128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10049" class="Bound">B</a>
      <a id="10136" class="Comment">-----</a>
    <a id="10146" class="Symbol">→</a> <a id="10148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10047" class="Bound">A</a> <a id="10150" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="10152" href="plfa.Connectives.html#10049" class="Bound">B</a>
</pre>{% endraw %}Evidence that `A ⊎ B` holds is either of the form `inj₁ M`, where `M`
provides evidence that `A` holds, or `inj₂ N`, where `N` provides
evidence that `B` holds.

Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conclude that `C` holds:
{% raw %}<pre class="Agda"><a id="case-⊎"></a><a id="10446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10446" class="Function">case-⊎</a> <a id="10453" class="Symbol">:</a> <a id="10455" class="Symbol">∀</a> <a id="10457" class="Symbol">{</a><a id="10458" href="plfa.Connectives.html#10458" class="Bound">A</a> <a id="10460" href="plfa.Connectives.html#10460" class="Bound">B</a> <a id="10462" href="plfa.Connectives.html#10462" class="Bound">C</a> <a id="10464" class="Symbol">:</a> <a id="10466" class="PrimitiveType">Set</a><a id="10469" class="Symbol">}</a>
  <a id="10473" class="Symbol">→</a> <a id="10475" class="Symbol">(</a><a id="10476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10458" class="Bound">A</a> <a id="10478" class="Symbol">→</a> <a id="10480" href="plfa.Connectives.html#10462" class="Bound">C</a><a id="10481" class="Symbol">)</a>
  <a id="10485" class="Symbol">→</a> <a id="10487" class="Symbol">(</a><a id="10488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10460" class="Bound">B</a> <a id="10490" class="Symbol">→</a> <a id="10492" href="plfa.Connectives.html#10462" class="Bound">C</a><a id="10493" class="Symbol">)</a>
  <a id="10497" class="Symbol">→</a> <a id="10499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10458" class="Bound">A</a> <a id="10501" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="10503" href="plfa.Connectives.html#10460" class="Bound">B</a>
    <a id="10509" class="Comment">-----------</a>
  <a id="10523" class="Symbol">→</a> <a id="10525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10462" class="Bound">C</a>
<a id="10527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10446" class="Function">case-⊎</a> <a id="10534" href="plfa.Connectives.html#10534" class="Bound">f</a> <a id="10536" href="plfa.Connectives.html#10536" class="Bound">g</a> <a id="10538" class="Symbol">(</a><a id="10539" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="10544" href="plfa.Connectives.html#10544" class="Bound">x</a><a id="10545" class="Symbol">)</a> <a id="10547" class="Symbol">=</a> <a id="10549" href="plfa.Connectives.html#10534" class="Bound">f</a> <a id="10551" href="plfa.Connectives.html#10544" class="Bound">x</a>
<a id="10553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10446" class="Function">case-⊎</a> <a id="10560" href="plfa.Connectives.html#10560" class="Bound">f</a> <a id="10562" href="plfa.Connectives.html#10562" class="Bound">g</a> <a id="10564" class="Symbol">(</a><a id="10565" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="10570" href="plfa.Connectives.html#10570" class="Bound">y</a><a id="10571" class="Symbol">)</a> <a id="10573" class="Symbol">=</a> <a id="10575" href="plfa.Connectives.html#10562" class="Bound">g</a> <a id="10577" href="plfa.Connectives.html#10570" class="Bound">y</a>
</pre>{% endraw %}Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.

When `inj₁` and `inj₂` appear on the right-hand side of an equation we
refer to them as _constructors_, and when they appear on the
left-hand side we refer to them as _destructors_.  We also refer to
`case-⊎` as a destructor, since it plays a similar role.  Other
terminology refers to `inj₁` and `inj₂` as _introducing_ a
disjunction, and to `case-⊎` as _eliminating_ a disjunction; indeed
the former are sometimes given the names `⊎-I₁` and `⊎-I₂` and the
latter the name `⊎-E`.

Applying the destructor to each of the constructors is the identity:
{% raw %}<pre class="Agda"><a id="η-⊎"></a><a id="11246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11246" class="Function">η-⊎</a> <a id="11250" class="Symbol">:</a> <a id="11252" class="Symbol">∀</a> <a id="11254" class="Symbol">{</a><a id="11255" href="plfa.Connectives.html#11255" class="Bound">A</a> <a id="11257" href="plfa.Connectives.html#11257" class="Bound">B</a> <a id="11259" class="Symbol">:</a> <a id="11261" class="PrimitiveType">Set</a><a id="11264" class="Symbol">}</a> <a id="11266" class="Symbol">(</a><a id="11267" href="plfa.Connectives.html#11267" class="Bound">w</a> <a id="11269" class="Symbol">:</a> <a id="11271" href="plfa.Connectives.html#11255" class="Bound">A</a> <a id="11273" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="11275" href="plfa.Connectives.html#11257" class="Bound">B</a><a id="11276" class="Symbol">)</a> <a id="11278" class="Symbol">→</a> <a id="11280" href="plfa.Connectives.html#10446" class="Function">case-⊎</a> <a id="11287" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="11292" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="11297" href="plfa.Connectives.html#11267" class="Bound">w</a> <a id="11299" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11301" href="plfa.Connectives.html#11267" class="Bound">w</a>
<a id="11303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11246" class="Function">η-⊎</a> <a id="11307" class="Symbol">(</a><a id="11308" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="11313" href="plfa.Connectives.html#11313" class="Bound">x</a><a id="11314" class="Symbol">)</a> <a id="11316" class="Symbol">=</a> <a id="11318" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="11323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11246" class="Function">η-⊎</a> <a id="11327" class="Symbol">(</a><a id="11328" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="11333" href="plfa.Connectives.html#11333" class="Bound">y</a><a id="11334" class="Symbol">)</a> <a id="11336" class="Symbol">=</a> <a id="11338" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}More generally, we can also throw in an arbitrary function from a disjunction:
{% raw %}<pre class="Agda"><a id="uniq-⊎"></a><a id="11430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11430" class="Function">uniq-⊎</a> <a id="11437" class="Symbol">:</a> <a id="11439" class="Symbol">∀</a> <a id="11441" class="Symbol">{</a><a id="11442" href="plfa.Connectives.html#11442" class="Bound">A</a> <a id="11444" href="plfa.Connectives.html#11444" class="Bound">B</a> <a id="11446" href="plfa.Connectives.html#11446" class="Bound">C</a> <a id="11448" class="Symbol">:</a> <a id="11450" class="PrimitiveType">Set</a><a id="11453" class="Symbol">}</a> <a id="11455" class="Symbol">(</a><a id="11456" href="plfa.Connectives.html#11456" class="Bound">h</a> <a id="11458" class="Symbol">:</a> <a id="11460" href="plfa.Connectives.html#11442" class="Bound">A</a> <a id="11462" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="11464" href="plfa.Connectives.html#11444" class="Bound">B</a> <a id="11466" class="Symbol">→</a> <a id="11468" href="plfa.Connectives.html#11446" class="Bound">C</a><a id="11469" class="Symbol">)</a> <a id="11471" class="Symbol">(</a><a id="11472" href="plfa.Connectives.html#11472" class="Bound">w</a> <a id="11474" class="Symbol">:</a> <a id="11476" href="plfa.Connectives.html#11442" class="Bound">A</a> <a id="11478" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="11480" href="plfa.Connectives.html#11444" class="Bound">B</a><a id="11481" class="Symbol">)</a> <a id="11483" class="Symbol">→</a>
  <a id="11487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10446" class="Function">case-⊎</a> <a id="11494" class="Symbol">(</a><a id="11495" href="plfa.Connectives.html#11456" class="Bound">h</a> <a id="11497" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="11499" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a><a id="11503" class="Symbol">)</a> <a id="11505" class="Symbol">(</a><a id="11506" href="plfa.Connectives.html#11456" class="Bound">h</a> <a id="11508" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="11510" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a><a id="11514" class="Symbol">)</a> <a id="11516" href="plfa.Connectives.html#11472" class="Bound">w</a> <a id="11518" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11520" href="plfa.Connectives.html#11456" class="Bound">h</a> <a id="11522" href="plfa.Connectives.html#11472" class="Bound">w</a>
<a id="11524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11430" class="Function">uniq-⊎</a> <a id="11531" href="plfa.Connectives.html#11531" class="Bound">h</a> <a id="11533" class="Symbol">(</a><a id="11534" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="11539" href="plfa.Connectives.html#11539" class="Bound">x</a><a id="11540" class="Symbol">)</a> <a id="11542" class="Symbol">=</a> <a id="11544" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="11549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11430" class="Function">uniq-⊎</a> <a id="11556" href="plfa.Connectives.html#11556" class="Bound">h</a> <a id="11558" class="Symbol">(</a><a id="11559" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="11564" href="plfa.Connectives.html#11564" class="Bound">y</a><a id="11565" class="Symbol">)</a> <a id="11567" class="Symbol">=</a> <a id="11569" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}The pattern matching on the left-hand side is essential.  Replacing
`w` by `inj₁ x` allows both sides of the propositional equality to
simplify to the same term, and similarly for `inj₂ y`.

We set the precedence of disjunction so that it binds less tightly
than any other declared operator:
{% raw %}<pre class="Agda"><a id="11874" class="Keyword">infix</a> <a id="11880" class="Number">1</a> <a id="11882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10042" class="Datatype Operator">_⊎_</a>
</pre>{% endraw %}Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.

Given two types `A` and `B`, we refer to `A ⊎ B` as the
_sum_ of `A` and `B`.  In set theory, it is also sometimes
called the _disjoint union_, and in computing it corresponds
to a _variant record_ type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five
members:

    inj₁ true     inj₂ aa
    inj₁ false    inj₂ bb
                  inj₂ cc

For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
{% raw %}<pre class="Agda"><a id="⊎-count"></a><a id="12664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12664" class="Function">⊎-count</a> <a id="12672" class="Symbol">:</a> <a id="12674" href="plfa.Connectives.html#4465" class="Datatype">Bool</a> <a id="12679" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="12681" href="plfa.Connectives.html#4518" class="Datatype">Tri</a> <a id="12685" class="Symbol">→</a> <a id="12687" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="12689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12664" class="Function">⊎-count</a> <a id="12697" class="Symbol">(</a><a id="12698" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="12703" href="plfa.Connectives.html#4484" class="InductiveConstructor">true</a><a id="12707" class="Symbol">)</a>   <a id="12711" class="Symbol">=</a>  <a id="12714" class="Number">1</a>
<a id="12716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12664" class="Function">⊎-count</a> <a id="12724" class="Symbol">(</a><a id="12725" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="12730" href="plfa.Connectives.html#4499" class="InductiveConstructor">false</a><a id="12735" class="Symbol">)</a>  <a id="12738" class="Symbol">=</a>  <a id="12741" class="Number">2</a>
<a id="12743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12664" class="Function">⊎-count</a> <a id="12751" class="Symbol">(</a><a id="12752" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="12757" href="plfa.Connectives.html#4536" class="InductiveConstructor">aa</a><a id="12759" class="Symbol">)</a>     <a id="12765" class="Symbol">=</a>  <a id="12768" class="Number">3</a>
<a id="12770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12664" class="Function">⊎-count</a> <a id="12778" class="Symbol">(</a><a id="12779" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="12784" href="plfa.Connectives.html#4547" class="InductiveConstructor">bb</a><a id="12786" class="Symbol">)</a>     <a id="12792" class="Symbol">=</a>  <a id="12795" class="Number">4</a>
<a id="12797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12664" class="Function">⊎-count</a> <a id="12805" class="Symbol">(</a><a id="12806" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="12811" href="plfa.Connectives.html#4558" class="InductiveConstructor">cc</a><a id="12813" class="Symbol">)</a>     <a id="12819" class="Symbol">=</a>  <a id="12822" class="Number">5</a>
</pre>{% endraw %}
Sum on types also shares a property with sum on numbers in that it is
commutative and associative _up to isomorphism_.

#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

{% raw %}<pre class="Agda"><a id="13035" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-assoc`

Show sum is associative up to isomorphism.

{% raw %}<pre class="Agda"><a id="13136" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## False is empty

False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type:
{% raw %}<pre class="Agda"><a id="13274" class="Keyword">data</a> <a id="⊥"></a><a id="13279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13279" class="Datatype">⊥</a> <a id="13281" class="Symbol">:</a> <a id="13283" class="PrimitiveType">Set</a> <a id="13287" class="Keyword">where</a>
  <a id="13295" class="Comment">-- no clauses!</a>
</pre>{% endraw %}There is no possible evidence that `⊥` holds.

Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
Since false never holds, knowing that it holds tells us we are in a
paradoxical situation.  Given evidence that `⊥` holds, we might
conclude anything!  This is a basic principle of logic, known in
medieval times by the Latin phrase _ex falso_, and known to children
through phrases such as "if pigs had wings, then I'd be the Queen of
Sheba".  We formalise it as follows:
{% raw %}<pre class="Agda"><a id="⊥-elim"></a><a id="13813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13813" class="Function">⊥-elim</a> <a id="13820" class="Symbol">:</a> <a id="13822" class="Symbol">∀</a> <a id="13824" class="Symbol">{</a><a id="13825" href="plfa.Connectives.html#13825" class="Bound">A</a> <a id="13827" class="Symbol">:</a> <a id="13829" class="PrimitiveType">Set</a><a id="13832" class="Symbol">}</a>
  <a id="13836" class="Symbol">→</a> <a id="13838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13279" class="Datatype">⊥</a>
    <a id="13844" class="Comment">--</a>
  <a id="13849" class="Symbol">→</a> <a id="13851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13825" class="Bound">A</a>
<a id="13853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13813" class="Function">⊥-elim</a> <a id="13860" class="Symbol">()</a>
</pre>{% endraw %}This is our first use of the _absurd pattern_ `()`.
Here since `⊥` is a type with no members, we indicate that it is
_never_ possible to match against a value of this type by using
the pattern `()`.

The nullary case of `case-⊎` is `⊥-elim`.  By analogy,
we might have called it `case-⊥`, but chose to stick with the name
in the standard library.

The nullary case of `uniq-⊎` is `uniq-⊥`, which asserts that `⊥-elim`
is equal to any arbitrary function from `⊥`:
{% raw %}<pre class="Agda"><a id="uniq-⊥"></a><a id="14334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14334" class="Function">uniq-⊥</a> <a id="14341" class="Symbol">:</a> <a id="14343" class="Symbol">∀</a> <a id="14345" class="Symbol">{</a><a id="14346" href="plfa.Connectives.html#14346" class="Bound">C</a> <a id="14348" class="Symbol">:</a> <a id="14350" class="PrimitiveType">Set</a><a id="14353" class="Symbol">}</a> <a id="14355" class="Symbol">(</a><a id="14356" href="plfa.Connectives.html#14356" class="Bound">h</a> <a id="14358" class="Symbol">:</a> <a id="14360" href="plfa.Connectives.html#13279" class="Datatype">⊥</a> <a id="14362" class="Symbol">→</a> <a id="14364" href="plfa.Connectives.html#14346" class="Bound">C</a><a id="14365" class="Symbol">)</a> <a id="14367" class="Symbol">(</a><a id="14368" href="plfa.Connectives.html#14368" class="Bound">w</a> <a id="14370" class="Symbol">:</a> <a id="14372" href="plfa.Connectives.html#13279" class="Datatype">⊥</a><a id="14373" class="Symbol">)</a> <a id="14375" class="Symbol">→</a> <a id="14377" href="plfa.Connectives.html#13813" class="Function">⊥-elim</a> <a id="14384" href="plfa.Connectives.html#14368" class="Bound">w</a> <a id="14386" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14388" href="plfa.Connectives.html#14356" class="Bound">h</a> <a id="14390" href="plfa.Connectives.html#14368" class="Bound">w</a>
<a id="14392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14334" class="Function">uniq-⊥</a> <a id="14399" href="plfa.Connectives.html#14399" class="Bound">h</a> <a id="14401" class="Symbol">()</a>
</pre>{% endraw %}Using the absurd pattern asserts there are no possible values for `w`,
so the equation holds trivially.

We refer to `⊥` as the _empty_ type. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:
{% raw %}<pre class="Agda"><a id="⊥-count"></a><a id="14675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14675" class="Function">⊥-count</a> <a id="14683" class="Symbol">:</a> <a id="14685" href="plfa.Connectives.html#13279" class="Datatype">⊥</a> <a id="14687" class="Symbol">→</a> <a id="14689" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="14691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14675" class="Function">⊥-count</a> <a id="14699" class="Symbol">()</a>
</pre>{% endraw %}Here again the absurd pattern `()` indicates that no value can match
type `⊥`.

For numbers, zero is the identity of addition. Correspondingly, empty
is the identity of sums _up to isomorphism_.

#### Exercise `⊥-identityˡ` (recommended)

Show empty is the left identity of sums up to isomorphism.

{% raw %}<pre class="Agda"><a id="15009" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊥-identityʳ`

Show empty is the right identity of sums up to isomorphism.

{% raw %}<pre class="Agda"><a id="15131" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Implication is function {#implication}

Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.

Evidence that `A → B` holds is of the form

    λ (x : A) → N

where `N` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.

Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds:
{% raw %}<pre class="Agda"><a id="→-elim"></a><a id="15934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15934" class="Function">→-elim</a> <a id="15941" class="Symbol">:</a> <a id="15943" class="Symbol">∀</a> <a id="15945" class="Symbol">{</a><a id="15946" href="plfa.Connectives.html#15946" class="Bound">A</a> <a id="15948" href="plfa.Connectives.html#15948" class="Bound">B</a> <a id="15950" class="Symbol">:</a> <a id="15952" class="PrimitiveType">Set</a><a id="15955" class="Symbol">}</a>
  <a id="15959" class="Symbol">→</a> <a id="15961" class="Symbol">(</a><a id="15962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15946" class="Bound">A</a> <a id="15964" class="Symbol">→</a> <a id="15966" href="plfa.Connectives.html#15948" class="Bound">B</a><a id="15967" class="Symbol">)</a>
  <a id="15971" class="Symbol">→</a> <a id="15973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15946" class="Bound">A</a>
    <a id="15979" class="Comment">-------</a>
  <a id="15989" class="Symbol">→</a> <a id="15991" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15948" class="Bound">B</a>
<a id="15993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15934" class="Function">→-elim</a> <a id="16000" href="plfa.Connectives.html#16000" class="Bound">L</a> <a id="16002" href="plfa.Connectives.html#16002" class="Bound">M</a> <a id="16004" class="Symbol">=</a> <a id="16006" href="plfa.Connectives.html#16000" class="Bound">L</a> <a id="16008" href="plfa.Connectives.html#16002" class="Bound">M</a>
</pre>{% endraw %}In medieval times, this rule was known by the name _modus ponens_.
It corresponds to function application.

Defining a function, with a named definition or a lambda abstraction,
is referred to as _introducing_ a function,
while applying a function is referred to as _eliminating_ the function.

Elimination followed by introduction is the identity:
{% raw %}<pre class="Agda"><a id="η-→"></a><a id="16367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#16367" class="Function">η-→</a> <a id="16371" class="Symbol">:</a> <a id="16373" class="Symbol">∀</a> <a id="16375" class="Symbol">{</a><a id="16376" href="plfa.Connectives.html#16376" class="Bound">A</a> <a id="16378" href="plfa.Connectives.html#16378" class="Bound">B</a> <a id="16380" class="Symbol">:</a> <a id="16382" class="PrimitiveType">Set</a><a id="16385" class="Symbol">}</a> <a id="16387" class="Symbol">(</a><a id="16388" href="plfa.Connectives.html#16388" class="Bound">f</a> <a id="16390" class="Symbol">:</a> <a id="16392" href="plfa.Connectives.html#16376" class="Bound">A</a> <a id="16394" class="Symbol">→</a> <a id="16396" href="plfa.Connectives.html#16378" class="Bound">B</a><a id="16397" class="Symbol">)</a> <a id="16399" class="Symbol">→</a> <a id="16401" class="Symbol">(λ</a> <a id="16404" class="Symbol">(</a><a id="16405" href="plfa.Connectives.html#16405" class="Bound">x</a> <a id="16407" class="Symbol">:</a> <a id="16409" href="plfa.Connectives.html#16376" class="Bound">A</a><a id="16410" class="Symbol">)</a> <a id="16412" class="Symbol">→</a> <a id="16414" href="plfa.Connectives.html#16388" class="Bound">f</a> <a id="16416" href="plfa.Connectives.html#16405" class="Bound">x</a><a id="16417" class="Symbol">)</a> <a id="16419" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16421" href="plfa.Connectives.html#16388" class="Bound">f</a>
<a id="16423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#16367" class="Function">η-→</a> <a id="16427" href="plfa.Connectives.html#16427" class="Bound">f</a> <a id="16429" class="Symbol">=</a> <a id="16431" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.

Given two types `A` and `B`, we refer to `A → B` as the _function_
space from `A` to `B`.  It is also sometimes called the _exponential_,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
members, and type `B` has `n` distinct members, then the type
`A → B` has `nᵐ` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. Then the type `Bool → Tri` has nine (that is,
three squared) members:

    λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
    λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
    λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
{% raw %}<pre class="Agda"><a id="→-count"></a><a id="17439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17439" class="Function">→-count</a> <a id="17447" class="Symbol">:</a> <a id="17449" class="Symbol">(</a><a id="17450" href="plfa.Connectives.html#4465" class="Datatype">Bool</a> <a id="17455" class="Symbol">→</a> <a id="17457" href="plfa.Connectives.html#4518" class="Datatype">Tri</a><a id="17460" class="Symbol">)</a> <a id="17462" class="Symbol">→</a> <a id="17464" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="17466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17439" class="Function">→-count</a> <a id="17474" href="plfa.Connectives.html#17474" class="Bound">f</a> <a id="17476" class="Keyword">with</a> <a id="17481" href="plfa.Connectives.html#17474" class="Bound">f</a> <a id="17483" href="plfa.Connectives.html#4484" class="InductiveConstructor">true</a> <a id="17488" class="Symbol">|</a> <a id="17490" href="plfa.Connectives.html#17474" class="Bound">f</a> <a id="17492" href="plfa.Connectives.html#4499" class="InductiveConstructor">false</a>
<a id="17498" class="Symbol">...</a>          <a id="17511" class="Symbol">|</a> <a id="17513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4536" class="InductiveConstructor">aa</a>     <a id="17520" class="Symbol">|</a> <a id="17522" href="plfa.Connectives.html#4536" class="InductiveConstructor">aa</a>      <a id="17530" class="Symbol">=</a>   <a id="17534" class="Number">1</a>
<a id="17536" class="Symbol">...</a>          <a id="17549" class="Symbol">|</a> <a id="17551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4536" class="InductiveConstructor">aa</a>     <a id="17558" class="Symbol">|</a> <a id="17560" href="plfa.Connectives.html#4547" class="InductiveConstructor">bb</a>      <a id="17568" class="Symbol">=</a>   <a id="17572" class="Number">2</a>
<a id="17574" class="Symbol">...</a>          <a id="17587" class="Symbol">|</a> <a id="17589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4536" class="InductiveConstructor">aa</a>     <a id="17596" class="Symbol">|</a> <a id="17598" href="plfa.Connectives.html#4558" class="InductiveConstructor">cc</a>      <a id="17606" class="Symbol">=</a>   <a id="17610" class="Number">3</a>
<a id="17612" class="Symbol">...</a>          <a id="17625" class="Symbol">|</a> <a id="17627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4547" class="InductiveConstructor">bb</a>     <a id="17634" class="Symbol">|</a> <a id="17636" href="plfa.Connectives.html#4536" class="InductiveConstructor">aa</a>      <a id="17644" class="Symbol">=</a>   <a id="17648" class="Number">4</a>
<a id="17650" class="Symbol">...</a>          <a id="17663" class="Symbol">|</a> <a id="17665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4547" class="InductiveConstructor">bb</a>     <a id="17672" class="Symbol">|</a> <a id="17674" href="plfa.Connectives.html#4547" class="InductiveConstructor">bb</a>      <a id="17682" class="Symbol">=</a>   <a id="17686" class="Number">5</a>
<a id="17688" class="Symbol">...</a>          <a id="17701" class="Symbol">|</a> <a id="17703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4547" class="InductiveConstructor">bb</a>     <a id="17710" class="Symbol">|</a> <a id="17712" href="plfa.Connectives.html#4558" class="InductiveConstructor">cc</a>      <a id="17720" class="Symbol">=</a>   <a id="17724" class="Number">6</a>
<a id="17726" class="Symbol">...</a>          <a id="17739" class="Symbol">|</a> <a id="17741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4558" class="InductiveConstructor">cc</a>     <a id="17748" class="Symbol">|</a> <a id="17750" href="plfa.Connectives.html#4536" class="InductiveConstructor">aa</a>      <a id="17758" class="Symbol">=</a>   <a id="17762" class="Number">7</a>
<a id="17764" class="Symbol">...</a>          <a id="17777" class="Symbol">|</a> <a id="17779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4558" class="InductiveConstructor">cc</a>     <a id="17786" class="Symbol">|</a> <a id="17788" href="plfa.Connectives.html#4547" class="InductiveConstructor">bb</a>      <a id="17796" class="Symbol">=</a>   <a id="17800" class="Number">8</a>
<a id="17802" class="Symbol">...</a>          <a id="17815" class="Symbol">|</a> <a id="17817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4558" class="InductiveConstructor">cc</a>     <a id="17824" class="Symbol">|</a> <a id="17826" href="plfa.Connectives.html#4558" class="InductiveConstructor">cc</a>      <a id="17834" class="Symbol">=</a>   <a id="17838" class="Number">9</a>
</pre>{% endraw %}
Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.

Corresponding to the law

    (p ^ n) ^ m  ≡  p ^ (n * m)

we have the isomorphism

    A → (B → C)  ≃  (A × B) → C

Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality:
{% raw %}<pre class="Agda"><a id="currying"></a><a id="18364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#18364" class="Function">currying</a> <a id="18373" class="Symbol">:</a> <a id="18375" class="Symbol">∀</a> <a id="18377" class="Symbol">{</a><a id="18378" href="plfa.Connectives.html#18378" class="Bound">A</a> <a id="18380" href="plfa.Connectives.html#18380" class="Bound">B</a> <a id="18382" href="plfa.Connectives.html#18382" class="Bound">C</a> <a id="18384" class="Symbol">:</a> <a id="18386" class="PrimitiveType">Set</a><a id="18389" class="Symbol">}</a> <a id="18391" class="Symbol">→</a> <a id="18393" class="Symbol">(</a><a id="18394" href="plfa.Connectives.html#18378" class="Bound">A</a> <a id="18396" class="Symbol">→</a> <a id="18398" href="plfa.Connectives.html#18380" class="Bound">B</a> <a id="18400" class="Symbol">→</a> <a id="18402" href="plfa.Connectives.html#18382" class="Bound">C</a><a id="18403" class="Symbol">)</a> <a id="18405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="18407" class="Symbol">(</a><a id="18408" href="plfa.Connectives.html#18378" class="Bound">A</a> <a id="18410" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="18412" href="plfa.Connectives.html#18380" class="Bound">B</a> <a id="18414" class="Symbol">→</a> <a id="18416" href="plfa.Connectives.html#18382" class="Bound">C</a><a id="18417" class="Symbol">)</a>
<a id="18419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#18364" class="Function">currying</a> <a id="18428" class="Symbol">=</a>
  <a id="18432" class="Keyword">record</a>
    <a id="18443" class="Symbol">{</a> <a id="18445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4025" class="Field">to</a>      <a id="18453" class="Symbol">=</a>  <a id="18456" class="Symbol">λ{</a> <a id="18459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#18459" class="Bound">f</a> <a id="18461" class="Symbol">→</a> <a id="18463" class="Symbol">λ{</a> <a id="18466" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="18468" href="plfa.Connectives.html#18468" class="Bound">x</a> <a id="18470" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="18472" href="plfa.Connectives.html#18472" class="Bound">y</a> <a id="18474" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="18476" class="Symbol">→</a> <a id="18478" href="plfa.Connectives.html#18459" class="Bound">f</a> <a id="18480" href="plfa.Connectives.html#18468" class="Bound">x</a> <a id="18482" href="plfa.Connectives.html#18472" class="Bound">y</a> <a id="18484" class="Symbol">}}</a>
    <a id="18491" class="Symbol">;</a> <a id="18493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4042" class="Field">from</a>    <a id="18501" class="Symbol">=</a>  <a id="18504" class="Symbol">λ{</a> <a id="18507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#18507" class="Bound">g</a> <a id="18509" class="Symbol">→</a> <a id="18511" class="Symbol">λ{</a> <a id="18514" href="plfa.Connectives.html#18514" class="Bound">x</a> <a id="18516" class="Symbol">→</a> <a id="18518" class="Symbol">λ{</a> <a id="18521" href="plfa.Connectives.html#18521" class="Bound">y</a> <a id="18523" class="Symbol">→</a> <a id="18525" href="plfa.Connectives.html#18507" class="Bound">g</a> <a id="18527" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="18529" href="plfa.Connectives.html#18514" class="Bound">x</a> <a id="18531" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="18533" href="plfa.Connectives.html#18521" class="Bound">y</a> <a id="18535" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="18537" class="Symbol">}}}</a>
    <a id="18545" class="Symbol">;</a> <a id="18547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4059" class="Field">from∘to</a> <a id="18555" class="Symbol">=</a>  <a id="18558" class="Symbol">λ{</a> <a id="18561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#18561" class="Bound">f</a> <a id="18563" class="Symbol">→</a> <a id="18565" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="18570" class="Symbol">}</a>
    <a id="18576" class="Symbol">;</a> <a id="18578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4101" class="Field">to∘from</a> <a id="18586" class="Symbol">=</a>  <a id="18589" class="Symbol">λ{</a> <a id="18592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#18592" class="Bound">g</a> <a id="18594" class="Symbol">→</a> <a id="18596" href="plfa.Isomorphism.html#2678" class="Postulate">extensionality</a> <a id="18611" class="Symbol">λ{</a> <a id="18614" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="18616" href="plfa.Connectives.html#18616" class="Bound">x</a> <a id="18618" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="18620" href="plfa.Connectives.html#18620" class="Bound">y</a> <a id="18622" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="18624" class="Symbol">→</a> <a id="18626" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="18631" class="Symbol">}}</a>
    <a id="18638" class="Symbol">}</a>
</pre>{% endraw %}
Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, our way of writing addition

    _+_ : ℕ → ℕ → ℕ

is isomorphic to a function that accepts a pair of arguments:

    _+′_ : (ℕ × ℕ) → ℕ

Agda is optimised for currying, so `2 + 3` abbreviates `_+_ 2 3`.
In a language optimised for pairing, we would instead take `2 +′ 3` as
an abbreviation for `_+′_ ⟨ 2 , 3 ⟩`.

Corresponding to the law

    p ^ (n + m) = (p ^ n) * (p ^ m)

we have the isomorphism:

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.  The proof of the left inverse requires extensionality:
{% raw %}<pre class="Agda"><a id="→-distrib-⊎"></a><a id="19525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#19525" class="Function">→-distrib-⊎</a> <a id="19537" class="Symbol">:</a> <a id="19539" class="Symbol">∀</a> <a id="19541" class="Symbol">{</a><a id="19542" href="plfa.Connectives.html#19542" class="Bound">A</a> <a id="19544" href="plfa.Connectives.html#19544" class="Bound">B</a> <a id="19546" href="plfa.Connectives.html#19546" class="Bound">C</a> <a id="19548" class="Symbol">:</a> <a id="19550" class="PrimitiveType">Set</a><a id="19553" class="Symbol">}</a> <a id="19555" class="Symbol">→</a> <a id="19557" class="Symbol">(</a><a id="19558" href="plfa.Connectives.html#19542" class="Bound">A</a> <a id="19560" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="19562" href="plfa.Connectives.html#19544" class="Bound">B</a> <a id="19564" class="Symbol">→</a> <a id="19566" href="plfa.Connectives.html#19546" class="Bound">C</a><a id="19567" class="Symbol">)</a> <a id="19569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="19571" class="Symbol">((</a><a id="19573" href="plfa.Connectives.html#19542" class="Bound">A</a> <a id="19575" class="Symbol">→</a> <a id="19577" href="plfa.Connectives.html#19546" class="Bound">C</a><a id="19578" class="Symbol">)</a> <a id="19580" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="19582" class="Symbol">(</a><a id="19583" href="plfa.Connectives.html#19544" class="Bound">B</a> <a id="19585" class="Symbol">→</a> <a id="19587" href="plfa.Connectives.html#19546" class="Bound">C</a><a id="19588" class="Symbol">))</a>
<a id="19591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#19525" class="Function">→-distrib-⊎</a> <a id="19603" class="Symbol">=</a>
  <a id="19607" class="Keyword">record</a>
    <a id="19618" class="Symbol">{</a> <a id="19620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4025" class="Field">to</a>      <a id="19628" class="Symbol">=</a> <a id="19630" class="Symbol">λ{</a> <a id="19633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#19633" class="Bound">f</a> <a id="19635" class="Symbol">→</a> <a id="19637" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="19639" href="plfa.Connectives.html#19633" class="Bound">f</a> <a id="19641" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="19643" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="19648" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="19650" href="plfa.Connectives.html#19633" class="Bound">f</a> <a id="19652" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="19654" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="19659" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="19661" class="Symbol">}</a>
    <a id="19667" class="Symbol">;</a> <a id="19669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4042" class="Field">from</a>    <a id="19677" class="Symbol">=</a> <a id="19679" class="Symbol">λ{</a> <a id="19682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="19684" href="plfa.Connectives.html#19684" class="Bound">g</a> <a id="19686" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="19688" href="plfa.Connectives.html#19688" class="Bound">h</a> <a id="19690" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="19692" class="Symbol">→</a> <a id="19694" class="Symbol">λ{</a> <a id="19697" class="Symbol">(</a><a id="19698" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="19703" href="plfa.Connectives.html#19703" class="Bound">x</a><a id="19704" class="Symbol">)</a> <a id="19706" class="Symbol">→</a> <a id="19708" href="plfa.Connectives.html#19684" class="Bound">g</a> <a id="19710" href="plfa.Connectives.html#19703" class="Bound">x</a> <a id="19712" class="Symbol">;</a> <a id="19714" class="Symbol">(</a><a id="19715" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="19720" href="plfa.Connectives.html#19720" class="Bound">y</a><a id="19721" class="Symbol">)</a> <a id="19723" class="Symbol">→</a> <a id="19725" href="plfa.Connectives.html#19688" class="Bound">h</a> <a id="19727" href="plfa.Connectives.html#19720" class="Bound">y</a> <a id="19729" class="Symbol">}</a> <a id="19731" class="Symbol">}</a>
    <a id="19737" class="Symbol">;</a> <a id="19739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4059" class="Field">from∘to</a> <a id="19747" class="Symbol">=</a> <a id="19749" class="Symbol">λ{</a> <a id="19752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#19752" class="Bound">f</a> <a id="19754" class="Symbol">→</a> <a id="19756" href="plfa.Isomorphism.html#2678" class="Postulate">extensionality</a> <a id="19771" class="Symbol">λ{</a> <a id="19774" class="Symbol">(</a><a id="19775" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="19780" href="plfa.Connectives.html#19780" class="Bound">x</a><a id="19781" class="Symbol">)</a> <a id="19783" class="Symbol">→</a> <a id="19785" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19790" class="Symbol">;</a> <a id="19792" class="Symbol">(</a><a id="19793" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="19798" href="plfa.Connectives.html#19798" class="Bound">y</a><a id="19799" class="Symbol">)</a> <a id="19801" class="Symbol">→</a> <a id="19803" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19808" class="Symbol">}</a> <a id="19810" class="Symbol">}</a>
    <a id="19816" class="Symbol">;</a> <a id="19818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4101" class="Field">to∘from</a> <a id="19826" class="Symbol">=</a> <a id="19828" class="Symbol">λ{</a> <a id="19831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="19833" href="plfa.Connectives.html#19833" class="Bound">g</a> <a id="19835" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="19837" href="plfa.Connectives.html#19837" class="Bound">h</a> <a id="19839" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="19841" class="Symbol">→</a> <a id="19843" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19848" class="Symbol">}</a>
    <a id="19854" class="Symbol">}</a>
</pre>{% endraw %}
Corresponding to the law

    (p * n) ^ m = (p ^ m) * (n ^ m)

we have the isomorphism:

    A → B × C  ≃  (A → B) × (A → C)

That is, the assertion that if `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof of left inverse requires both extensionality
and the rule `η-×` for products:
{% raw %}<pre class="Agda"><a id="→-distrib-×"></a><a id="20245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20245" class="Function">→-distrib-×</a> <a id="20257" class="Symbol">:</a> <a id="20259" class="Symbol">∀</a> <a id="20261" class="Symbol">{</a><a id="20262" href="plfa.Connectives.html#20262" class="Bound">A</a> <a id="20264" href="plfa.Connectives.html#20264" class="Bound">B</a> <a id="20266" href="plfa.Connectives.html#20266" class="Bound">C</a> <a id="20268" class="Symbol">:</a> <a id="20270" class="PrimitiveType">Set</a><a id="20273" class="Symbol">}</a> <a id="20275" class="Symbol">→</a> <a id="20277" class="Symbol">(</a><a id="20278" href="plfa.Connectives.html#20262" class="Bound">A</a> <a id="20280" class="Symbol">→</a> <a id="20282" href="plfa.Connectives.html#20264" class="Bound">B</a> <a id="20284" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="20286" href="plfa.Connectives.html#20266" class="Bound">C</a><a id="20287" class="Symbol">)</a> <a id="20289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="20291" class="Symbol">(</a><a id="20292" href="plfa.Connectives.html#20262" class="Bound">A</a> <a id="20294" class="Symbol">→</a> <a id="20296" href="plfa.Connectives.html#20264" class="Bound">B</a><a id="20297" class="Symbol">)</a> <a id="20299" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="20301" class="Symbol">(</a><a id="20302" href="plfa.Connectives.html#20262" class="Bound">A</a> <a id="20304" class="Symbol">→</a> <a id="20306" href="plfa.Connectives.html#20266" class="Bound">C</a><a id="20307" class="Symbol">)</a>
<a id="20309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20245" class="Function">→-distrib-×</a> <a id="20321" class="Symbol">=</a>
  <a id="20325" class="Keyword">record</a>
    <a id="20336" class="Symbol">{</a> <a id="20338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4025" class="Field">to</a>      <a id="20346" class="Symbol">=</a> <a id="20348" class="Symbol">λ{</a> <a id="20351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20351" class="Bound">f</a> <a id="20353" class="Symbol">→</a> <a id="20355" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="20357" href="plfa.Connectives.html#1593" class="Function">proj₁</a> <a id="20363" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="20365" href="plfa.Connectives.html#20351" class="Bound">f</a> <a id="20367" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20369" href="plfa.Connectives.html#1662" class="Function">proj₂</a> <a id="20375" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="20377" href="plfa.Connectives.html#20351" class="Bound">f</a> <a id="20379" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="20381" class="Symbol">}</a>
    <a id="20387" class="Symbol">;</a> <a id="20389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4042" class="Field">from</a>    <a id="20397" class="Symbol">=</a> <a id="20399" class="Symbol">λ{</a> <a id="20402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="20404" href="plfa.Connectives.html#20404" class="Bound">g</a> <a id="20406" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20408" href="plfa.Connectives.html#20408" class="Bound">h</a> <a id="20410" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="20412" class="Symbol">→</a> <a id="20414" class="Symbol">λ</a> <a id="20416" href="plfa.Connectives.html#20416" class="Bound">x</a> <a id="20418" class="Symbol">→</a> <a id="20420" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="20422" href="plfa.Connectives.html#20404" class="Bound">g</a> <a id="20424" href="plfa.Connectives.html#20416" class="Bound">x</a> <a id="20426" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20428" href="plfa.Connectives.html#20408" class="Bound">h</a> <a id="20430" href="plfa.Connectives.html#20416" class="Bound">x</a> <a id="20432" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="20434" class="Symbol">}</a>
    <a id="20440" class="Symbol">;</a> <a id="20442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4059" class="Field">from∘to</a> <a id="20450" class="Symbol">=</a> <a id="20452" class="Symbol">λ{</a> <a id="20455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20455" class="Bound">f</a> <a id="20457" class="Symbol">→</a> <a id="20459" href="plfa.Isomorphism.html#2678" class="Postulate">extensionality</a> <a id="20474" class="Symbol">λ{</a> <a id="20477" href="plfa.Connectives.html#20477" class="Bound">x</a> <a id="20479" class="Symbol">→</a> <a id="20481" href="plfa.Connectives.html#3544" class="Function">η-×</a> <a id="20485" class="Symbol">(</a><a id="20486" href="plfa.Connectives.html#20455" class="Bound">f</a> <a id="20488" href="plfa.Connectives.html#20477" class="Bound">x</a><a id="20489" class="Symbol">)</a> <a id="20491" class="Symbol">}</a> <a id="20493" class="Symbol">}</a>
    <a id="20499" class="Symbol">;</a> <a id="20501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4101" class="Field">to∘from</a> <a id="20509" class="Symbol">=</a> <a id="20511" class="Symbol">λ{</a> <a id="20514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="20516" href="plfa.Connectives.html#20516" class="Bound">g</a> <a id="20518" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20520" href="plfa.Connectives.html#20520" class="Bound">h</a> <a id="20522" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="20524" class="Symbol">→</a> <a id="20526" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="20531" class="Symbol">}</a>
    <a id="20537" class="Symbol">}</a>
</pre>{% endraw %}

## Distribution

Products distribute over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results:
{% raw %}<pre class="Agda"><a id="×-distrib-⊎"></a><a id="20696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20696" class="Function">×-distrib-⊎</a> <a id="20708" class="Symbol">:</a> <a id="20710" class="Symbol">∀</a> <a id="20712" class="Symbol">{</a><a id="20713" href="plfa.Connectives.html#20713" class="Bound">A</a> <a id="20715" href="plfa.Connectives.html#20715" class="Bound">B</a> <a id="20717" href="plfa.Connectives.html#20717" class="Bound">C</a> <a id="20719" class="Symbol">:</a> <a id="20721" class="PrimitiveType">Set</a><a id="20724" class="Symbol">}</a> <a id="20726" class="Symbol">→</a> <a id="20728" class="Symbol">(</a><a id="20729" href="plfa.Connectives.html#20713" class="Bound">A</a> <a id="20731" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="20733" href="plfa.Connectives.html#20715" class="Bound">B</a><a id="20734" class="Symbol">)</a> <a id="20736" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="20738" href="plfa.Connectives.html#20717" class="Bound">C</a> <a id="20740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="20742" class="Symbol">(</a><a id="20743" href="plfa.Connectives.html#20713" class="Bound">A</a> <a id="20745" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="20747" href="plfa.Connectives.html#20717" class="Bound">C</a><a id="20748" class="Symbol">)</a> <a id="20750" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="20752" class="Symbol">(</a><a id="20753" href="plfa.Connectives.html#20715" class="Bound">B</a> <a id="20755" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="20757" href="plfa.Connectives.html#20717" class="Bound">C</a><a id="20758" class="Symbol">)</a>
<a id="20760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20696" class="Function">×-distrib-⊎</a> <a id="20772" class="Symbol">=</a>
  <a id="20776" class="Keyword">record</a>
    <a id="20787" class="Symbol">{</a> <a id="20789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4025" class="Field">to</a>      <a id="20797" class="Symbol">=</a> <a id="20799" class="Symbol">λ{</a> <a id="20802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="20804" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="20809" href="plfa.Connectives.html#20809" class="Bound">x</a> <a id="20811" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20813" href="plfa.Connectives.html#20813" class="Bound">z</a> <a id="20815" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="20817" class="Symbol">→</a> <a id="20819" class="Symbol">(</a><a id="20820" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="20825" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="20827" href="plfa.Connectives.html#20809" class="Bound">x</a> <a id="20829" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20831" href="plfa.Connectives.html#20813" class="Bound">z</a> <a id="20833" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a><a id="20834" class="Symbol">)</a>
                 <a id="20853" class="Symbol">;</a> <a id="20855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="20857" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="20862" href="plfa.Connectives.html#20862" class="Bound">y</a> <a id="20864" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20866" href="plfa.Connectives.html#20866" class="Bound">z</a> <a id="20868" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="20870" class="Symbol">→</a> <a id="20872" class="Symbol">(</a><a id="20873" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="20878" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="20880" href="plfa.Connectives.html#20862" class="Bound">y</a> <a id="20882" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20884" href="plfa.Connectives.html#20866" class="Bound">z</a> <a id="20886" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a><a id="20887" class="Symbol">)</a>
                 <a id="20906" class="Symbol">}</a>
    <a id="20912" class="Symbol">;</a> <a id="20914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4042" class="Field">from</a>    <a id="20922" class="Symbol">=</a> <a id="20924" class="Symbol">λ{</a> <a id="20927" class="Symbol">(</a><a id="20928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10073" class="InductiveConstructor">inj₁</a> <a id="20933" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="20935" href="plfa.Connectives.html#20935" class="Bound">x</a> <a id="20937" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20939" href="plfa.Connectives.html#20939" class="Bound">z</a> <a id="20941" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a><a id="20942" class="Symbol">)</a> <a id="20944" class="Symbol">→</a> <a id="20946" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="20948" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="20953" href="plfa.Connectives.html#20935" class="Bound">x</a> <a id="20955" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20957" href="plfa.Connectives.html#20939" class="Bound">z</a> <a id="20959" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a>
                 <a id="20978" class="Symbol">;</a> <a id="20980" class="Symbol">(</a><a id="20981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10115" class="InductiveConstructor">inj₂</a> <a id="20986" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="20988" href="plfa.Connectives.html#20988" class="Bound">y</a> <a id="20990" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="20992" href="plfa.Connectives.html#20992" class="Bound">z</a> <a id="20994" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a><a id="20995" class="Symbol">)</a> <a id="20997" class="Symbol">→</a> <a id="20999" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="21001" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="21006" href="plfa.Connectives.html#20988" class="Bound">y</a> <a id="21008" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21010" href="plfa.Connectives.html#20992" class="Bound">z</a> <a id="21012" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a>
                 <a id="21031" class="Symbol">}</a>
    <a id="21037" class="Symbol">;</a> <a id="21039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4059" class="Field">from∘to</a> <a id="21047" class="Symbol">=</a> <a id="21049" class="Symbol">λ{</a> <a id="21052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="21054" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="21059" href="plfa.Connectives.html#21059" class="Bound">x</a> <a id="21061" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21063" href="plfa.Connectives.html#21063" class="Bound">z</a> <a id="21065" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="21067" class="Symbol">→</a> <a id="21069" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21091" class="Symbol">;</a> <a id="21093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="21095" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="21100" href="plfa.Connectives.html#21100" class="Bound">y</a> <a id="21102" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21104" href="plfa.Connectives.html#21104" class="Bound">z</a> <a id="21106" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="21108" class="Symbol">→</a> <a id="21110" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21132" class="Symbol">}</a>
    <a id="21138" class="Symbol">;</a> <a id="21140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4101" class="Field">to∘from</a> <a id="21148" class="Symbol">=</a> <a id="21150" class="Symbol">λ{</a> <a id="21153" class="Symbol">(</a><a id="21154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10073" class="InductiveConstructor">inj₁</a> <a id="21159" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="21161" href="plfa.Connectives.html#21161" class="Bound">x</a> <a id="21163" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21165" href="plfa.Connectives.html#21165" class="Bound">z</a> <a id="21167" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a><a id="21168" class="Symbol">)</a> <a id="21170" class="Symbol">→</a> <a id="21172" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21194" class="Symbol">;</a> <a id="21196" class="Symbol">(</a><a id="21197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10115" class="InductiveConstructor">inj₂</a> <a id="21202" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="21204" href="plfa.Connectives.html#21204" class="Bound">y</a> <a id="21206" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21208" href="plfa.Connectives.html#21208" class="Bound">z</a> <a id="21210" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a><a id="21211" class="Symbol">)</a> <a id="21213" class="Symbol">→</a> <a id="21215" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21237" class="Symbol">}</a>
    <a id="21243" class="Symbol">}</a>
</pre>{% endraw %}
Sums do not distribute over products up to isomorphism, but it is an embedding:
{% raw %}<pre class="Agda"><a id="⊎-distrib-×"></a><a id="21334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#21334" class="Function">⊎-distrib-×</a> <a id="21346" class="Symbol">:</a> <a id="21348" class="Symbol">∀</a> <a id="21350" class="Symbol">{</a><a id="21351" href="plfa.Connectives.html#21351" class="Bound">A</a> <a id="21353" href="plfa.Connectives.html#21353" class="Bound">B</a> <a id="21355" href="plfa.Connectives.html#21355" class="Bound">C</a> <a id="21357" class="Symbol">:</a> <a id="21359" class="PrimitiveType">Set</a><a id="21362" class="Symbol">}</a> <a id="21364" class="Symbol">→</a> <a id="21366" class="Symbol">(</a><a id="21367" href="plfa.Connectives.html#21351" class="Bound">A</a> <a id="21369" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="21371" href="plfa.Connectives.html#21353" class="Bound">B</a><a id="21372" class="Symbol">)</a> <a id="21374" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="21376" href="plfa.Connectives.html#21355" class="Bound">C</a> <a id="21378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8806" class="Record Operator">≲</a> <a id="21380" class="Symbol">(</a><a id="21381" href="plfa.Connectives.html#21351" class="Bound">A</a> <a id="21383" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="21385" href="plfa.Connectives.html#21355" class="Bound">C</a><a id="21386" class="Symbol">)</a> <a id="21388" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="21390" class="Symbol">(</a><a id="21391" href="plfa.Connectives.html#21353" class="Bound">B</a> <a id="21393" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="21395" href="plfa.Connectives.html#21355" class="Bound">C</a><a id="21396" class="Symbol">)</a>
<a id="21398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#21334" class="Function">⊎-distrib-×</a> <a id="21410" class="Symbol">=</a>
  <a id="21414" class="Keyword">record</a>
    <a id="21425" class="Symbol">{</a> <a id="21427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8846" class="Field">to</a>      <a id="21435" class="Symbol">=</a> <a id="21437" class="Symbol">λ{</a> <a id="21440" class="Symbol">(</a><a id="21441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10073" class="InductiveConstructor">inj₁</a> <a id="21446" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="21448" href="plfa.Connectives.html#21448" class="Bound">x</a> <a id="21450" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21452" href="plfa.Connectives.html#21452" class="Bound">y</a> <a id="21454" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a><a id="21455" class="Symbol">)</a> <a id="21457" class="Symbol">→</a> <a id="21459" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="21461" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="21466" href="plfa.Connectives.html#21448" class="Bound">x</a> <a id="21468" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21470" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="21475" href="plfa.Connectives.html#21452" class="Bound">y</a> <a id="21477" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a>
                 <a id="21496" class="Symbol">;</a> <a id="21498" class="Symbol">(</a><a id="21499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10115" class="InductiveConstructor">inj₂</a> <a id="21504" href="plfa.Connectives.html#21504" class="Bound">z</a><a id="21505" class="Symbol">)</a>         <a id="21515" class="Symbol">→</a> <a id="21517" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="21519" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="21524" href="plfa.Connectives.html#21504" class="Bound">z</a> <a id="21526" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21528" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="21533" href="plfa.Connectives.html#21504" class="Bound">z</a> <a id="21535" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a>
                 <a id="21554" class="Symbol">}</a>
    <a id="21560" class="Symbol">;</a> <a id="21562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8866" class="Field">from</a>    <a id="21570" class="Symbol">=</a> <a id="21572" class="Symbol">λ{</a> <a id="21575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="21577" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="21582" href="plfa.Connectives.html#21582" class="Bound">x</a> <a id="21584" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21586" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="21591" href="plfa.Connectives.html#21591" class="Bound">y</a> <a id="21593" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="21595" class="Symbol">→</a> <a id="21597" class="Symbol">(</a><a id="21598" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="21603" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="21605" href="plfa.Connectives.html#21582" class="Bound">x</a> <a id="21607" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21609" href="plfa.Connectives.html#21591" class="Bound">y</a> <a id="21611" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a><a id="21612" class="Symbol">)</a>
                 <a id="21631" class="Symbol">;</a> <a id="21633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="21635" href="plfa.Connectives.html#10073" class="InductiveConstructor">inj₁</a> <a id="21640" href="plfa.Connectives.html#21640" class="Bound">x</a> <a id="21642" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21644" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="21649" href="plfa.Connectives.html#21649" class="Bound">z</a> <a id="21651" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="21653" class="Symbol">→</a> <a id="21655" class="Symbol">(</a><a id="21656" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="21661" href="plfa.Connectives.html#21649" class="Bound">z</a><a id="21662" class="Symbol">)</a>
                 <a id="21681" class="Symbol">;</a> <a id="21683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1308" class="InductiveConstructor Operator">⟨</a> <a id="21685" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="21690" href="plfa.Connectives.html#21690" class="Bound">z</a> <a id="21692" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21694" class="Symbol">_</a>      <a id="21701" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a> <a id="21703" class="Symbol">→</a> <a id="21705" class="Symbol">(</a><a id="21706" href="plfa.Connectives.html#10115" class="InductiveConstructor">inj₂</a> <a id="21711" href="plfa.Connectives.html#21690" class="Bound">z</a><a id="21712" class="Symbol">)</a>
                 <a id="21731" class="Symbol">}</a>
    <a id="21737" class="Symbol">;</a> <a id="21739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8886" class="Field">from∘to</a> <a id="21747" class="Symbol">=</a> <a id="21749" class="Symbol">λ{</a> <a id="21752" class="Symbol">(</a><a id="21753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10073" class="InductiveConstructor">inj₁</a> <a id="21758" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟨</a> <a id="21760" href="plfa.Connectives.html#21760" class="Bound">x</a> <a id="21762" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">,</a> <a id="21764" href="plfa.Connectives.html#21764" class="Bound">y</a> <a id="21766" href="plfa.Connectives.html#1308" class="InductiveConstructor Operator">⟩</a><a id="21767" class="Symbol">)</a> <a id="21769" class="Symbol">→</a> <a id="21771" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21793" class="Symbol">;</a> <a id="21795" class="Symbol">(</a><a id="21796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10115" class="InductiveConstructor">inj₂</a> <a id="21801" href="plfa.Connectives.html#21801" class="Bound">z</a><a id="21802" class="Symbol">)</a>         <a id="21812" class="Symbol">→</a> <a id="21814" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="21836" class="Symbol">}</a>
    <a id="21842" class="Symbol">}</a>
</pre>{% endraw %}Note that there is a choice in how we write the `from` function.
As given, it takes `⟨ inj₂ z , inj₂ z′ ⟩` to `inj₂ z`, but it is
easy to write a variant that instead returns `inj₂ z′`.  We have
an embedding rather than an isomorphism because the
`from` function must discard either `z` or `z′` in this case.

In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:

    A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
    A ⊎ (B × C) ⇔ (A ⊎ B) × (A ⊎ C)

But when we consider the functions that provide evidence for these
implications, then the first corresponds to an isomorphism while the
second only corresponds to an embedding, revealing a sense in which
one of these laws is "more true" than the other.


#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds:
{% raw %}<pre class="Agda"><a id="22695" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="22707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22707" class="Postulate">⊎-weak-×</a> <a id="22716" class="Symbol">:</a> <a id="22718" class="Symbol">∀</a> <a id="22720" class="Symbol">{</a><a id="22721" href="plfa.Connectives.html#22721" class="Bound">A</a> <a id="22723" href="plfa.Connectives.html#22723" class="Bound">B</a> <a id="22725" href="plfa.Connectives.html#22725" class="Bound">C</a> <a id="22727" class="Symbol">:</a> <a id="22729" class="PrimitiveType">Set</a><a id="22732" class="Symbol">}</a> <a id="22734" class="Symbol">→</a> <a id="22736" class="Symbol">(</a><a id="22737" href="plfa.Connectives.html#22721" class="Bound">A</a> <a id="22739" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="22741" href="plfa.Connectives.html#22723" class="Bound">B</a><a id="22742" class="Symbol">)</a> <a id="22744" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="22746" href="plfa.Connectives.html#22725" class="Bound">C</a> <a id="22748" class="Symbol">→</a> <a id="22750" href="plfa.Connectives.html#22721" class="Bound">A</a> <a id="22752" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="22754" class="Symbol">(</a><a id="22755" href="plfa.Connectives.html#22723" class="Bound">B</a> <a id="22757" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="22759" href="plfa.Connectives.html#22725" class="Bound">C</a><a id="22760" class="Symbol">)</a>
</pre>{% endraw %}This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

{% raw %}<pre class="Agda"><a id="22902" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `⊎×-implies-×⊎`

Show that a disjunct of conjuncts implies a conjunct of disjuncts:
{% raw %}<pre class="Agda"><a id="23033" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="23045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#23045" class="Postulate">⊎×-implies-×⊎</a> <a id="23059" class="Symbol">:</a> <a id="23061" class="Symbol">∀</a> <a id="23063" class="Symbol">{</a><a id="23064" href="plfa.Connectives.html#23064" class="Bound">A</a> <a id="23066" href="plfa.Connectives.html#23066" class="Bound">B</a> <a id="23068" href="plfa.Connectives.html#23068" class="Bound">C</a> <a id="23070" href="plfa.Connectives.html#23070" class="Bound">D</a> <a id="23072" class="Symbol">:</a> <a id="23074" class="PrimitiveType">Set</a><a id="23077" class="Symbol">}</a> <a id="23079" class="Symbol">→</a> <a id="23081" class="Symbol">(</a><a id="23082" href="plfa.Connectives.html#23064" class="Bound">A</a> <a id="23084" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="23086" href="plfa.Connectives.html#23066" class="Bound">B</a><a id="23087" class="Symbol">)</a> <a id="23089" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="23091" class="Symbol">(</a><a id="23092" href="plfa.Connectives.html#23068" class="Bound">C</a> <a id="23094" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="23096" href="plfa.Connectives.html#23070" class="Bound">D</a><a id="23097" class="Symbol">)</a> <a id="23099" class="Symbol">→</a> <a id="23101" class="Symbol">(</a><a id="23102" href="plfa.Connectives.html#23064" class="Bound">A</a> <a id="23104" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="23106" href="plfa.Connectives.html#23068" class="Bound">C</a><a id="23107" class="Symbol">)</a> <a id="23109" href="plfa.Connectives.html#1277" class="Datatype Operator">×</a> <a id="23111" class="Symbol">(</a><a id="23112" href="plfa.Connectives.html#23066" class="Bound">B</a> <a id="23114" href="plfa.Connectives.html#10042" class="Datatype Operator">⊎</a> <a id="23116" href="plfa.Connectives.html#23070" class="Bound">D</a><a id="23117" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, give a counterexample.

{% raw %}<pre class="Agda"><a id="23197" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="23334" class="Keyword">import</a> <a id="23341" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="23354" class="Keyword">using</a> <a id="23360" class="Symbol">(</a><a id="23361" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="23364" class="Symbol">;</a> <a id="23366" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="23371" class="Symbol">;</a> <a id="23373" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="23378" class="Symbol">)</a> <a id="23380" class="Keyword">renaming</a> <a id="23389" class="Symbol">(</a><a id="23390" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="23394" class="Symbol">to</a> <a id="23397" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="23402" class="Symbol">)</a>
<a id="23404" class="Keyword">import</a> <a id="23411" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="23421" class="Keyword">using</a> <a id="23427" class="Symbol">(</a><a id="23428" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="23429" class="Symbol">;</a> <a id="23431" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="23433" class="Symbol">)</a>
<a id="23435" class="Keyword">import</a> <a id="23442" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="23451" class="Keyword">using</a> <a id="23457" class="Symbol">(</a><a id="23458" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="23461" class="Symbol">;</a> <a id="23463" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="23467" class="Symbol">;</a> <a id="23469" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="23473" class="Symbol">)</a> <a id="23475" class="Keyword">renaming</a> <a id="23484" class="Symbol">(</a><a id="23485" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="23491" class="Symbol">to</a> <a id="23494" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="23500" class="Symbol">)</a>
<a id="23502" class="Keyword">import</a> <a id="23509" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="23520" class="Keyword">using</a> <a id="23526" class="Symbol">(</a><a id="23527" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="23528" class="Symbol">;</a> <a id="23530" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="23536" class="Symbol">)</a>
<a id="23538" class="Keyword">import</a> <a id="23545" href="https://agda.github.io/agda-stdlib/v1.1/Function.Equivalence.html" class="Module">Function.Equivalence</a> <a id="23566" class="Keyword">using</a> <a id="23572" class="Symbol">(</a><a id="23573" href="https://agda.github.io/agda-stdlib/v1.1/Function.Equivalence.html#971" class="Function Operator">_⇔_</a><a id="23576" class="Symbol">)</a>
</pre>{% endraw %}The standard library constructs pairs with `_,_` whereas we use `⟨_,_⟩`.
The former makes it convenient to build triples or larger tuples from pairs,
permitting `a , b , c` to stand for `(a , (b , c))`.  But it conflicts with
other useful notations, such as `[_,_]` to construct a list of two elements in
Chapter [Lists]({{ site.baseurl }}/Lists/)
and `Γ , A` to extend environments in
Chapter [DeBruijn]({{ site.baseurl }}/DeBruijn/).
The standard library `_⇔_` is similar to ours, but the one in the
standard library is less convenient, since it is parameterised with
respect to an arbitrary notion of equivalence.


## Unicode

This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
