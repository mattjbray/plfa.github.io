---
src       : "src/plfa/Quantifiers.lagda.md"
title     : "Quantifiers: Universals and existentials"
layout    : page
prev      : /Negation/
permalink : /Quantifiers/
next      : /Decidable/
---

{% raw %}<pre class="Agda"><a id="159" class="Keyword">module</a> <a id="166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}" class="Module">plfa.Quantifiers</a> <a id="183" class="Keyword">where</a>
</pre>{% endraw %}
This chapter introduces universal and existential quantification.

## Imports

{% raw %}<pre class="Agda"><a id="277" class="Keyword">import</a> <a id="284" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="322" class="Symbol">as</a> <a id="325" class="Module">Eq</a>
<a id="328" class="Keyword">open</a> <a id="333" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="336" class="Keyword">using</a> <a id="342" class="Symbol">(</a><a id="343" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="346" class="Symbol">;</a> <a id="348" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="352" class="Symbol">)</a>
<a id="354" class="Keyword">open</a> <a id="359" class="Keyword">import</a> <a id="366" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="375" class="Keyword">using</a> <a id="381" class="Symbol">(</a><a id="382" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="383" class="Symbol">;</a> <a id="385" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="389" class="Symbol">;</a> <a id="391" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="394" class="Symbol">;</a> <a id="396" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="399" class="Symbol">;</a> <a id="401" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="404" class="Symbol">)</a>
<a id="406" class="Keyword">open</a> <a id="411" class="Keyword">import</a> <a id="418" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="435" class="Keyword">using</a> <a id="441" class="Symbol">(</a><a id="442" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="444" class="Symbol">)</a>
<a id="446" class="Keyword">open</a> <a id="451" class="Keyword">import</a> <a id="458" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="471" class="Keyword">using</a> <a id="477" class="Symbol">(</a><a id="478" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="481" class="Symbol">;</a> <a id="483" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="488" class="Symbol">)</a> <a id="490" class="Keyword">renaming</a> <a id="499" class="Symbol">(</a><a id="500" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="504" class="Symbol">to</a> <a id="507" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="512" class="Symbol">)</a>
<a id="514" class="Keyword">open</a> <a id="519" class="Keyword">import</a> <a id="526" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="535" class="Keyword">using</a> <a id="541" class="Symbol">(</a><a id="542" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="545" class="Symbol">)</a>
<a id="547" class="Keyword">open</a> <a id="552" class="Keyword">import</a> <a id="559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="576" class="Keyword">using</a> <a id="582" class="Symbol">(</a><a id="583" href="plfa.Isomorphism.html#3985" class="Record Operator">_≃_</a><a id="586" class="Symbol">;</a> <a id="588" href="plfa.Isomorphism.html#2678" class="Postulate">extensionality</a><a id="602" class="Symbol">)</a>
</pre>{% endraw %}

## Universals

We formalise universal quantification using the
dependent function type, which has appeared throughout this book.

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`∀ (x : A) → B x`.

Evidence that `∀ (x : A) → B x` holds is of the form

    λ (x : A) → N x

where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L
M` provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.

Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
{% raw %}<pre class="Agda"><a id="∀-elim"></a><a id="1724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#1724" class="Function">∀-elim</a> <a id="1731" class="Symbol">:</a> <a id="1733" class="Symbol">∀</a> <a id="1735" class="Symbol">{</a><a id="1736" href="plfa.Quantifiers.html#1736" class="Bound">A</a> <a id="1738" class="Symbol">:</a> <a id="1740" class="PrimitiveType">Set</a><a id="1743" class="Symbol">}</a> <a id="1745" class="Symbol">{</a><a id="1746" href="plfa.Quantifiers.html#1746" class="Bound">B</a> <a id="1748" class="Symbol">:</a> <a id="1750" href="plfa.Quantifiers.html#1736" class="Bound">A</a> <a id="1752" class="Symbol">→</a> <a id="1754" class="PrimitiveType">Set</a><a id="1757" class="Symbol">}</a>
  <a id="1761" class="Symbol">→</a> <a id="1763" class="Symbol">(</a><a id="1764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#1764" class="Bound">L</a> <a id="1766" class="Symbol">:</a> <a id="1768" class="Symbol">∀</a> <a id="1770" class="Symbol">(</a><a id="1771" href="plfa.Quantifiers.html#1771" class="Bound">x</a> <a id="1773" class="Symbol">:</a> <a id="1775" href="plfa.Quantifiers.html#1736" class="Bound">A</a><a id="1776" class="Symbol">)</a> <a id="1778" class="Symbol">→</a> <a id="1780" href="plfa.Quantifiers.html#1746" class="Bound">B</a> <a id="1782" href="plfa.Quantifiers.html#1771" class="Bound">x</a><a id="1783" class="Symbol">)</a>
  <a id="1787" class="Symbol">→</a> <a id="1789" class="Symbol">(</a><a id="1790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#1790" class="Bound">M</a> <a id="1792" class="Symbol">:</a> <a id="1794" href="plfa.Quantifiers.html#1736" class="Bound">A</a><a id="1795" class="Symbol">)</a>
    <a id="1801" class="Comment">-----------------</a>
  <a id="1821" class="Symbol">→</a> <a id="1823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#1746" class="Bound">B</a> <a id="1825" href="plfa.Quantifiers.html#1790" class="Bound">M</a>
<a id="1827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#1724" class="Function">∀-elim</a> <a id="1834" href="plfa.Quantifiers.html#1834" class="Bound">L</a> <a id="1836" href="plfa.Quantifiers.html#1836" class="Bound">M</a> <a id="1838" class="Symbol">=</a> <a id="1840" href="plfa.Quantifiers.html#1834" class="Bound">L</a> <a id="1842" href="plfa.Quantifiers.html#1836" class="Bound">M</a>
</pre>{% endraw %}As with `→-elim`, the rule corresponds to function application.

Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.

Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
{% raw %}<pre class="Agda"><a id="3106" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="3118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#3118" class="Postulate">∀-distrib-×</a> <a id="3130" class="Symbol">:</a> <a id="3132" class="Symbol">∀</a> <a id="3134" class="Symbol">{</a><a id="3135" href="plfa.Quantifiers.html#3135" class="Bound">A</a> <a id="3137" class="Symbol">:</a> <a id="3139" class="PrimitiveType">Set</a><a id="3142" class="Symbol">}</a> <a id="3144" class="Symbol">{</a><a id="3145" href="plfa.Quantifiers.html#3145" class="Bound">B</a> <a id="3147" href="plfa.Quantifiers.html#3147" class="Bound">C</a> <a id="3149" class="Symbol">:</a> <a id="3151" href="plfa.Quantifiers.html#3135" class="Bound">A</a> <a id="3153" class="Symbol">→</a> <a id="3155" class="PrimitiveType">Set</a><a id="3158" class="Symbol">}</a> <a id="3160" class="Symbol">→</a>
    <a id="3166" class="Symbol">(∀</a> <a id="3169" class="Symbol">(</a><a id="3170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#3170" class="Bound">x</a> <a id="3172" class="Symbol">:</a> <a id="3174" href="plfa.Quantifiers.html#3135" class="Bound">A</a><a id="3175" class="Symbol">)</a> <a id="3177" class="Symbol">→</a> <a id="3179" href="plfa.Quantifiers.html#3145" class="Bound">B</a> <a id="3181" href="plfa.Quantifiers.html#3170" class="Bound">x</a> <a id="3183" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3185" href="plfa.Quantifiers.html#3147" class="Bound">C</a> <a id="3187" href="plfa.Quantifiers.html#3170" class="Bound">x</a><a id="3188" class="Symbol">)</a> <a id="3190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="3192" class="Symbol">(∀</a> <a id="3195" class="Symbol">(</a><a id="3196" href="plfa.Quantifiers.html#3196" class="Bound">x</a> <a id="3198" class="Symbol">:</a> <a id="3200" href="plfa.Quantifiers.html#3135" class="Bound">A</a><a id="3201" class="Symbol">)</a> <a id="3203" class="Symbol">→</a> <a id="3205" href="plfa.Quantifiers.html#3145" class="Bound">B</a> <a id="3207" href="plfa.Quantifiers.html#3196" class="Bound">x</a><a id="3208" class="Symbol">)</a> <a id="3210" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3212" class="Symbol">(∀</a> <a id="3215" class="Symbol">(</a><a id="3216" href="plfa.Quantifiers.html#3216" class="Bound">x</a> <a id="3218" class="Symbol">:</a> <a id="3220" href="plfa.Quantifiers.html#3135" class="Bound">A</a><a id="3221" class="Symbol">)</a> <a id="3223" class="Symbol">→</a> <a id="3225" href="plfa.Quantifiers.html#3147" class="Bound">C</a> <a id="3227" href="plfa.Quantifiers.html#3216" class="Bound">x</a><a id="3228" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives]({{ site.baseurl }}/Connectives/).

#### Exercise `⊎∀-implies-∀⊎`

Show that a disjunction of universals implies a universal of disjunctions:
{% raw %}<pre class="Agda"><a id="3449" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="3461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#3461" class="Postulate">⊎∀-implies-∀⊎</a> <a id="3475" class="Symbol">:</a> <a id="3477" class="Symbol">∀</a> <a id="3479" class="Symbol">{</a><a id="3480" href="plfa.Quantifiers.html#3480" class="Bound">A</a> <a id="3482" class="Symbol">:</a> <a id="3484" class="PrimitiveType">Set</a><a id="3487" class="Symbol">}</a> <a id="3489" class="Symbol">{</a><a id="3490" href="plfa.Quantifiers.html#3490" class="Bound">B</a> <a id="3492" href="plfa.Quantifiers.html#3492" class="Bound">C</a> <a id="3494" class="Symbol">:</a> <a id="3496" href="plfa.Quantifiers.html#3480" class="Bound">A</a> <a id="3498" class="Symbol">→</a> <a id="3500" class="PrimitiveType">Set</a><a id="3503" class="Symbol">}</a> <a id="3505" class="Symbol">→</a>
    <a id="3511" class="Symbol">(∀</a> <a id="3514" class="Symbol">(</a><a id="3515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#3515" class="Bound">x</a> <a id="3517" class="Symbol">:</a> <a id="3519" href="plfa.Quantifiers.html#3480" class="Bound">A</a><a id="3520" class="Symbol">)</a> <a id="3522" class="Symbol">→</a> <a id="3524" href="plfa.Quantifiers.html#3490" class="Bound">B</a> <a id="3526" href="plfa.Quantifiers.html#3515" class="Bound">x</a><a id="3527" class="Symbol">)</a> <a id="3529" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3531" class="Symbol">(∀</a> <a id="3534" class="Symbol">(</a><a id="3535" href="plfa.Quantifiers.html#3535" class="Bound">x</a> <a id="3537" class="Symbol">:</a> <a id="3539" href="plfa.Quantifiers.html#3480" class="Bound">A</a><a id="3540" class="Symbol">)</a> <a id="3542" class="Symbol">→</a> <a id="3544" href="plfa.Quantifiers.html#3492" class="Bound">C</a> <a id="3546" href="plfa.Quantifiers.html#3535" class="Bound">x</a><a id="3547" class="Symbol">)</a>  <a id="3550" class="Symbol">→</a>  <a id="3553" class="Symbol">∀</a> <a id="3555" class="Symbol">(</a><a id="3556" href="plfa.Quantifiers.html#3556" class="Bound">x</a> <a id="3558" class="Symbol">:</a> <a id="3560" href="plfa.Quantifiers.html#3480" class="Bound">A</a><a id="3561" class="Symbol">)</a> <a id="3563" class="Symbol">→</a> <a id="3565" href="plfa.Quantifiers.html#3490" class="Bound">B</a> <a id="3567" href="plfa.Quantifiers.html#3556" class="Bound">x</a> <a id="3569" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3571" href="plfa.Quantifiers.html#3492" class="Bound">C</a> <a id="3573" href="plfa.Quantifiers.html#3556" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×`

Consider the following type.
{% raw %}<pre class="Agda"><a id="3694" class="Keyword">data</a> <a id="Tri"></a><a id="3699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#3699" class="Datatype">Tri</a> <a id="3703" class="Symbol">:</a> <a id="3705" class="PrimitiveType">Set</a> <a id="3709" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="3717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#3717" class="InductiveConstructor">aa</a> <a id="3720" class="Symbol">:</a> <a id="3722" href="plfa.Quantifiers.html#3699" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="3728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#3728" class="InductiveConstructor">bb</a> <a id="3731" class="Symbol">:</a> <a id="3733" href="plfa.Quantifiers.html#3699" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="3739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#3739" class="InductiveConstructor">cc</a> <a id="3742" class="Symbol">:</a> <a id="3744" href="plfa.Quantifiers.html#3699" class="Datatype">Tri</a>
</pre>{% endraw %}Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.


## Existentials

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.

We formalise existential quantification by declaring a suitable
inductive type:
{% raw %}<pre class="Agda"><a id="4370" class="Keyword">data</a> <a id="Σ"></a><a id="4375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4375" class="Datatype">Σ</a> <a id="4377" class="Symbol">(</a><a id="4378" href="plfa.Quantifiers.html#4378" class="Bound">A</a> <a id="4380" class="Symbol">:</a> <a id="4382" class="PrimitiveType">Set</a><a id="4385" class="Symbol">)</a> <a id="4387" class="Symbol">(</a><a id="4388" href="plfa.Quantifiers.html#4388" class="Bound">B</a> <a id="4390" class="Symbol">:</a> <a id="4392" href="plfa.Quantifiers.html#4378" class="Bound">A</a> <a id="4394" class="Symbol">→</a> <a id="4396" class="PrimitiveType">Set</a><a id="4399" class="Symbol">)</a> <a id="4401" class="Symbol">:</a> <a id="4403" class="PrimitiveType">Set</a> <a id="4407" class="Keyword">where</a>
  <a id="Σ.⟨_,_⟩"></a><a id="4415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4415" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="4421" class="Symbol">:</a> <a id="4423" class="Symbol">(</a><a id="4424" href="plfa.Quantifiers.html#4424" class="Bound">x</a> <a id="4426" class="Symbol">:</a> <a id="4428" href="plfa.Quantifiers.html#4378" class="Bound">A</a><a id="4429" class="Symbol">)</a> <a id="4431" class="Symbol">→</a> <a id="4433" href="plfa.Quantifiers.html#4388" class="Bound">B</a> <a id="4435" href="plfa.Quantifiers.html#4424" class="Bound">x</a> <a id="4437" class="Symbol">→</a> <a id="4439" href="plfa.Quantifiers.html#4375" class="Datatype">Σ</a> <a id="4441" href="plfa.Quantifiers.html#4378" class="Bound">A</a> <a id="4443" href="plfa.Quantifiers.html#4388" class="Bound">B</a>
</pre>{% endraw %}We define a convenient syntax for existentials as follows:
{% raw %}<pre class="Agda"><a id="Σ-syntax"></a><a id="4512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4512" class="Function">Σ-syntax</a> <a id="4521" class="Symbol">=</a> <a id="4523" href="plfa.Quantifiers.html#4375" class="Datatype">Σ</a>
<a id="4525" class="Keyword">infix</a> <a id="4531" class="Number">2</a> <a id="4533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4512" class="Function">Σ-syntax</a>
<a id="4542" class="Keyword">syntax</a> <a id="4549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4512" class="Function">Σ-syntax</a> <a id="4558" class="Bound">A</a> <a id="4560" class="Symbol">(λ</a> <a id="4563" class="Bound">x</a> <a id="4565" class="Symbol">→</a> <a id="4567" class="Bound">B</a><a id="4568" class="Symbol">)</a> <a id="4570" class="Symbol">=</a> <a id="4572" class="Function">Σ[</a> <a id="4575" class="Bound">x</a> <a id="4577" class="Function">∈</a> <a id="4579" class="Bound">A</a> <a id="4581" class="Function">]</a> <a id="4583" class="Bound">B</a>
</pre>{% endraw %}This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.

Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Equivalently, we could also declare existentials as a record type:
{% raw %}<pre class="Agda"><a id="5012" class="Keyword">record</a> <a id="Σ′"></a><a id="5019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5019" class="Record">Σ′</a> <a id="5022" class="Symbol">(</a><a id="5023" href="plfa.Quantifiers.html#5023" class="Bound">A</a> <a id="5025" class="Symbol">:</a> <a id="5027" class="PrimitiveType">Set</a><a id="5030" class="Symbol">)</a> <a id="5032" class="Symbol">(</a><a id="5033" href="plfa.Quantifiers.html#5033" class="Bound">B</a> <a id="5035" class="Symbol">:</a> <a id="5037" href="plfa.Quantifiers.html#5023" class="Bound">A</a> <a id="5039" class="Symbol">→</a> <a id="5041" class="PrimitiveType">Set</a><a id="5044" class="Symbol">)</a> <a id="5046" class="Symbol">:</a> <a id="5048" class="PrimitiveType">Set</a> <a id="5052" class="Keyword">where</a>
  <a id="5060" class="Keyword">field</a>
    <a id="Σ′.proj₁′"></a><a id="5070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5070" class="Field">proj₁′</a> <a id="5077" class="Symbol">:</a> <a id="5079" href="plfa.Quantifiers.html#5023" class="Bound">A</a>
    <a id="Σ′.proj₂′"></a><a id="5085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5085" class="Field">proj₂′</a> <a id="5092" class="Symbol">:</a> <a id="5094" href="plfa.Quantifiers.html#5033" class="Bound">B</a> <a id="5096" href="plfa.Quantifiers.html#5070" class="Field">proj₁′</a>
</pre>{% endraw %}Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B M`.

Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.

Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.

Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.

A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
{% raw %}<pre class="Agda"><a id="∃"></a><a id="6743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6743" class="Function">∃</a> <a id="6745" class="Symbol">:</a> <a id="6747" class="Symbol">∀</a> <a id="6749" class="Symbol">{</a><a id="6750" href="plfa.Quantifiers.html#6750" class="Bound">A</a> <a id="6752" class="Symbol">:</a> <a id="6754" class="PrimitiveType">Set</a><a id="6757" class="Symbol">}</a> <a id="6759" class="Symbol">(</a><a id="6760" href="plfa.Quantifiers.html#6760" class="Bound">B</a> <a id="6762" class="Symbol">:</a> <a id="6764" href="plfa.Quantifiers.html#6750" class="Bound">A</a> <a id="6766" class="Symbol">→</a> <a id="6768" class="PrimitiveType">Set</a><a id="6771" class="Symbol">)</a> <a id="6773" class="Symbol">→</a> <a id="6775" class="PrimitiveType">Set</a>
<a id="6779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6743" class="Function">∃</a> <a id="6781" class="Symbol">{</a><a id="6782" href="plfa.Quantifiers.html#6782" class="Bound">A</a><a id="6783" class="Symbol">}</a> <a id="6785" href="plfa.Quantifiers.html#6785" class="Bound">B</a> <a id="6787" class="Symbol">=</a> <a id="6789" href="plfa.Quantifiers.html#4375" class="Datatype">Σ</a> <a id="6791" href="plfa.Quantifiers.html#6782" class="Bound">A</a> <a id="6793" href="plfa.Quantifiers.html#6785" class="Bound">B</a>

<a id="∃-syntax"></a><a id="6796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6796" class="Function">∃-syntax</a> <a id="6805" class="Symbol">=</a> <a id="6807" href="plfa.Quantifiers.html#6743" class="Function">∃</a>
<a id="6809" class="Keyword">syntax</a> <a id="6816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6796" class="Function">∃-syntax</a> <a id="6825" class="Symbol">(λ</a> <a id="6828" class="Bound">x</a> <a id="6830" class="Symbol">→</a> <a id="6832" class="Bound">B</a><a id="6833" class="Symbol">)</a> <a id="6835" class="Symbol">=</a> <a id="6837" class="Function">∃[</a> <a id="6840" class="Bound">x</a> <a id="6842" class="Function">]</a> <a id="6844" class="Bound">B</a>
</pre>{% endraw %}The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
{% raw %}<pre class="Agda"><a id="∃-elim"></a><a id="7178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7178" class="Function">∃-elim</a> <a id="7185" class="Symbol">:</a> <a id="7187" class="Symbol">∀</a> <a id="7189" class="Symbol">{</a><a id="7190" href="plfa.Quantifiers.html#7190" class="Bound">A</a> <a id="7192" class="Symbol">:</a> <a id="7194" class="PrimitiveType">Set</a><a id="7197" class="Symbol">}</a> <a id="7199" class="Symbol">{</a><a id="7200" href="plfa.Quantifiers.html#7200" class="Bound">B</a> <a id="7202" class="Symbol">:</a> <a id="7204" href="plfa.Quantifiers.html#7190" class="Bound">A</a> <a id="7206" class="Symbol">→</a> <a id="7208" class="PrimitiveType">Set</a><a id="7211" class="Symbol">}</a> <a id="7213" class="Symbol">{</a><a id="7214" href="plfa.Quantifiers.html#7214" class="Bound">C</a> <a id="7216" class="Symbol">:</a> <a id="7218" class="PrimitiveType">Set</a><a id="7221" class="Symbol">}</a>
  <a id="7225" class="Symbol">→</a> <a id="7227" class="Symbol">(∀</a> <a id="7230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7230" class="Bound">x</a> <a id="7232" class="Symbol">→</a> <a id="7234" href="plfa.Quantifiers.html#7200" class="Bound">B</a> <a id="7236" href="plfa.Quantifiers.html#7230" class="Bound">x</a> <a id="7238" class="Symbol">→</a> <a id="7240" href="plfa.Quantifiers.html#7214" class="Bound">C</a><a id="7241" class="Symbol">)</a>
  <a id="7245" class="Symbol">→</a> <a id="7247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6796" class="Function">∃[</a> <a id="7250" href="plfa.Quantifiers.html#7250" class="Bound">x</a> <a id="7252" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="7254" href="plfa.Quantifiers.html#7200" class="Bound">B</a> <a id="7256" href="plfa.Quantifiers.html#7250" class="Bound">x</a>
    <a id="7262" class="Comment">---------------</a>
  <a id="7280" class="Symbol">→</a> <a id="7282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7214" class="Bound">C</a>
<a id="7284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7178" class="Function">∃-elim</a> <a id="7291" href="plfa.Quantifiers.html#7291" class="Bound">f</a> <a id="7293" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="7295" href="plfa.Quantifiers.html#7295" class="Bound">x</a> <a id="7297" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="7299" href="plfa.Quantifiers.html#7299" class="Bound">y</a> <a id="7301" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a> <a id="7303" class="Symbol">=</a> <a id="7305" href="plfa.Quantifiers.html#7291" class="Bound">f</a> <a id="7307" href="plfa.Quantifiers.html#7295" class="Bound">x</a> <a id="7309" href="plfa.Quantifiers.html#7299" class="Bound">y</a>
</pre>{% endraw %}In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism:
{% raw %}<pre class="Agda"><a id="∀∃-currying"></a><a id="7759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7759" class="Function">∀∃-currying</a> <a id="7771" class="Symbol">:</a> <a id="7773" class="Symbol">∀</a> <a id="7775" class="Symbol">{</a><a id="7776" href="plfa.Quantifiers.html#7776" class="Bound">A</a> <a id="7778" class="Symbol">:</a> <a id="7780" class="PrimitiveType">Set</a><a id="7783" class="Symbol">}</a> <a id="7785" class="Symbol">{</a><a id="7786" href="plfa.Quantifiers.html#7786" class="Bound">B</a> <a id="7788" class="Symbol">:</a> <a id="7790" href="plfa.Quantifiers.html#7776" class="Bound">A</a> <a id="7792" class="Symbol">→</a> <a id="7794" class="PrimitiveType">Set</a><a id="7797" class="Symbol">}</a> <a id="7799" class="Symbol">{</a><a id="7800" href="plfa.Quantifiers.html#7800" class="Bound">C</a> <a id="7802" class="Symbol">:</a> <a id="7804" class="PrimitiveType">Set</a><a id="7807" class="Symbol">}</a>
  <a id="7811" class="Symbol">→</a> <a id="7813" class="Symbol">(∀</a> <a id="7816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7816" class="Bound">x</a> <a id="7818" class="Symbol">→</a> <a id="7820" href="plfa.Quantifiers.html#7786" class="Bound">B</a> <a id="7822" href="plfa.Quantifiers.html#7816" class="Bound">x</a> <a id="7824" class="Symbol">→</a> <a id="7826" href="plfa.Quantifiers.html#7800" class="Bound">C</a><a id="7827" class="Symbol">)</a> <a id="7829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="7831" class="Symbol">(</a><a id="7832" href="plfa.Quantifiers.html#6796" class="Function">∃[</a> <a id="7835" href="plfa.Quantifiers.html#7835" class="Bound">x</a> <a id="7837" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="7839" href="plfa.Quantifiers.html#7786" class="Bound">B</a> <a id="7841" href="plfa.Quantifiers.html#7835" class="Bound">x</a> <a id="7843" class="Symbol">→</a> <a id="7845" href="plfa.Quantifiers.html#7800" class="Bound">C</a><a id="7846" class="Symbol">)</a>
<a id="7848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7759" class="Function">∀∃-currying</a> <a id="7860" class="Symbol">=</a>
  <a id="7864" class="Keyword">record</a>
    <a id="7875" class="Symbol">{</a> <a id="7877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4025" class="Field">to</a>      <a id="7885" class="Symbol">=</a>  <a id="7888" class="Symbol">λ{</a> <a id="7891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7891" class="Bound">f</a> <a id="7893" class="Symbol">→</a> <a id="7895" class="Symbol">λ{</a> <a id="7898" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="7900" href="plfa.Quantifiers.html#7900" class="Bound">x</a> <a id="7902" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="7904" href="plfa.Quantifiers.html#7904" class="Bound">y</a> <a id="7906" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a> <a id="7908" class="Symbol">→</a> <a id="7910" href="plfa.Quantifiers.html#7891" class="Bound">f</a> <a id="7912" href="plfa.Quantifiers.html#7900" class="Bound">x</a> <a id="7914" href="plfa.Quantifiers.html#7904" class="Bound">y</a> <a id="7916" class="Symbol">}}</a>
    <a id="7923" class="Symbol">;</a> <a id="7925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4042" class="Field">from</a>    <a id="7933" class="Symbol">=</a>  <a id="7936" class="Symbol">λ{</a> <a id="7939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7939" class="Bound">g</a> <a id="7941" class="Symbol">→</a> <a id="7943" class="Symbol">λ{</a> <a id="7946" href="plfa.Quantifiers.html#7946" class="Bound">x</a> <a id="7948" class="Symbol">→</a> <a id="7950" class="Symbol">λ{</a> <a id="7953" href="plfa.Quantifiers.html#7953" class="Bound">y</a> <a id="7955" class="Symbol">→</a> <a id="7957" href="plfa.Quantifiers.html#7939" class="Bound">g</a> <a id="7959" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="7961" href="plfa.Quantifiers.html#7946" class="Bound">x</a> <a id="7963" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="7965" href="plfa.Quantifiers.html#7953" class="Bound">y</a> <a id="7967" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a> <a id="7969" class="Symbol">}}}</a>
    <a id="7977" class="Symbol">;</a> <a id="7979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4059" class="Field">from∘to</a> <a id="7987" class="Symbol">=</a>  <a id="7990" class="Symbol">λ{</a> <a id="7993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7993" class="Bound">f</a> <a id="7995" class="Symbol">→</a> <a id="7997" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8002" class="Symbol">}</a>
    <a id="8008" class="Symbol">;</a> <a id="8010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4101" class="Field">to∘from</a> <a id="8018" class="Symbol">=</a>  <a id="8021" class="Symbol">λ{</a> <a id="8024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#8024" class="Bound">g</a> <a id="8026" class="Symbol">→</a> <a id="8028" href="plfa.Isomorphism.html#2678" class="Postulate">extensionality</a> <a id="8043" class="Symbol">λ{</a> <a id="8046" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="8048" href="plfa.Quantifiers.html#8048" class="Bound">x</a> <a id="8050" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="8052" href="plfa.Quantifiers.html#8052" class="Bound">y</a> <a id="8054" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a> <a id="8056" class="Symbol">→</a> <a id="8058" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8063" class="Symbol">}}</a>
    <a id="8070" class="Symbol">}</a>
</pre>{% endraw %}The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication]({{ site.baseurl }}/Connectives/#implication).

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
{% raw %}<pre class="Agda"><a id="8387" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="8399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#8399" class="Postulate">∃-distrib-⊎</a> <a id="8411" class="Symbol">:</a> <a id="8413" class="Symbol">∀</a> <a id="8415" class="Symbol">{</a><a id="8416" href="plfa.Quantifiers.html#8416" class="Bound">A</a> <a id="8418" class="Symbol">:</a> <a id="8420" class="PrimitiveType">Set</a><a id="8423" class="Symbol">}</a> <a id="8425" class="Symbol">{</a><a id="8426" href="plfa.Quantifiers.html#8426" class="Bound">B</a> <a id="8428" href="plfa.Quantifiers.html#8428" class="Bound">C</a> <a id="8430" class="Symbol">:</a> <a id="8432" href="plfa.Quantifiers.html#8416" class="Bound">A</a> <a id="8434" class="Symbol">→</a> <a id="8436" class="PrimitiveType">Set</a><a id="8439" class="Symbol">}</a> <a id="8441" class="Symbol">→</a>
    <a id="8447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6796" class="Function">∃[</a> <a id="8450" href="plfa.Quantifiers.html#8450" class="Bound">x</a> <a id="8452" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="8454" class="Symbol">(</a><a id="8455" href="plfa.Quantifiers.html#8426" class="Bound">B</a> <a id="8457" href="plfa.Quantifiers.html#8450" class="Bound">x</a> <a id="8459" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8461" href="plfa.Quantifiers.html#8428" class="Bound">C</a> <a id="8463" href="plfa.Quantifiers.html#8450" class="Bound">x</a><a id="8464" class="Symbol">)</a> <a id="8466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="8468" class="Symbol">(</a><a id="8469" href="plfa.Quantifiers.html#6796" class="Function">∃[</a> <a id="8472" href="plfa.Quantifiers.html#8472" class="Bound">x</a> <a id="8474" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="8476" href="plfa.Quantifiers.html#8426" class="Bound">B</a> <a id="8478" href="plfa.Quantifiers.html#8472" class="Bound">x</a><a id="8479" class="Symbol">)</a> <a id="8481" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="8483" class="Symbol">(</a><a id="8484" href="plfa.Quantifiers.html#6796" class="Function">∃[</a> <a id="8487" href="plfa.Quantifiers.html#8487" class="Bound">x</a> <a id="8489" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="8491" href="plfa.Quantifiers.html#8428" class="Bound">C</a> <a id="8493" href="plfa.Quantifiers.html#8487" class="Bound">x</a><a id="8494" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `∃×-implies-×∃`

Show that an existential of conjunctions implies a conjunction of existentials:
{% raw %}<pre class="Agda"><a id="8616" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="8628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#8628" class="Postulate">∃×-implies-×∃</a> <a id="8642" class="Symbol">:</a> <a id="8644" class="Symbol">∀</a> <a id="8646" class="Symbol">{</a><a id="8647" href="plfa.Quantifiers.html#8647" class="Bound">A</a> <a id="8649" class="Symbol">:</a> <a id="8651" class="PrimitiveType">Set</a><a id="8654" class="Symbol">}</a> <a id="8656" class="Symbol">{</a><a id="8657" href="plfa.Quantifiers.html#8657" class="Bound">B</a> <a id="8659" href="plfa.Quantifiers.html#8659" class="Bound">C</a> <a id="8661" class="Symbol">:</a> <a id="8663" href="plfa.Quantifiers.html#8647" class="Bound">A</a> <a id="8665" class="Symbol">→</a> <a id="8667" class="PrimitiveType">Set</a><a id="8670" class="Symbol">}</a> <a id="8672" class="Symbol">→</a>
    <a id="8678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6796" class="Function">∃[</a> <a id="8681" href="plfa.Quantifiers.html#8681" class="Bound">x</a> <a id="8683" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="8685" class="Symbol">(</a><a id="8686" href="plfa.Quantifiers.html#8657" class="Bound">B</a> <a id="8688" href="plfa.Quantifiers.html#8681" class="Bound">x</a> <a id="8690" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="8692" href="plfa.Quantifiers.html#8659" class="Bound">C</a> <a id="8694" href="plfa.Quantifiers.html#8681" class="Bound">x</a><a id="8695" class="Symbol">)</a> <a id="8697" class="Symbol">→</a> <a id="8699" class="Symbol">(</a><a id="8700" href="plfa.Quantifiers.html#6796" class="Function">∃[</a> <a id="8703" href="plfa.Quantifiers.html#8703" class="Bound">x</a> <a id="8705" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="8707" href="plfa.Quantifiers.html#8657" class="Bound">B</a> <a id="8709" href="plfa.Quantifiers.html#8703" class="Bound">x</a><a id="8710" class="Symbol">)</a> <a id="8712" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="8714" class="Symbol">(</a><a id="8715" href="plfa.Quantifiers.html#6796" class="Function">∃[</a> <a id="8718" href="plfa.Quantifiers.html#8718" class="Bound">x</a> <a id="8720" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="8722" href="plfa.Quantifiers.html#8659" class="Bound">C</a> <a id="8724" href="plfa.Quantifiers.html#8718" class="Bound">x</a><a id="8725" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-⊎`

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.


## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations]({{ site.baseurl }}/Relations/):
{% raw %}<pre class="Agda"><a id="9050" class="Keyword">data</a> <a id="even"></a><a id="9055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9055" class="Datatype">even</a> <a id="9060" class="Symbol">:</a> <a id="9062" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="9064" class="Symbol">→</a> <a id="9066" class="PrimitiveType">Set</a>
<a id="9070" class="Keyword">data</a> <a id="odd"></a><a id="9075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9075" class="Datatype">odd</a>  <a id="9080" class="Symbol">:</a> <a id="9082" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="9084" class="Symbol">→</a> <a id="9086" class="PrimitiveType">Set</a>

<a id="9091" class="Keyword">data</a> <a id="9096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9055" class="Datatype">even</a> <a id="9101" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="9110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9110" class="InductiveConstructor">even-zero</a> <a id="9120" class="Symbol">:</a> <a id="9122" href="plfa.Quantifiers.html#9055" class="Datatype">even</a> <a id="9127" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="9135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9135" class="InductiveConstructor">even-suc</a> <a id="9144" class="Symbol">:</a> <a id="9146" class="Symbol">∀</a> <a id="9148" class="Symbol">{</a><a id="9149" href="plfa.Quantifiers.html#9149" class="Bound">n</a> <a id="9151" class="Symbol">:</a> <a id="9153" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9154" class="Symbol">}</a>
    <a id="9160" class="Symbol">→</a> <a id="9162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9075" class="Datatype">odd</a> <a id="9166" href="plfa.Quantifiers.html#9149" class="Bound">n</a>
      <a id="9174" class="Comment">------------</a>
    <a id="9191" class="Symbol">→</a> <a id="9193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9055" class="Datatype">even</a> <a id="9198" class="Symbol">(</a><a id="9199" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9203" href="plfa.Quantifiers.html#9149" class="Bound">n</a><a id="9204" class="Symbol">)</a>

<a id="9207" class="Keyword">data</a> <a id="9212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9075" class="Datatype">odd</a> <a id="9216" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="9224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9224" class="InductiveConstructor">odd-suc</a> <a id="9232" class="Symbol">:</a> <a id="9234" class="Symbol">∀</a> <a id="9236" class="Symbol">{</a><a id="9237" href="plfa.Quantifiers.html#9237" class="Bound">n</a> <a id="9239" class="Symbol">:</a> <a id="9241" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9242" class="Symbol">}</a>
    <a id="9248" class="Symbol">→</a> <a id="9250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9055" class="Datatype">even</a> <a id="9255" href="plfa.Quantifiers.html#9237" class="Bound">n</a>
      <a id="9263" class="Comment">-----------</a>
    <a id="9279" class="Symbol">→</a> <a id="9281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9075" class="Datatype">odd</a> <a id="9285" class="Symbol">(</a><a id="9286" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="9290" href="plfa.Quantifiers.html#9237" class="Bound">n</a><a id="9291" class="Symbol">)</a>
</pre>{% endraw %}A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.

We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:

`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`

By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.

Here is the proof in the forward direction:
{% raw %}<pre class="Agda"><a id="even-∃"></a><a id="9912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9912" class="Function">even-∃</a> <a id="9919" class="Symbol">:</a> <a id="9921" class="Symbol">∀</a> <a id="9923" class="Symbol">{</a><a id="9924" href="plfa.Quantifiers.html#9924" class="Bound">n</a> <a id="9926" class="Symbol">:</a> <a id="9928" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9929" class="Symbol">}</a> <a id="9931" class="Symbol">→</a> <a id="9933" href="plfa.Quantifiers.html#9055" class="Datatype">even</a> <a id="9938" href="plfa.Quantifiers.html#9924" class="Bound">n</a> <a id="9940" class="Symbol">→</a> <a id="9942" href="plfa.Quantifiers.html#6796" class="Function">∃[</a> <a id="9945" href="plfa.Quantifiers.html#9945" class="Bound">m</a> <a id="9947" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="9949" class="Symbol">(</a>    <a id="9954" href="plfa.Quantifiers.html#9945" class="Bound">m</a> <a id="9956" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="9958" class="Number">2</a> <a id="9960" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9962" href="plfa.Quantifiers.html#9924" class="Bound">n</a><a id="9963" class="Symbol">)</a>
<a id="odd-∃"></a><a id="9965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9965" class="Function">odd-∃</a>  <a id="9972" class="Symbol">:</a> <a id="9974" class="Symbol">∀</a> <a id="9976" class="Symbol">{</a><a id="9977" href="plfa.Quantifiers.html#9977" class="Bound">n</a> <a id="9979" class="Symbol">:</a> <a id="9981" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="9982" class="Symbol">}</a> <a id="9984" class="Symbol">→</a>  <a id="9987" href="plfa.Quantifiers.html#9075" class="Datatype">odd</a> <a id="9991" href="plfa.Quantifiers.html#9977" class="Bound">n</a> <a id="9993" class="Symbol">→</a> <a id="9995" href="plfa.Quantifiers.html#6796" class="Function">∃[</a> <a id="9998" href="plfa.Quantifiers.html#9998" class="Bound">m</a> <a id="10000" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="10002" class="Symbol">(</a><a id="10003" class="Number">1</a> <a id="10005" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="10007" href="plfa.Quantifiers.html#9998" class="Bound">m</a> <a id="10009" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="10011" class="Number">2</a> <a id="10013" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10015" href="plfa.Quantifiers.html#9977" class="Bound">n</a><a id="10016" class="Symbol">)</a>

<a id="10019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9912" class="Function">even-∃</a> <a id="10026" href="plfa.Quantifiers.html#9110" class="InductiveConstructor">even-zero</a>                       <a id="10058" class="Symbol">=</a>  <a id="10061" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="10063" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="10068" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="10070" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10075" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a>
<a id="10077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9912" class="Function">even-∃</a> <a id="10084" class="Symbol">(</a><a id="10085" href="plfa.Quantifiers.html#9135" class="InductiveConstructor">even-suc</a> <a id="10094" href="plfa.Quantifiers.html#10094" class="Bound">o</a><a id="10095" class="Symbol">)</a> <a id="10097" class="Keyword">with</a> <a id="10102" href="plfa.Quantifiers.html#9965" class="Function">odd-∃</a> <a id="10108" href="plfa.Quantifiers.html#10094" class="Bound">o</a>
<a id="10110" class="Symbol">...</a>                    <a id="10133" class="Symbol">|</a> <a id="10135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4415" class="InductiveConstructor Operator">⟨</a> <a id="10137" href="plfa.Quantifiers.html#10137" class="Bound">m</a> <a id="10139" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="10141" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10146" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a>  <a id="10149" class="Symbol">=</a>  <a id="10152" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="10154" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10158" href="plfa.Quantifiers.html#10137" class="Bound">m</a> <a id="10160" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="10162" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10167" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a>

<a id="10170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9965" class="Function">odd-∃</a>  <a id="10177" class="Symbol">(</a><a id="10178" href="plfa.Quantifiers.html#9224" class="InductiveConstructor">odd-suc</a> <a id="10186" href="plfa.Quantifiers.html#10186" class="Bound">e</a><a id="10187" class="Symbol">)</a>  <a id="10190" class="Keyword">with</a> <a id="10195" href="plfa.Quantifiers.html#9912" class="Function">even-∃</a> <a id="10202" href="plfa.Quantifiers.html#10186" class="Bound">e</a>
<a id="10204" class="Symbol">...</a>                    <a id="10227" class="Symbol">|</a> <a id="10229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4415" class="InductiveConstructor Operator">⟨</a> <a id="10231" href="plfa.Quantifiers.html#10231" class="Bound">m</a> <a id="10233" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="10235" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10240" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a>  <a id="10243" class="Symbol">=</a>  <a id="10246" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="10248" href="plfa.Quantifiers.html#10231" class="Bound">m</a> <a id="10250" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="10252" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="10257" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a>
</pre>{% endraw %}We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:

* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

This completes the proof in the forward direction.

Here is the proof in the reverse direction:
{% raw %}<pre class="Agda"><a id="∃-even"></a><a id="11277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11277" class="Function">∃-even</a> <a id="11284" class="Symbol">:</a> <a id="11286" class="Symbol">∀</a> <a id="11288" class="Symbol">{</a><a id="11289" href="plfa.Quantifiers.html#11289" class="Bound">n</a> <a id="11291" class="Symbol">:</a> <a id="11293" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11294" class="Symbol">}</a> <a id="11296" class="Symbol">→</a> <a id="11298" href="plfa.Quantifiers.html#6796" class="Function">∃[</a> <a id="11301" href="plfa.Quantifiers.html#11301" class="Bound">m</a> <a id="11303" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="11305" class="Symbol">(</a>    <a id="11310" href="plfa.Quantifiers.html#11301" class="Bound">m</a> <a id="11312" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="11314" class="Number">2</a> <a id="11316" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11318" href="plfa.Quantifiers.html#11289" class="Bound">n</a><a id="11319" class="Symbol">)</a> <a id="11321" class="Symbol">→</a> <a id="11323" href="plfa.Quantifiers.html#9055" class="Datatype">even</a> <a id="11328" href="plfa.Quantifiers.html#11289" class="Bound">n</a>
<a id="∃-odd"></a><a id="11330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11330" class="Function">∃-odd</a>  <a id="11337" class="Symbol">:</a> <a id="11339" class="Symbol">∀</a> <a id="11341" class="Symbol">{</a><a id="11342" href="plfa.Quantifiers.html#11342" class="Bound">n</a> <a id="11344" class="Symbol">:</a> <a id="11346" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11347" class="Symbol">}</a> <a id="11349" class="Symbol">→</a> <a id="11351" href="plfa.Quantifiers.html#6796" class="Function">∃[</a> <a id="11354" href="plfa.Quantifiers.html#11354" class="Bound">m</a> <a id="11356" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="11358" class="Symbol">(</a><a id="11359" class="Number">1</a> <a id="11361" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11363" href="plfa.Quantifiers.html#11354" class="Bound">m</a> <a id="11365" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="11367" class="Number">2</a> <a id="11369" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11371" href="plfa.Quantifiers.html#11342" class="Bound">n</a><a id="11372" class="Symbol">)</a> <a id="11374" class="Symbol">→</a>  <a id="11377" href="plfa.Quantifiers.html#9075" class="Datatype">odd</a> <a id="11381" href="plfa.Quantifiers.html#11342" class="Bound">n</a>

<a id="11384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11277" class="Function">∃-even</a> <a id="11391" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a>  <a id="11394" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="11399" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="11401" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11406" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a>  <a id="11409" class="Symbol">=</a>  <a id="11412" href="plfa.Quantifiers.html#9110" class="InductiveConstructor">even-zero</a>
<a id="11422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11277" class="Function">∃-even</a> <a id="11429" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="11431" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11435" href="plfa.Quantifiers.html#11435" class="Bound">m</a> <a id="11437" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="11439" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11444" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a>  <a id="11447" class="Symbol">=</a>  <a id="11450" href="plfa.Quantifiers.html#9135" class="InductiveConstructor">even-suc</a> <a id="11459" class="Symbol">(</a><a id="11460" href="plfa.Quantifiers.html#11330" class="Function">∃-odd</a> <a id="11466" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="11468" href="plfa.Quantifiers.html#11435" class="Bound">m</a> <a id="11470" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="11472" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11477" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a><a id="11478" class="Symbol">)</a>

<a id="11481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11330" class="Function">∃-odd</a>  <a id="11488" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a>     <a id="11494" href="plfa.Quantifiers.html#11494" class="Bound">m</a> <a id="11496" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="11498" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11503" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a>  <a id="11506" class="Symbol">=</a>  <a id="11509" href="plfa.Quantifiers.html#9224" class="InductiveConstructor">odd-suc</a> <a id="11517" class="Symbol">(</a><a id="11518" href="plfa.Quantifiers.html#11277" class="Function">∃-even</a> <a id="11525" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="11527" href="plfa.Quantifiers.html#11494" class="Bound">m</a> <a id="11529" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="11531" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11536" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a><a id="11537" class="Symbol">)</a>
</pre>{% endraw %}Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:

- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.

This completes the proof in the backward direction.

#### Exercise `∃-even-odd`

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

{% raw %}<pre class="Agda"><a id="12531" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `∃-|-≤`

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

{% raw %}<pre class="Agda"><a id="12668" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Existentials, Universals, and Negation

Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
{% raw %}<pre class="Agda"><a id="¬∃≃∀¬"></a><a id="13047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13047" class="Function">¬∃≃∀¬</a> <a id="13053" class="Symbol">:</a> <a id="13055" class="Symbol">∀</a> <a id="13057" class="Symbol">{</a><a id="13058" href="plfa.Quantifiers.html#13058" class="Bound">A</a> <a id="13060" class="Symbol">:</a> <a id="13062" class="PrimitiveType">Set</a><a id="13065" class="Symbol">}</a> <a id="13067" class="Symbol">{</a><a id="13068" href="plfa.Quantifiers.html#13068" class="Bound">B</a> <a id="13070" class="Symbol">:</a> <a id="13072" href="plfa.Quantifiers.html#13058" class="Bound">A</a> <a id="13074" class="Symbol">→</a> <a id="13076" class="PrimitiveType">Set</a><a id="13079" class="Symbol">}</a>
  <a id="13083" class="Symbol">→</a> <a id="13085" class="Symbol">(</a><a id="13086" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="13088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6796" class="Function">∃[</a> <a id="13091" href="plfa.Quantifiers.html#13091" class="Bound">x</a> <a id="13093" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="13095" href="plfa.Quantifiers.html#13068" class="Bound">B</a> <a id="13097" href="plfa.Quantifiers.html#13091" class="Bound">x</a><a id="13098" class="Symbol">)</a> <a id="13100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3985" class="Record Operator">≃</a> <a id="13102" class="Symbol">∀</a> <a id="13104" href="plfa.Quantifiers.html#13104" class="Bound">x</a> <a id="13106" class="Symbol">→</a> <a id="13108" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="13110" href="plfa.Quantifiers.html#13068" class="Bound">B</a> <a id="13112" href="plfa.Quantifiers.html#13104" class="Bound">x</a>
<a id="13114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13047" class="Function">¬∃≃∀¬</a> <a id="13120" class="Symbol">=</a>
  <a id="13124" class="Keyword">record</a>
    <a id="13135" class="Symbol">{</a> <a id="13137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4025" class="Field">to</a>      <a id="13145" class="Symbol">=</a>  <a id="13148" class="Symbol">λ{</a> <a id="13151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13151" class="Bound">¬∃xy</a> <a id="13156" href="plfa.Quantifiers.html#13156" class="Bound">x</a> <a id="13158" href="plfa.Quantifiers.html#13158" class="Bound">y</a> <a id="13160" class="Symbol">→</a> <a id="13162" href="plfa.Quantifiers.html#13151" class="Bound">¬∃xy</a> <a id="13167" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="13169" href="plfa.Quantifiers.html#13156" class="Bound">x</a> <a id="13171" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="13173" href="plfa.Quantifiers.html#13158" class="Bound">y</a> <a id="13175" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a> <a id="13177" class="Symbol">}</a>
    <a id="13183" class="Symbol">;</a> <a id="13185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4042" class="Field">from</a>    <a id="13193" class="Symbol">=</a>  <a id="13196" class="Symbol">λ{</a> <a id="13199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13199" class="Bound">∀¬xy</a> <a id="13204" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="13206" href="plfa.Quantifiers.html#13206" class="Bound">x</a> <a id="13208" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="13210" href="plfa.Quantifiers.html#13210" class="Bound">y</a> <a id="13212" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a> <a id="13214" class="Symbol">→</a> <a id="13216" href="plfa.Quantifiers.html#13199" class="Bound">∀¬xy</a> <a id="13221" href="plfa.Quantifiers.html#13206" class="Bound">x</a> <a id="13223" href="plfa.Quantifiers.html#13210" class="Bound">y</a> <a id="13225" class="Symbol">}</a>
    <a id="13231" class="Symbol">;</a> <a id="13233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4059" class="Field">from∘to</a> <a id="13241" class="Symbol">=</a>  <a id="13244" class="Symbol">λ{</a> <a id="13247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13247" class="Bound">¬∃xy</a> <a id="13252" class="Symbol">→</a> <a id="13254" href="plfa.Isomorphism.html#2678" class="Postulate">extensionality</a> <a id="13269" class="Symbol">λ{</a> <a id="13272" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟨</a> <a id="13274" href="plfa.Quantifiers.html#13274" class="Bound">x</a> <a id="13276" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">,</a> <a id="13278" href="plfa.Quantifiers.html#13278" class="Bound">y</a> <a id="13280" href="plfa.Quantifiers.html#4415" class="InductiveConstructor Operator">⟩</a> <a id="13282" class="Symbol">→</a> <a id="13284" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="13289" class="Symbol">}</a> <a id="13291" class="Symbol">}</a>
    <a id="13297" class="Symbol">;</a> <a id="13299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4101" class="Field">to∘from</a> <a id="13307" class="Symbol">=</a>  <a id="13310" class="Symbol">λ{</a> <a id="13313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13313" class="Bound">∀¬xy</a> <a id="13318" class="Symbol">→</a> <a id="13320" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="13325" class="Symbol">}</a>
    <a id="13331" class="Symbol">}</a>
</pre>{% endraw %}In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.

In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
{% raw %}<pre class="Agda"><a id="14148" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="14160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14160" class="Postulate">∃¬-implies-¬∀</a> <a id="14174" class="Symbol">:</a> <a id="14176" class="Symbol">∀</a> <a id="14178" class="Symbol">{</a><a id="14179" href="plfa.Quantifiers.html#14179" class="Bound">A</a> <a id="14181" class="Symbol">:</a> <a id="14183" class="PrimitiveType">Set</a><a id="14186" class="Symbol">}</a> <a id="14188" class="Symbol">{</a><a id="14189" href="plfa.Quantifiers.html#14189" class="Bound">B</a> <a id="14191" class="Symbol">:</a> <a id="14193" href="plfa.Quantifiers.html#14179" class="Bound">A</a> <a id="14195" class="Symbol">→</a> <a id="14197" class="PrimitiveType">Set</a><a id="14200" class="Symbol">}</a>
    <a id="14206" class="Symbol">→</a> <a id="14208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6796" class="Function">∃[</a> <a id="14211" href="plfa.Quantifiers.html#14211" class="Bound">x</a> <a id="14213" href="plfa.Quantifiers.html#6796" class="Function">]</a> <a id="14215" class="Symbol">(</a><a id="14216" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="14218" href="plfa.Quantifiers.html#14189" class="Bound">B</a> <a id="14220" href="plfa.Quantifiers.html#14211" class="Bound">x</a><a id="14221" class="Symbol">)</a>
      <a id="14229" class="Comment">--------------</a>
    <a id="14248" class="Symbol">→</a> <a id="14250" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="14252" class="Symbol">(∀</a> <a id="14255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14255" class="Bound">x</a> <a id="14257" class="Symbol">→</a> <a id="14259" href="plfa.Quantifiers.html#14189" class="Bound">B</a> <a id="14261" href="plfa.Quantifiers.html#14255" class="Bound">x</a><a id="14262" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin),
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws), and
[Bin-predicates]({{ site.baseurl }}/Relations/#Bin-predicates)
define a datatype of bitstrings representing natural numbers:
{% raw %}<pre class="Agda"><a id="14639" class="Keyword">data</a> <a id="Bin"></a><a id="14644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14644" class="Datatype">Bin</a> <a id="14648" class="Symbol">:</a> <a id="14650" class="PrimitiveType">Set</a> <a id="14654" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="14662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14662" class="InductiveConstructor">nil</a> <a id="14666" class="Symbol">:</a> <a id="14668" href="plfa.Quantifiers.html#14644" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="14674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14674" class="InductiveConstructor Operator">x0_</a> <a id="14678" class="Symbol">:</a> <a id="14680" href="plfa.Quantifiers.html#14644" class="Datatype">Bin</a> <a id="14684" class="Symbol">→</a> <a id="14686" href="plfa.Quantifiers.html#14644" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="14692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14692" class="InductiveConstructor Operator">x1_</a> <a id="14696" class="Symbol">:</a> <a id="14698" href="plfa.Quantifiers.html#14644" class="Datatype">Bin</a> <a id="14702" class="Symbol">→</a> <a id="14704" href="plfa.Quantifiers.html#14644" class="Datatype">Bin</a>
</pre>{% endraw %}And ask you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can x
    ---------------
    to (from x) ≡ x

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ x ](Can x)`.

{% raw %}<pre class="Agda"><a id="15076" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="15213" class="Keyword">import</a> <a id="15220" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="15233" class="Keyword">using</a> <a id="15239" class="Symbol">(</a><a id="15240" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="15241" class="Symbol">;</a> <a id="15243" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="15246" class="Symbol">;</a> <a id="15248" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="15249" class="Symbol">;</a> <a id="15251" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="15259" class="Symbol">;</a> <a id="15261" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="15269" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
