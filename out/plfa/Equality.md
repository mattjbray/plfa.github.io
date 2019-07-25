---
src       : "src/plfa/Equality.lagda.md"
title     : "Equality: Equality and equational reasoning"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
---

{% raw %}<pre class="Agda"><a id="162" class="Keyword">module</a> <a id="169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}" class="Module">plfa.Equality</a> <a id="183" class="Keyword">where</a>
</pre>{% endraw %}
Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.


## Equality

We declare equality as follows:
{% raw %}<pre class="Agda"><a id="719" class="Keyword">data</a> <a id="_≡_"></a><a id="724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#724" class="Datatype Operator">_≡_</a> <a id="728" class="Symbol">{</a><a id="729" href="plfa.Equality.html#729" class="Bound">A</a> <a id="731" class="Symbol">:</a> <a id="733" class="PrimitiveType">Set</a><a id="736" class="Symbol">}</a> <a id="738" class="Symbol">(</a><a id="739" href="plfa.Equality.html#739" class="Bound">x</a> <a id="741" class="Symbol">:</a> <a id="743" href="plfa.Equality.html#729" class="Bound">A</a><a id="744" class="Symbol">)</a> <a id="746" class="Symbol">:</a> <a id="748" href="plfa.Equality.html#729" class="Bound">A</a> <a id="750" class="Symbol">→</a> <a id="752" class="PrimitiveType">Set</a> <a id="756" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#764" class="InductiveConstructor">refl</a> <a id="769" class="Symbol">:</a> <a id="771" href="plfa.Equality.html#739" class="Bound">x</a> <a id="773" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="775" href="plfa.Equality.html#739" class="Bound">x</a>
</pre>{% endraw %}In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.

We declare the precedence of equality as follows:
{% raw %}<pre class="Agda"><a id="1424" class="Keyword">infix</a> <a id="1430" class="Number">4</a> <a id="1432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#724" class="Datatype Operator">_≡_</a>
</pre>{% endraw %}We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.


## Equality is an equivalence relation

An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry:
{% raw %}<pre class="Agda"><a id="sym"></a><a id="1887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1887" class="Function">sym</a> <a id="1891" class="Symbol">:</a> <a id="1893" class="Symbol">∀</a> <a id="1895" class="Symbol">{</a><a id="1896" href="plfa.Equality.html#1896" class="Bound">A</a> <a id="1898" class="Symbol">:</a> <a id="1900" class="PrimitiveType">Set</a><a id="1903" class="Symbol">}</a> <a id="1905" class="Symbol">{</a><a id="1906" href="plfa.Equality.html#1906" class="Bound">x</a> <a id="1908" href="plfa.Equality.html#1908" class="Bound">y</a> <a id="1910" class="Symbol">:</a> <a id="1912" href="plfa.Equality.html#1896" class="Bound">A</a><a id="1913" class="Symbol">}</a>
  <a id="1917" class="Symbol">→</a> <a id="1919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1906" class="Bound">x</a> <a id="1921" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="1923" href="plfa.Equality.html#1908" class="Bound">y</a>
    <a id="1929" class="Comment">-----</a>
  <a id="1937" class="Symbol">→</a> <a id="1939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1908" class="Bound">y</a> <a id="1941" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="1943" href="plfa.Equality.html#1906" class="Bound">x</a>
<a id="1945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1887" class="Function">sym</a> <a id="1949" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a> <a id="1954" class="Symbol">=</a> <a id="1956" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>
</pre>{% endraw %}How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.

It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!

Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

This completes the definition as given above.

Transitivity is equally straightforward:
{% raw %}<pre class="Agda"><a id="trans"></a><a id="3615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3615" class="Function">trans</a> <a id="3621" class="Symbol">:</a> <a id="3623" class="Symbol">∀</a> <a id="3625" class="Symbol">{</a><a id="3626" href="plfa.Equality.html#3626" class="Bound">A</a> <a id="3628" class="Symbol">:</a> <a id="3630" class="PrimitiveType">Set</a><a id="3633" class="Symbol">}</a> <a id="3635" class="Symbol">{</a><a id="3636" href="plfa.Equality.html#3636" class="Bound">x</a> <a id="3638" href="plfa.Equality.html#3638" class="Bound">y</a> <a id="3640" href="plfa.Equality.html#3640" class="Bound">z</a> <a id="3642" class="Symbol">:</a> <a id="3644" href="plfa.Equality.html#3626" class="Bound">A</a><a id="3645" class="Symbol">}</a>
  <a id="3649" class="Symbol">→</a> <a id="3651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3636" class="Bound">x</a> <a id="3653" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="3655" href="plfa.Equality.html#3638" class="Bound">y</a>
  <a id="3659" class="Symbol">→</a> <a id="3661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3638" class="Bound">y</a> <a id="3663" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="3665" href="plfa.Equality.html#3640" class="Bound">z</a>
    <a id="3671" class="Comment">-----</a>
  <a id="3679" class="Symbol">→</a> <a id="3681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3636" class="Bound">x</a> <a id="3683" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="3685" href="plfa.Equality.html#3640" class="Bound">z</a>
<a id="3687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3615" class="Function">trans</a> <a id="3693" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a> <a id="3698" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>  <a id="3704" class="Symbol">=</a>  <a id="3707" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>
</pre>{% endraw %}Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.

## Congruence and substitution {#cong}

Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both:
{% raw %}<pre class="Agda"><a id="cong"></a><a id="4031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4031" class="Function">cong</a> <a id="4036" class="Symbol">:</a> <a id="4038" class="Symbol">∀</a> <a id="4040" class="Symbol">{</a><a id="4041" href="plfa.Equality.html#4041" class="Bound">A</a> <a id="4043" href="plfa.Equality.html#4043" class="Bound">B</a> <a id="4045" class="Symbol">:</a> <a id="4047" class="PrimitiveType">Set</a><a id="4050" class="Symbol">}</a> <a id="4052" class="Symbol">(</a><a id="4053" href="plfa.Equality.html#4053" class="Bound">f</a> <a id="4055" class="Symbol">:</a> <a id="4057" href="plfa.Equality.html#4041" class="Bound">A</a> <a id="4059" class="Symbol">→</a> <a id="4061" href="plfa.Equality.html#4043" class="Bound">B</a><a id="4062" class="Symbol">)</a> <a id="4064" class="Symbol">{</a><a id="4065" href="plfa.Equality.html#4065" class="Bound">x</a> <a id="4067" href="plfa.Equality.html#4067" class="Bound">y</a> <a id="4069" class="Symbol">:</a> <a id="4071" href="plfa.Equality.html#4041" class="Bound">A</a><a id="4072" class="Symbol">}</a>
  <a id="4076" class="Symbol">→</a> <a id="4078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4065" class="Bound">x</a> <a id="4080" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="4082" href="plfa.Equality.html#4067" class="Bound">y</a>
    <a id="4088" class="Comment">---------</a>
  <a id="4100" class="Symbol">→</a> <a id="4102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4053" class="Bound">f</a> <a id="4104" href="plfa.Equality.html#4065" class="Bound">x</a> <a id="4106" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="4108" href="plfa.Equality.html#4053" class="Bound">f</a> <a id="4110" href="plfa.Equality.html#4067" class="Bound">y</a>
<a id="4112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4031" class="Function">cong</a> <a id="4117" href="plfa.Equality.html#4117" class="Bound">f</a> <a id="4119" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>  <a id="4125" class="Symbol">=</a>  <a id="4128" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
Congruence of functions with two arguments is similar:
{% raw %}<pre class="Agda"><a id="cong₂"></a><a id="4197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4197" class="Function">cong₂</a> <a id="4203" class="Symbol">:</a> <a id="4205" class="Symbol">∀</a> <a id="4207" class="Symbol">{</a><a id="4208" href="plfa.Equality.html#4208" class="Bound">A</a> <a id="4210" href="plfa.Equality.html#4210" class="Bound">B</a> <a id="4212" href="plfa.Equality.html#4212" class="Bound">C</a> <a id="4214" class="Symbol">:</a> <a id="4216" class="PrimitiveType">Set</a><a id="4219" class="Symbol">}</a> <a id="4221" class="Symbol">(</a><a id="4222" href="plfa.Equality.html#4222" class="Bound">f</a> <a id="4224" class="Symbol">:</a> <a id="4226" href="plfa.Equality.html#4208" class="Bound">A</a> <a id="4228" class="Symbol">→</a> <a id="4230" href="plfa.Equality.html#4210" class="Bound">B</a> <a id="4232" class="Symbol">→</a> <a id="4234" href="plfa.Equality.html#4212" class="Bound">C</a><a id="4235" class="Symbol">)</a> <a id="4237" class="Symbol">{</a><a id="4238" href="plfa.Equality.html#4238" class="Bound">u</a> <a id="4240" href="plfa.Equality.html#4240" class="Bound">x</a> <a id="4242" class="Symbol">:</a> <a id="4244" href="plfa.Equality.html#4208" class="Bound">A</a><a id="4245" class="Symbol">}</a> <a id="4247" class="Symbol">{</a><a id="4248" href="plfa.Equality.html#4248" class="Bound">v</a> <a id="4250" href="plfa.Equality.html#4250" class="Bound">y</a> <a id="4252" class="Symbol">:</a> <a id="4254" href="plfa.Equality.html#4210" class="Bound">B</a><a id="4255" class="Symbol">}</a>
  <a id="4259" class="Symbol">→</a> <a id="4261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4238" class="Bound">u</a> <a id="4263" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="4265" href="plfa.Equality.html#4240" class="Bound">x</a>
  <a id="4269" class="Symbol">→</a> <a id="4271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4248" class="Bound">v</a> <a id="4273" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="4275" href="plfa.Equality.html#4250" class="Bound">y</a>
    <a id="4281" class="Comment">-------------</a>
  <a id="4297" class="Symbol">→</a> <a id="4299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4222" class="Bound">f</a> <a id="4301" href="plfa.Equality.html#4238" class="Bound">u</a> <a id="4303" href="plfa.Equality.html#4248" class="Bound">v</a> <a id="4305" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="4307" href="plfa.Equality.html#4222" class="Bound">f</a> <a id="4309" href="plfa.Equality.html#4240" class="Bound">x</a> <a id="4311" href="plfa.Equality.html#4250" class="Bound">y</a>
<a id="4313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4197" class="Function">cong₂</a> <a id="4319" href="plfa.Equality.html#4319" class="Bound">f</a> <a id="4321" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a> <a id="4326" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>  <a id="4332" class="Symbol">=</a>  <a id="4335" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms:
{% raw %}<pre class="Agda"><a id="cong-app"></a><a id="4507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4507" class="Function">cong-app</a> <a id="4516" class="Symbol">:</a> <a id="4518" class="Symbol">∀</a> <a id="4520" class="Symbol">{</a><a id="4521" href="plfa.Equality.html#4521" class="Bound">A</a> <a id="4523" href="plfa.Equality.html#4523" class="Bound">B</a> <a id="4525" class="Symbol">:</a> <a id="4527" class="PrimitiveType">Set</a><a id="4530" class="Symbol">}</a> <a id="4532" class="Symbol">{</a><a id="4533" href="plfa.Equality.html#4533" class="Bound">f</a> <a id="4535" href="plfa.Equality.html#4535" class="Bound">g</a> <a id="4537" class="Symbol">:</a> <a id="4539" href="plfa.Equality.html#4521" class="Bound">A</a> <a id="4541" class="Symbol">→</a> <a id="4543" href="plfa.Equality.html#4523" class="Bound">B</a><a id="4544" class="Symbol">}</a>
  <a id="4548" class="Symbol">→</a> <a id="4550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4533" class="Bound">f</a> <a id="4552" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="4554" href="plfa.Equality.html#4535" class="Bound">g</a>
    <a id="4560" class="Comment">---------------------</a>
  <a id="4584" class="Symbol">→</a> <a id="4586" class="Symbol">∀</a> <a id="4588" class="Symbol">(</a><a id="4589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4589" class="Bound">x</a> <a id="4591" class="Symbol">:</a> <a id="4593" href="plfa.Equality.html#4521" class="Bound">A</a><a id="4594" class="Symbol">)</a> <a id="4596" class="Symbol">→</a> <a id="4598" href="plfa.Equality.html#4533" class="Bound">f</a> <a id="4600" href="plfa.Equality.html#4589" class="Bound">x</a> <a id="4602" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="4604" href="plfa.Equality.html#4535" class="Bound">g</a> <a id="4606" href="plfa.Equality.html#4589" class="Bound">x</a>
<a id="4608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4507" class="Function">cong-app</a> <a id="4617" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a> <a id="4622" href="plfa.Equality.html#4622" class="Bound">x</a> <a id="4624" class="Symbol">=</a> <a id="4626" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second:
{% raw %}<pre class="Agda"><a id="subst"></a><a id="4773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4773" class="Function">subst</a> <a id="4779" class="Symbol">:</a> <a id="4781" class="Symbol">∀</a> <a id="4783" class="Symbol">{</a><a id="4784" href="plfa.Equality.html#4784" class="Bound">A</a> <a id="4786" class="Symbol">:</a> <a id="4788" class="PrimitiveType">Set</a><a id="4791" class="Symbol">}</a> <a id="4793" class="Symbol">{</a><a id="4794" href="plfa.Equality.html#4794" class="Bound">x</a> <a id="4796" href="plfa.Equality.html#4796" class="Bound">y</a> <a id="4798" class="Symbol">:</a> <a id="4800" href="plfa.Equality.html#4784" class="Bound">A</a><a id="4801" class="Symbol">}</a> <a id="4803" class="Symbol">(</a><a id="4804" href="plfa.Equality.html#4804" class="Bound">P</a> <a id="4806" class="Symbol">:</a> <a id="4808" href="plfa.Equality.html#4784" class="Bound">A</a> <a id="4810" class="Symbol">→</a> <a id="4812" class="PrimitiveType">Set</a><a id="4815" class="Symbol">)</a>
  <a id="4819" class="Symbol">→</a> <a id="4821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4794" class="Bound">x</a> <a id="4823" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="4825" href="plfa.Equality.html#4796" class="Bound">y</a>
    <a id="4831" class="Comment">---------</a>
  <a id="4843" class="Symbol">→</a> <a id="4845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4804" class="Bound">P</a> <a id="4847" href="plfa.Equality.html#4794" class="Bound">x</a> <a id="4849" class="Symbol">→</a> <a id="4851" href="plfa.Equality.html#4804" class="Bound">P</a> <a id="4853" href="plfa.Equality.html#4796" class="Bound">y</a>
<a id="4855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4773" class="Function">subst</a> <a id="4861" href="plfa.Equality.html#4861" class="Bound">P</a> <a id="4863" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a> <a id="4868" href="plfa.Equality.html#4868" class="Bound">px</a> <a id="4871" class="Symbol">=</a> <a id="4873" href="plfa.Equality.html#4868" class="Bound">px</a>
</pre>{% endraw %}

## Chains of equations

Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library:
{% raw %}<pre class="Agda"><a id="5121" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="5128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5128" class="Module">≡-Reasoning</a> <a id="5140" class="Symbol">{</a><a id="5141" href="plfa.Equality.html#5141" class="Bound">A</a> <a id="5143" class="Symbol">:</a> <a id="5145" class="PrimitiveType">Set</a><a id="5148" class="Symbol">}</a> <a id="5150" class="Keyword">where</a>

  <a id="5159" class="Keyword">infix</a>  <a id="5166" class="Number">1</a> <a id="5168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5216" class="Function Operator">begin_</a>
  <a id="5177" class="Keyword">infixr</a> <a id="5184" class="Number">2</a> <a id="5186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5296" class="Function Operator">_≡⟨⟩_</a> <a id="5192" href="plfa.Equality.html#5381" class="Function Operator">_≡⟨_⟩_</a>
  <a id="5201" class="Keyword">infix</a>  <a id="5208" class="Number">3</a> <a id="5210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5496" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="5216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5216" class="Function Operator">begin_</a> <a id="5223" class="Symbol">:</a> <a id="5225" class="Symbol">∀</a> <a id="5227" class="Symbol">{</a><a id="5228" href="plfa.Equality.html#5228" class="Bound">x</a> <a id="5230" href="plfa.Equality.html#5230" class="Bound">y</a> <a id="5232" class="Symbol">:</a> <a id="5234" href="plfa.Equality.html#5141" class="Bound">A</a><a id="5235" class="Symbol">}</a>
    <a id="5241" class="Symbol">→</a> <a id="5243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5228" class="Bound">x</a> <a id="5245" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="5247" href="plfa.Equality.html#5230" class="Bound">y</a>
      <a id="5255" class="Comment">-----</a>
    <a id="5265" class="Symbol">→</a> <a id="5267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5228" class="Bound">x</a> <a id="5269" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="5271" href="plfa.Equality.html#5230" class="Bound">y</a>
  <a id="5275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5216" class="Function Operator">begin</a> <a id="5281" href="plfa.Equality.html#5281" class="Bound">x≡y</a>  <a id="5286" class="Symbol">=</a>  <a id="5289" href="plfa.Equality.html#5281" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="5296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5296" class="Function Operator">_≡⟨⟩_</a> <a id="5302" class="Symbol">:</a> <a id="5304" class="Symbol">∀</a> <a id="5306" class="Symbol">(</a><a id="5307" href="plfa.Equality.html#5307" class="Bound">x</a> <a id="5309" class="Symbol">:</a> <a id="5311" href="plfa.Equality.html#5141" class="Bound">A</a><a id="5312" class="Symbol">)</a> <a id="5314" class="Symbol">{</a><a id="5315" href="plfa.Equality.html#5315" class="Bound">y</a> <a id="5317" class="Symbol">:</a> <a id="5319" href="plfa.Equality.html#5141" class="Bound">A</a><a id="5320" class="Symbol">}</a>
    <a id="5326" class="Symbol">→</a> <a id="5328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5307" class="Bound">x</a> <a id="5330" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="5332" href="plfa.Equality.html#5315" class="Bound">y</a>
      <a id="5340" class="Comment">-----</a>
    <a id="5350" class="Symbol">→</a> <a id="5352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5307" class="Bound">x</a> <a id="5354" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="5356" href="plfa.Equality.html#5315" class="Bound">y</a>
  <a id="5360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5360" class="Bound">x</a> <a id="5362" href="plfa.Equality.html#5296" class="Function Operator">≡⟨⟩</a> <a id="5366" href="plfa.Equality.html#5366" class="Bound">x≡y</a>  <a id="5371" class="Symbol">=</a>  <a id="5374" href="plfa.Equality.html#5366" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="5381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Function Operator">_≡⟨_⟩_</a> <a id="5388" class="Symbol">:</a> <a id="5390" class="Symbol">∀</a> <a id="5392" class="Symbol">(</a><a id="5393" href="plfa.Equality.html#5393" class="Bound">x</a> <a id="5395" class="Symbol">:</a> <a id="5397" href="plfa.Equality.html#5141" class="Bound">A</a><a id="5398" class="Symbol">)</a> <a id="5400" class="Symbol">{</a><a id="5401" href="plfa.Equality.html#5401" class="Bound">y</a> <a id="5403" href="plfa.Equality.html#5403" class="Bound">z</a> <a id="5405" class="Symbol">:</a> <a id="5407" href="plfa.Equality.html#5141" class="Bound">A</a><a id="5408" class="Symbol">}</a>
    <a id="5414" class="Symbol">→</a> <a id="5416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5393" class="Bound">x</a> <a id="5418" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="5420" href="plfa.Equality.html#5401" class="Bound">y</a>
    <a id="5426" class="Symbol">→</a> <a id="5428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5401" class="Bound">y</a> <a id="5430" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="5432" href="plfa.Equality.html#5403" class="Bound">z</a>
      <a id="5440" class="Comment">-----</a>
    <a id="5450" class="Symbol">→</a> <a id="5452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5393" class="Bound">x</a> <a id="5454" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="5456" href="plfa.Equality.html#5403" class="Bound">z</a>
  <a id="5460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5460" class="Bound">x</a> <a id="5462" href="plfa.Equality.html#5381" class="Function Operator">≡⟨</a> <a id="5465" href="plfa.Equality.html#5465" class="Bound">x≡y</a> <a id="5469" href="plfa.Equality.html#5381" class="Function Operator">⟩</a> <a id="5471" href="plfa.Equality.html#5471" class="Bound">y≡z</a>  <a id="5476" class="Symbol">=</a>  <a id="5479" href="plfa.Equality.html#3615" class="Function">trans</a> <a id="5485" href="plfa.Equality.html#5465" class="Bound">x≡y</a> <a id="5489" href="plfa.Equality.html#5471" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="5496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5496" class="Function Operator">_∎</a> <a id="5499" class="Symbol">:</a> <a id="5501" class="Symbol">∀</a> <a id="5503" class="Symbol">(</a><a id="5504" href="plfa.Equality.html#5504" class="Bound">x</a> <a id="5506" class="Symbol">:</a> <a id="5508" href="plfa.Equality.html#5141" class="Bound">A</a><a id="5509" class="Symbol">)</a>
      <a id="5517" class="Comment">-----</a>
    <a id="5527" class="Symbol">→</a> <a id="5529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5504" class="Bound">x</a> <a id="5531" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="5533" href="plfa.Equality.html#5504" class="Bound">x</a>
  <a id="5537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5537" class="Bound">x</a> <a id="5539" href="plfa.Equality.html#5496" class="Function Operator">∎</a>  <a id="5542" class="Symbol">=</a>  <a id="5545" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>

<a id="5551" class="Keyword">open</a> <a id="5556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5128" class="Module">≡-Reasoning</a>
</pre>{% endraw %}This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.

As an example, let's look at a proof of transitivity
as a chain of equations:
{% raw %}<pre class="Agda"><a id="trans′"></a><a id="6187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6187" class="Function">trans′</a> <a id="6194" class="Symbol">:</a> <a id="6196" class="Symbol">∀</a> <a id="6198" class="Symbol">{</a><a id="6199" href="plfa.Equality.html#6199" class="Bound">A</a> <a id="6201" class="Symbol">:</a> <a id="6203" class="PrimitiveType">Set</a><a id="6206" class="Symbol">}</a> <a id="6208" class="Symbol">{</a><a id="6209" href="plfa.Equality.html#6209" class="Bound">x</a> <a id="6211" href="plfa.Equality.html#6211" class="Bound">y</a> <a id="6213" href="plfa.Equality.html#6213" class="Bound">z</a> <a id="6215" class="Symbol">:</a> <a id="6217" href="plfa.Equality.html#6199" class="Bound">A</a><a id="6218" class="Symbol">}</a>
  <a id="6222" class="Symbol">→</a> <a id="6224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6209" class="Bound">x</a> <a id="6226" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="6228" href="plfa.Equality.html#6211" class="Bound">y</a>
  <a id="6232" class="Symbol">→</a> <a id="6234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6211" class="Bound">y</a> <a id="6236" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="6238" href="plfa.Equality.html#6213" class="Bound">z</a>
    <a id="6244" class="Comment">-----</a>
  <a id="6252" class="Symbol">→</a> <a id="6254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6209" class="Bound">x</a> <a id="6256" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="6258" href="plfa.Equality.html#6213" class="Bound">z</a>
<a id="6260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6187" class="Function">trans′</a> <a id="6267" class="Symbol">{</a><a id="6268" href="plfa.Equality.html#6268" class="Bound">A</a><a id="6269" class="Symbol">}</a> <a id="6271" class="Symbol">{</a><a id="6272" href="plfa.Equality.html#6272" class="Bound">x</a><a id="6273" class="Symbol">}</a> <a id="6275" class="Symbol">{</a><a id="6276" href="plfa.Equality.html#6276" class="Bound">y</a><a id="6277" class="Symbol">}</a> <a id="6279" class="Symbol">{</a><a id="6280" href="plfa.Equality.html#6280" class="Bound">z</a><a id="6281" class="Symbol">}</a> <a id="6283" href="plfa.Equality.html#6283" class="Bound">x≡y</a> <a id="6287" href="plfa.Equality.html#6287" class="Bound">y≡z</a> <a id="6291" class="Symbol">=</a>
  <a id="6295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5216" class="Function Operator">begin</a>
    <a id="6305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6272" class="Bound">x</a>
  <a id="6309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Function Operator">≡⟨</a> <a id="6312" href="plfa.Equality.html#6283" class="Bound">x≡y</a> <a id="6316" href="plfa.Equality.html#5381" class="Function Operator">⟩</a>
    <a id="6322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6276" class="Bound">y</a>
  <a id="6326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Function Operator">≡⟨</a> <a id="6329" href="plfa.Equality.html#6287" class="Bound">y≡z</a> <a id="6333" href="plfa.Equality.html#5381" class="Function Operator">⟩</a>
    <a id="6339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6280" class="Bound">z</a>
  <a id="6343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5496" class="Function Operator">∎</a>
</pre>{% endraw %}According to the fixity declarations, the body parses as follows:

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:

    trans x≡y (trans y≡z refl)

We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` that ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.


## Chains of equations, another example

As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict:
{% raw %}<pre class="Agda"><a id="8028" class="Keyword">data</a> <a id="ℕ"></a><a id="8033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8033" class="Datatype">ℕ</a> <a id="8035" class="Symbol">:</a> <a id="8037" class="PrimitiveType">Set</a> <a id="8041" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="8049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8049" class="InductiveConstructor">zero</a> <a id="8054" class="Symbol">:</a> <a id="8056" href="plfa.Equality.html#8033" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="8060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8060" class="InductiveConstructor">suc</a>  <a id="8065" class="Symbol">:</a> <a id="8067" href="plfa.Equality.html#8033" class="Datatype">ℕ</a> <a id="8069" class="Symbol">→</a> <a id="8071" href="plfa.Equality.html#8033" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="8074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8074" class="Function Operator">_+_</a> <a id="8078" class="Symbol">:</a> <a id="8080" href="plfa.Equality.html#8033" class="Datatype">ℕ</a> <a id="8082" class="Symbol">→</a> <a id="8084" href="plfa.Equality.html#8033" class="Datatype">ℕ</a> <a id="8086" class="Symbol">→</a> <a id="8088" href="plfa.Equality.html#8033" class="Datatype">ℕ</a>
<a id="8090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8049" class="InductiveConstructor">zero</a>    <a id="8098" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8100" href="plfa.Equality.html#8100" class="Bound">n</a>  <a id="8103" class="Symbol">=</a>  <a id="8106" href="plfa.Equality.html#8100" class="Bound">n</a>
<a id="8108" class="Symbol">(</a><a id="8109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8060" class="InductiveConstructor">suc</a> <a id="8113" href="plfa.Equality.html#8113" class="Bound">m</a><a id="8114" class="Symbol">)</a> <a id="8116" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8118" href="plfa.Equality.html#8118" class="Bound">n</a>  <a id="8121" class="Symbol">=</a>  <a id="8124" href="plfa.Equality.html#8060" class="InductiveConstructor">suc</a> <a id="8128" class="Symbol">(</a><a id="8129" href="plfa.Equality.html#8113" class="Bound">m</a> <a id="8131" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8133" href="plfa.Equality.html#8118" class="Bound">n</a><a id="8134" class="Symbol">)</a>
</pre>{% endraw %}
To save space we postulate (rather than prove in full) two lemmas:
{% raw %}<pre class="Agda"><a id="8212" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="8224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8224" class="Postulate">+-identity</a> <a id="8235" class="Symbol">:</a> <a id="8237" class="Symbol">∀</a> <a id="8239" class="Symbol">(</a><a id="8240" href="plfa.Equality.html#8240" class="Bound">m</a> <a id="8242" class="Symbol">:</a> <a id="8244" href="plfa.Equality.html#8033" class="Datatype">ℕ</a><a id="8245" class="Symbol">)</a> <a id="8247" class="Symbol">→</a> <a id="8249" href="plfa.Equality.html#8240" class="Bound">m</a> <a id="8251" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8253" href="plfa.Equality.html#8049" class="InductiveConstructor">zero</a> <a id="8258" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="8260" href="plfa.Equality.html#8240" class="Bound">m</a>
  <a id="+-suc"></a><a id="8264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8264" class="Postulate">+-suc</a> <a id="8270" class="Symbol">:</a> <a id="8272" class="Symbol">∀</a> <a id="8274" class="Symbol">(</a><a id="8275" href="plfa.Equality.html#8275" class="Bound">m</a> <a id="8277" href="plfa.Equality.html#8277" class="Bound">n</a> <a id="8279" class="Symbol">:</a> <a id="8281" href="plfa.Equality.html#8033" class="Datatype">ℕ</a><a id="8282" class="Symbol">)</a> <a id="8284" class="Symbol">→</a> <a id="8286" href="plfa.Equality.html#8275" class="Bound">m</a> <a id="8288" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8290" href="plfa.Equality.html#8060" class="InductiveConstructor">suc</a> <a id="8294" href="plfa.Equality.html#8277" class="Bound">n</a> <a id="8296" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="8298" href="plfa.Equality.html#8060" class="InductiveConstructor">suc</a> <a id="8302" class="Symbol">(</a><a id="8303" href="plfa.Equality.html#8275" class="Bound">m</a> <a id="8305" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8307" href="plfa.Equality.html#8277" class="Bound">n</a><a id="8308" class="Symbol">)</a>
</pre>{% endraw %}This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.

We then repeat the proof of commutativity:
{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="8658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8658" class="Function">+-comm</a> <a id="8665" class="Symbol">:</a> <a id="8667" class="Symbol">∀</a> <a id="8669" class="Symbol">(</a><a id="8670" href="plfa.Equality.html#8670" class="Bound">m</a> <a id="8672" href="plfa.Equality.html#8672" class="Bound">n</a> <a id="8674" class="Symbol">:</a> <a id="8676" href="plfa.Equality.html#8033" class="Datatype">ℕ</a><a id="8677" class="Symbol">)</a> <a id="8679" class="Symbol">→</a> <a id="8681" href="plfa.Equality.html#8670" class="Bound">m</a> <a id="8683" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8685" href="plfa.Equality.html#8672" class="Bound">n</a> <a id="8687" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="8689" href="plfa.Equality.html#8672" class="Bound">n</a> <a id="8691" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8693" href="plfa.Equality.html#8670" class="Bound">m</a>
<a id="8695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8658" class="Function">+-comm</a> <a id="8702" href="plfa.Equality.html#8702" class="Bound">m</a> <a id="8704" href="plfa.Equality.html#8049" class="InductiveConstructor">zero</a> <a id="8709" class="Symbol">=</a>
  <a id="8713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5216" class="Function Operator">begin</a>
    <a id="8723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8702" class="Bound">m</a> <a id="8725" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8727" href="plfa.Equality.html#8049" class="InductiveConstructor">zero</a>
  <a id="8734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Function Operator">≡⟨</a> <a id="8737" href="plfa.Equality.html#8224" class="Postulate">+-identity</a> <a id="8748" href="plfa.Equality.html#8702" class="Bound">m</a> <a id="8750" href="plfa.Equality.html#5381" class="Function Operator">⟩</a>
    <a id="8756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8702" class="Bound">m</a>
  <a id="8760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5296" class="Function Operator">≡⟨⟩</a>
    <a id="8768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8049" class="InductiveConstructor">zero</a> <a id="8773" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8775" href="plfa.Equality.html#8702" class="Bound">m</a>
  <a id="8779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5496" class="Function Operator">∎</a>
<a id="8781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8658" class="Function">+-comm</a> <a id="8788" href="plfa.Equality.html#8788" class="Bound">m</a> <a id="8790" class="Symbol">(</a><a id="8791" href="plfa.Equality.html#8060" class="InductiveConstructor">suc</a> <a id="8795" href="plfa.Equality.html#8795" class="Bound">n</a><a id="8796" class="Symbol">)</a> <a id="8798" class="Symbol">=</a>
  <a id="8802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5216" class="Function Operator">begin</a>
    <a id="8812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8788" class="Bound">m</a> <a id="8814" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8816" href="plfa.Equality.html#8060" class="InductiveConstructor">suc</a> <a id="8820" href="plfa.Equality.html#8795" class="Bound">n</a>
  <a id="8824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Function Operator">≡⟨</a> <a id="8827" href="plfa.Equality.html#8264" class="Postulate">+-suc</a> <a id="8833" href="plfa.Equality.html#8788" class="Bound">m</a> <a id="8835" href="plfa.Equality.html#8795" class="Bound">n</a> <a id="8837" href="plfa.Equality.html#5381" class="Function Operator">⟩</a>
    <a id="8843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8060" class="InductiveConstructor">suc</a> <a id="8847" class="Symbol">(</a><a id="8848" href="plfa.Equality.html#8788" class="Bound">m</a> <a id="8850" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8852" href="plfa.Equality.html#8795" class="Bound">n</a><a id="8853" class="Symbol">)</a>
  <a id="8857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Function Operator">≡⟨</a> <a id="8860" href="plfa.Equality.html#4031" class="Function">cong</a> <a id="8865" href="plfa.Equality.html#8060" class="InductiveConstructor">suc</a> <a id="8869" class="Symbol">(</a><a id="8870" href="plfa.Equality.html#8658" class="Function">+-comm</a> <a id="8877" href="plfa.Equality.html#8788" class="Bound">m</a> <a id="8879" href="plfa.Equality.html#8795" class="Bound">n</a><a id="8880" class="Symbol">)</a> <a id="8882" href="plfa.Equality.html#5381" class="Function Operator">⟩</a>
    <a id="8888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8060" class="InductiveConstructor">suc</a> <a id="8892" class="Symbol">(</a><a id="8893" href="plfa.Equality.html#8795" class="Bound">n</a> <a id="8895" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8897" href="plfa.Equality.html#8788" class="Bound">m</a><a id="8898" class="Symbol">)</a>
  <a id="8902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5296" class="Function Operator">≡⟨⟩</a>
    <a id="8910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8060" class="InductiveConstructor">suc</a> <a id="8914" href="plfa.Equality.html#8795" class="Bound">n</a> <a id="8916" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="8918" href="plfa.Equality.html#8788" class="Bound">m</a>
  <a id="8922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5496" class="Function Operator">∎</a>
</pre>{% endraw %}The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.

Agda always treats a term as equivalent to its
simplified term.  The reason that one can write

      suc (n + m)
    ≡⟨⟩
      suc n + m

is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write

      suc n + m
    ≡⟨⟩
      suc (n + m)

and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.


#### Exercise `≤-Reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}/Relations/)
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.

{% raw %}<pre class="Agda"><a id="10002" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}


## Rewriting

Consider a property of natural numbers, such as being even.
We repeat the earlier definition:
{% raw %}<pre class="Agda"><a id="10144" class="Keyword">data</a> <a id="even"></a><a id="10149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10149" class="Datatype">even</a> <a id="10154" class="Symbol">:</a> <a id="10156" href="plfa.Equality.html#8033" class="Datatype">ℕ</a> <a id="10158" class="Symbol">→</a> <a id="10160" class="PrimitiveType">Set</a>
<a id="10164" class="Keyword">data</a> <a id="odd"></a><a id="10169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10169" class="Datatype">odd</a>  <a id="10174" class="Symbol">:</a> <a id="10176" href="plfa.Equality.html#8033" class="Datatype">ℕ</a> <a id="10178" class="Symbol">→</a> <a id="10180" class="PrimitiveType">Set</a>

<a id="10185" class="Keyword">data</a> <a id="10190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10149" class="Datatype">even</a> <a id="10195" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="10204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10204" class="InductiveConstructor">even-zero</a> <a id="10214" class="Symbol">:</a> <a id="10216" href="plfa.Equality.html#10149" class="Datatype">even</a> <a id="10221" href="plfa.Equality.html#8049" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="10229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10229" class="InductiveConstructor">even-suc</a> <a id="10238" class="Symbol">:</a> <a id="10240" class="Symbol">∀</a> <a id="10242" class="Symbol">{</a><a id="10243" href="plfa.Equality.html#10243" class="Bound">n</a> <a id="10245" class="Symbol">:</a> <a id="10247" href="plfa.Equality.html#8033" class="Datatype">ℕ</a><a id="10248" class="Symbol">}</a>
    <a id="10254" class="Symbol">→</a> <a id="10256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10169" class="Datatype">odd</a> <a id="10260" href="plfa.Equality.html#10243" class="Bound">n</a>
      <a id="10268" class="Comment">------------</a>
    <a id="10285" class="Symbol">→</a> <a id="10287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10149" class="Datatype">even</a> <a id="10292" class="Symbol">(</a><a id="10293" href="plfa.Equality.html#8060" class="InductiveConstructor">suc</a> <a id="10297" href="plfa.Equality.html#10243" class="Bound">n</a><a id="10298" class="Symbol">)</a>

<a id="10301" class="Keyword">data</a> <a id="10306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10169" class="Datatype">odd</a> <a id="10310" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="10318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10318" class="InductiveConstructor">odd-suc</a> <a id="10326" class="Symbol">:</a> <a id="10328" class="Symbol">∀</a> <a id="10330" class="Symbol">{</a><a id="10331" href="plfa.Equality.html#10331" class="Bound">n</a> <a id="10333" class="Symbol">:</a> <a id="10335" href="plfa.Equality.html#8033" class="Datatype">ℕ</a><a id="10336" class="Symbol">}</a>
    <a id="10342" class="Symbol">→</a> <a id="10344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10149" class="Datatype">even</a> <a id="10349" href="plfa.Equality.html#10331" class="Bound">n</a>
      <a id="10357" class="Comment">-----------</a>
    <a id="10373" class="Symbol">→</a> <a id="10375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10169" class="Datatype">odd</a> <a id="10379" class="Symbol">(</a><a id="10380" href="plfa.Equality.html#8060" class="InductiveConstructor">suc</a> <a id="10384" href="plfa.Equality.html#10331" class="Bound">n</a><a id="10385" class="Symbol">)</a>
</pre>{% endraw %}In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.

Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality:
{% raw %}<pre class="Agda"><a id="10783" class="Symbol">{-#</a> <a id="10787" class="Keyword">BUILTIN</a> <a id="10795" class="Pragma">EQUALITY</a> <a id="10804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#724" class="Datatype Operator">_≡_</a> <a id="10808" class="Symbol">#-}</a>
</pre>{% endraw %}
We can then prove the desired property as follows:
{% raw %}<pre class="Agda"><a id="even-comm"></a><a id="10872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10872" class="Function">even-comm</a> <a id="10882" class="Symbol">:</a> <a id="10884" class="Symbol">∀</a> <a id="10886" class="Symbol">(</a><a id="10887" href="plfa.Equality.html#10887" class="Bound">m</a> <a id="10889" href="plfa.Equality.html#10889" class="Bound">n</a> <a id="10891" class="Symbol">:</a> <a id="10893" href="plfa.Equality.html#8033" class="Datatype">ℕ</a><a id="10894" class="Symbol">)</a>
  <a id="10898" class="Symbol">→</a> <a id="10900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10149" class="Datatype">even</a> <a id="10905" class="Symbol">(</a><a id="10906" href="plfa.Equality.html#10887" class="Bound">m</a> <a id="10908" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="10910" href="plfa.Equality.html#10889" class="Bound">n</a><a id="10911" class="Symbol">)</a>
    <a id="10917" class="Comment">------------</a>
  <a id="10932" class="Symbol">→</a> <a id="10934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10149" class="Datatype">even</a> <a id="10939" class="Symbol">(</a><a id="10940" href="plfa.Equality.html#10889" class="Bound">n</a> <a id="10942" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="10944" href="plfa.Equality.html#10887" class="Bound">m</a><a id="10945" class="Symbol">)</a>
<a id="10947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10872" class="Function">even-comm</a> <a id="10957" href="plfa.Equality.html#10957" class="Bound">m</a> <a id="10959" href="plfa.Equality.html#10959" class="Bound">n</a> <a id="10961" href="plfa.Equality.html#10961" class="Bound">ev</a>  <a id="10965" class="Keyword">rewrite</a> <a id="10973" href="plfa.Equality.html#8658" class="Function">+-comm</a> <a id="10980" href="plfa.Equality.html#10959" class="Bound">n</a> <a id="10982" href="plfa.Equality.html#10957" class="Bound">m</a>  <a id="10985" class="Symbol">=</a>  <a id="10988" href="plfa.Equality.html#10961" class="Bound">ev</a>
</pre>{% endraw %}Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.

It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

Now we add the rewrite:

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.


## Multiple rewrites

One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities:
{% raw %}<pre class="Agda"><a id="+-comm′"></a><a id="12648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12648" class="Function">+-comm′</a> <a id="12656" class="Symbol">:</a> <a id="12658" class="Symbol">∀</a> <a id="12660" class="Symbol">(</a><a id="12661" href="plfa.Equality.html#12661" class="Bound">m</a> <a id="12663" href="plfa.Equality.html#12663" class="Bound">n</a> <a id="12665" class="Symbol">:</a> <a id="12667" href="plfa.Equality.html#8033" class="Datatype">ℕ</a><a id="12668" class="Symbol">)</a> <a id="12670" class="Symbol">→</a> <a id="12672" href="plfa.Equality.html#12661" class="Bound">m</a> <a id="12674" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="12676" href="plfa.Equality.html#12663" class="Bound">n</a> <a id="12678" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="12680" href="plfa.Equality.html#12663" class="Bound">n</a> <a id="12682" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="12684" href="plfa.Equality.html#12661" class="Bound">m</a>
<a id="12686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12648" class="Function">+-comm′</a> <a id="12694" href="plfa.Equality.html#8049" class="InductiveConstructor">zero</a>    <a id="12702" href="plfa.Equality.html#12702" class="Bound">n</a>  <a id="12705" class="Keyword">rewrite</a> <a id="12713" href="plfa.Equality.html#8224" class="Postulate">+-identity</a> <a id="12724" href="plfa.Equality.html#12702" class="Bound">n</a>             <a id="12738" class="Symbol">=</a>  <a id="12741" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>
<a id="12746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12648" class="Function">+-comm′</a> <a id="12754" class="Symbol">(</a><a id="12755" href="plfa.Equality.html#8060" class="InductiveConstructor">suc</a> <a id="12759" href="plfa.Equality.html#12759" class="Bound">m</a><a id="12760" class="Symbol">)</a> <a id="12762" href="plfa.Equality.html#12762" class="Bound">n</a>  <a id="12765" class="Keyword">rewrite</a> <a id="12773" href="plfa.Equality.html#8264" class="Postulate">+-suc</a> <a id="12779" href="plfa.Equality.html#12762" class="Bound">n</a> <a id="12781" href="plfa.Equality.html#12759" class="Bound">m</a> <a id="12783" class="Symbol">|</a> <a id="12785" href="plfa.Equality.html#12648" class="Function">+-comm′</a> <a id="12793" href="plfa.Equality.html#12759" class="Bound">m</a> <a id="12795" href="plfa.Equality.html#12762" class="Bound">n</a>  <a id="12798" class="Symbol">=</a>  <a id="12801" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>
</pre>{% endraw %}This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.


## Rewriting expanded

The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction:
{% raw %}<pre class="Agda"><a id="even-comm′"></a><a id="13350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13350" class="Function">even-comm′</a> <a id="13361" class="Symbol">:</a> <a id="13363" class="Symbol">∀</a> <a id="13365" class="Symbol">(</a><a id="13366" href="plfa.Equality.html#13366" class="Bound">m</a> <a id="13368" href="plfa.Equality.html#13368" class="Bound">n</a> <a id="13370" class="Symbol">:</a> <a id="13372" href="plfa.Equality.html#8033" class="Datatype">ℕ</a><a id="13373" class="Symbol">)</a>
  <a id="13377" class="Symbol">→</a> <a id="13379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10149" class="Datatype">even</a> <a id="13384" class="Symbol">(</a><a id="13385" href="plfa.Equality.html#13366" class="Bound">m</a> <a id="13387" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="13389" href="plfa.Equality.html#13368" class="Bound">n</a><a id="13390" class="Symbol">)</a>
    <a id="13396" class="Comment">------------</a>
  <a id="13411" class="Symbol">→</a> <a id="13413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10149" class="Datatype">even</a> <a id="13418" class="Symbol">(</a><a id="13419" href="plfa.Equality.html#13368" class="Bound">n</a> <a id="13421" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="13423" href="plfa.Equality.html#13366" class="Bound">m</a><a id="13424" class="Symbol">)</a>
<a id="13426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13350" class="Function">even-comm′</a> <a id="13437" href="plfa.Equality.html#13437" class="Bound">m</a> <a id="13439" href="plfa.Equality.html#13439" class="Bound">n</a> <a id="13441" href="plfa.Equality.html#13441" class="Bound">ev</a> <a id="13444" class="Keyword">with</a>   <a id="13451" href="plfa.Equality.html#13437" class="Bound">m</a> <a id="13453" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="13455" href="plfa.Equality.html#13439" class="Bound">n</a>  <a id="13458" class="Symbol">|</a> <a id="13460" href="plfa.Equality.html#8658" class="Function">+-comm</a> <a id="13467" href="plfa.Equality.html#13437" class="Bound">m</a> <a id="13469" href="plfa.Equality.html#13439" class="Bound">n</a>
<a id="13471" class="Symbol">...</a>                  <a id="13492" class="Symbol">|</a> <a id="13494" class="DottedPattern Symbol">.(</a><a id="13496" class="DottedPattern Bound">n</a> <a id="13498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8074" class="DottedPattern Function Operator">+</a> <a id="13500" class="DottedPattern Bound">m</a><a id="13501" class="DottedPattern Symbol">)</a> <a id="13503" class="Symbol">|</a> <a id="13505" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>       <a id="13516" class="Symbol">=</a> <a id="13518" class="Bound">ev</a>
</pre>{% endraw %}In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of
`m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)

In this case, we can avoid rewrite by simply applying the substitution
function defined earlier:
{% raw %}<pre class="Agda"><a id="even-comm″"></a><a id="14665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14665" class="Function">even-comm″</a> <a id="14676" class="Symbol">:</a> <a id="14678" class="Symbol">∀</a> <a id="14680" class="Symbol">(</a><a id="14681" href="plfa.Equality.html#14681" class="Bound">m</a> <a id="14683" href="plfa.Equality.html#14683" class="Bound">n</a> <a id="14685" class="Symbol">:</a> <a id="14687" href="plfa.Equality.html#8033" class="Datatype">ℕ</a><a id="14688" class="Symbol">)</a>
  <a id="14692" class="Symbol">→</a> <a id="14694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10149" class="Datatype">even</a> <a id="14699" class="Symbol">(</a><a id="14700" href="plfa.Equality.html#14681" class="Bound">m</a> <a id="14702" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="14704" href="plfa.Equality.html#14683" class="Bound">n</a><a id="14705" class="Symbol">)</a>
    <a id="14711" class="Comment">------------</a>
  <a id="14726" class="Symbol">→</a> <a id="14728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10149" class="Datatype">even</a> <a id="14733" class="Symbol">(</a><a id="14734" href="plfa.Equality.html#14683" class="Bound">n</a> <a id="14736" href="plfa.Equality.html#8074" class="Function Operator">+</a> <a id="14738" href="plfa.Equality.html#14681" class="Bound">m</a><a id="14739" class="Symbol">)</a>
<a id="14741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14665" class="Function">even-comm″</a> <a id="14752" href="plfa.Equality.html#14752" class="Bound">m</a> <a id="14754" href="plfa.Equality.html#14754" class="Bound">n</a>  <a id="14757" class="Symbol">=</a>  <a id="14760" href="plfa.Equality.html#4773" class="Function">subst</a> <a id="14766" href="plfa.Equality.html#10149" class="Datatype">even</a> <a id="14771" class="Symbol">(</a><a id="14772" href="plfa.Equality.html#8658" class="Function">+-comm</a> <a id="14779" href="plfa.Equality.html#14752" class="Bound">m</a> <a id="14781" href="plfa.Equality.html#14754" class="Bound">n</a><a id="14782" class="Symbol">)</a>
</pre>{% endraw %}Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.


## Leibniz equality

The form of asserting equality that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equality.

Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.

Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`:
{% raw %}<pre class="Agda"><a id="_≐_"></a><a id="15913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15913" class="Function Operator">_≐_</a> <a id="15917" class="Symbol">:</a> <a id="15919" class="Symbol">∀</a> <a id="15921" class="Symbol">{</a><a id="15922" href="plfa.Equality.html#15922" class="Bound">A</a> <a id="15924" class="Symbol">:</a> <a id="15926" class="PrimitiveType">Set</a><a id="15929" class="Symbol">}</a> <a id="15931" class="Symbol">(</a><a id="15932" href="plfa.Equality.html#15932" class="Bound">x</a> <a id="15934" href="plfa.Equality.html#15934" class="Bound">y</a> <a id="15936" class="Symbol">:</a> <a id="15938" href="plfa.Equality.html#15922" class="Bound">A</a><a id="15939" class="Symbol">)</a> <a id="15941" class="Symbol">→</a> <a id="15943" class="PrimitiveType">Set₁</a>
<a id="15948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15913" class="Function Operator">_≐_</a> <a id="15952" class="Symbol">{</a><a id="15953" href="plfa.Equality.html#15953" class="Bound">A</a><a id="15954" class="Symbol">}</a> <a id="15956" href="plfa.Equality.html#15956" class="Bound">x</a> <a id="15958" href="plfa.Equality.html#15958" class="Bound">y</a> <a id="15960" class="Symbol">=</a> <a id="15962" class="Symbol">∀</a> <a id="15964" class="Symbol">(</a><a id="15965" href="plfa.Equality.html#15965" class="Bound">P</a> <a id="15967" class="Symbol">:</a> <a id="15969" href="plfa.Equality.html#15953" class="Bound">A</a> <a id="15971" class="Symbol">→</a> <a id="15973" class="PrimitiveType">Set</a><a id="15976" class="Symbol">)</a> <a id="15978" class="Symbol">→</a> <a id="15980" href="plfa.Equality.html#15965" class="Bound">P</a> <a id="15982" href="plfa.Equality.html#15956" class="Bound">x</a> <a id="15984" class="Symbol">→</a> <a id="15986" href="plfa.Equality.html#15965" class="Bound">P</a> <a id="15988" href="plfa.Equality.html#15958" class="Bound">y</a>
</pre>{% endraw %}We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.

This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.

Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition:
{% raw %}<pre class="Agda"><a id="refl-≐"></a><a id="16812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16812" class="Function">refl-≐</a> <a id="16819" class="Symbol">:</a> <a id="16821" class="Symbol">∀</a> <a id="16823" class="Symbol">{</a><a id="16824" href="plfa.Equality.html#16824" class="Bound">A</a> <a id="16826" class="Symbol">:</a> <a id="16828" class="PrimitiveType">Set</a><a id="16831" class="Symbol">}</a> <a id="16833" class="Symbol">{</a><a id="16834" href="plfa.Equality.html#16834" class="Bound">x</a> <a id="16836" class="Symbol">:</a> <a id="16838" href="plfa.Equality.html#16824" class="Bound">A</a><a id="16839" class="Symbol">}</a>
  <a id="16843" class="Symbol">→</a> <a id="16845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16834" class="Bound">x</a> <a id="16847" href="plfa.Equality.html#15913" class="Function Operator">≐</a> <a id="16849" href="plfa.Equality.html#16834" class="Bound">x</a>
<a id="16851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16812" class="Function">refl-≐</a> <a id="16858" href="plfa.Equality.html#16858" class="Bound">P</a> <a id="16860" href="plfa.Equality.html#16860" class="Bound">Px</a>  <a id="16864" class="Symbol">=</a>  <a id="16867" href="plfa.Equality.html#16860" class="Bound">Px</a>

<a id="trans-≐"></a><a id="16871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16871" class="Function">trans-≐</a> <a id="16879" class="Symbol">:</a> <a id="16881" class="Symbol">∀</a> <a id="16883" class="Symbol">{</a><a id="16884" href="plfa.Equality.html#16884" class="Bound">A</a> <a id="16886" class="Symbol">:</a> <a id="16888" class="PrimitiveType">Set</a><a id="16891" class="Symbol">}</a> <a id="16893" class="Symbol">{</a><a id="16894" href="plfa.Equality.html#16894" class="Bound">x</a> <a id="16896" href="plfa.Equality.html#16896" class="Bound">y</a> <a id="16898" href="plfa.Equality.html#16898" class="Bound">z</a> <a id="16900" class="Symbol">:</a> <a id="16902" href="plfa.Equality.html#16884" class="Bound">A</a><a id="16903" class="Symbol">}</a>
  <a id="16907" class="Symbol">→</a> <a id="16909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16894" class="Bound">x</a> <a id="16911" href="plfa.Equality.html#15913" class="Function Operator">≐</a> <a id="16913" href="plfa.Equality.html#16896" class="Bound">y</a>
  <a id="16917" class="Symbol">→</a> <a id="16919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16896" class="Bound">y</a> <a id="16921" href="plfa.Equality.html#15913" class="Function Operator">≐</a> <a id="16923" href="plfa.Equality.html#16898" class="Bound">z</a>
    <a id="16929" class="Comment">-----</a>
  <a id="16937" class="Symbol">→</a> <a id="16939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16894" class="Bound">x</a> <a id="16941" href="plfa.Equality.html#15913" class="Function Operator">≐</a> <a id="16943" href="plfa.Equality.html#16898" class="Bound">z</a>
<a id="16945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16871" class="Function">trans-≐</a> <a id="16953" href="plfa.Equality.html#16953" class="Bound">x≐y</a> <a id="16957" href="plfa.Equality.html#16957" class="Bound">y≐z</a> <a id="16961" href="plfa.Equality.html#16961" class="Bound">P</a> <a id="16963" href="plfa.Equality.html#16963" class="Bound">Px</a>  <a id="16967" class="Symbol">=</a>  <a id="16970" href="plfa.Equality.html#16957" class="Bound">y≐z</a> <a id="16974" href="plfa.Equality.html#16961" class="Bound">P</a> <a id="16976" class="Symbol">(</a><a id="16977" href="plfa.Equality.html#16953" class="Bound">x≐y</a> <a id="16981" href="plfa.Equality.html#16961" class="Bound">P</a> <a id="16983" href="plfa.Equality.html#16963" class="Bound">Px</a><a id="16985" class="Symbol">)</a>
</pre>{% endraw %}
Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well:
{% raw %}<pre class="Agda"><a id="sym-≐"></a><a id="17147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17147" class="Function">sym-≐</a> <a id="17153" class="Symbol">:</a> <a id="17155" class="Symbol">∀</a> <a id="17157" class="Symbol">{</a><a id="17158" href="plfa.Equality.html#17158" class="Bound">A</a> <a id="17160" class="Symbol">:</a> <a id="17162" class="PrimitiveType">Set</a><a id="17165" class="Symbol">}</a> <a id="17167" class="Symbol">{</a><a id="17168" href="plfa.Equality.html#17168" class="Bound">x</a> <a id="17170" href="plfa.Equality.html#17170" class="Bound">y</a> <a id="17172" class="Symbol">:</a> <a id="17174" href="plfa.Equality.html#17158" class="Bound">A</a><a id="17175" class="Symbol">}</a>
  <a id="17179" class="Symbol">→</a> <a id="17181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17168" class="Bound">x</a> <a id="17183" href="plfa.Equality.html#15913" class="Function Operator">≐</a> <a id="17185" href="plfa.Equality.html#17170" class="Bound">y</a>
    <a id="17191" class="Comment">-----</a>
  <a id="17199" class="Symbol">→</a> <a id="17201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17170" class="Bound">y</a> <a id="17203" href="plfa.Equality.html#15913" class="Function Operator">≐</a> <a id="17205" href="plfa.Equality.html#17168" class="Bound">x</a>
<a id="17207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17147" class="Function">sym-≐</a> <a id="17213" class="Symbol">{</a><a id="17214" href="plfa.Equality.html#17214" class="Bound">A</a><a id="17215" class="Symbol">}</a> <a id="17217" class="Symbol">{</a><a id="17218" href="plfa.Equality.html#17218" class="Bound">x</a><a id="17219" class="Symbol">}</a> <a id="17221" class="Symbol">{</a><a id="17222" href="plfa.Equality.html#17222" class="Bound">y</a><a id="17223" class="Symbol">}</a> <a id="17225" href="plfa.Equality.html#17225" class="Bound">x≐y</a> <a id="17229" href="plfa.Equality.html#17229" class="Bound">P</a>  <a id="17232" class="Symbol">=</a>  <a id="17235" href="plfa.Equality.html#17317" class="Function">Qy</a>
  <a id="17240" class="Keyword">where</a>
    <a id="17250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17250" class="Function">Q</a> <a id="17252" class="Symbol">:</a> <a id="17254" href="plfa.Equality.html#17214" class="Bound">A</a> <a id="17256" class="Symbol">→</a> <a id="17258" class="PrimitiveType">Set</a>
    <a id="17266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17250" class="Function">Q</a> <a id="17268" href="plfa.Equality.html#17268" class="Bound">z</a> <a id="17270" class="Symbol">=</a> <a id="17272" href="plfa.Equality.html#17229" class="Bound">P</a> <a id="17274" href="plfa.Equality.html#17268" class="Bound">z</a> <a id="17276" class="Symbol">→</a> <a id="17278" href="plfa.Equality.html#17229" class="Bound">P</a> <a id="17280" href="plfa.Equality.html#17218" class="Bound">x</a>
    <a id="17286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17286" class="Function">Qx</a> <a id="17289" class="Symbol">:</a> <a id="17291" href="plfa.Equality.html#17250" class="Function">Q</a> <a id="17293" href="plfa.Equality.html#17218" class="Bound">x</a>
    <a id="17299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17286" class="Function">Qx</a> <a id="17302" class="Symbol">=</a> <a id="17304" href="plfa.Equality.html#16812" class="Function">refl-≐</a> <a id="17311" href="plfa.Equality.html#17229" class="Bound">P</a>
    <a id="17317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17317" class="Function">Qy</a> <a id="17320" class="Symbol">:</a> <a id="17322" href="plfa.Equality.html#17250" class="Function">Q</a> <a id="17324" href="plfa.Equality.html#17222" class="Bound">y</a>
    <a id="17330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17317" class="Function">Qy</a> <a id="17333" class="Symbol">=</a> <a id="17335" href="plfa.Equality.html#17225" class="Bound">x≐y</a> <a id="17339" href="plfa.Equality.html#17250" class="Function">Q</a> <a id="17341" href="plfa.Equality.html#17286" class="Function">Qx</a>
</pre>{% endraw %}
Given `x ≐ y`, a specific `P`, we have to construct a proof that `P y`
implies `P x`.  To do so, we instantiate the equality with a predicate
`Q` such that `Q z` holds if `P z` implies `P x`.  The property `Q x`
is trivial by reflexivity, and hence `Q y` follows from `x ≐ y`.  But
`Q y` is exactly a proof of what we require, that `P y` implies `P x`.

We now show that Martin Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`:
{% raw %}<pre class="Agda"><a id="≡-implies-≐"></a><a id="18002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18002" class="Function">≡-implies-≐</a> <a id="18014" class="Symbol">:</a> <a id="18016" class="Symbol">∀</a> <a id="18018" class="Symbol">{</a><a id="18019" href="plfa.Equality.html#18019" class="Bound">A</a> <a id="18021" class="Symbol">:</a> <a id="18023" class="PrimitiveType">Set</a><a id="18026" class="Symbol">}</a> <a id="18028" class="Symbol">{</a><a id="18029" href="plfa.Equality.html#18029" class="Bound">x</a> <a id="18031" href="plfa.Equality.html#18031" class="Bound">y</a> <a id="18033" class="Symbol">:</a> <a id="18035" href="plfa.Equality.html#18019" class="Bound">A</a><a id="18036" class="Symbol">}</a>
  <a id="18040" class="Symbol">→</a> <a id="18042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18029" class="Bound">x</a> <a id="18044" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="18046" href="plfa.Equality.html#18031" class="Bound">y</a>
    <a id="18052" class="Comment">-----</a>
  <a id="18060" class="Symbol">→</a> <a id="18062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18029" class="Bound">x</a> <a id="18064" href="plfa.Equality.html#15913" class="Function Operator">≐</a> <a id="18066" href="plfa.Equality.html#18031" class="Bound">y</a>
<a id="18068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18002" class="Function">≡-implies-≐</a> <a id="18080" href="plfa.Equality.html#18080" class="Bound">x≡y</a> <a id="18084" href="plfa.Equality.html#18084" class="Bound">P</a>  <a id="18087" class="Symbol">=</a>  <a id="18090" href="plfa.Equality.html#4773" class="Function">subst</a> <a id="18096" href="plfa.Equality.html#18084" class="Bound">P</a> <a id="18098" href="plfa.Equality.html#18080" class="Bound">x≡y</a>
</pre>{% endraw %}This direction follows from substitution, which we showed earlier.

In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`:
{% raw %}<pre class="Agda"><a id="≐-implies-≡"></a><a id="18301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18301" class="Function">≐-implies-≡</a> <a id="18313" class="Symbol">:</a> <a id="18315" class="Symbol">∀</a> <a id="18317" class="Symbol">{</a><a id="18318" href="plfa.Equality.html#18318" class="Bound">A</a> <a id="18320" class="Symbol">:</a> <a id="18322" class="PrimitiveType">Set</a><a id="18325" class="Symbol">}</a> <a id="18327" class="Symbol">{</a><a id="18328" href="plfa.Equality.html#18328" class="Bound">x</a> <a id="18330" href="plfa.Equality.html#18330" class="Bound">y</a> <a id="18332" class="Symbol">:</a> <a id="18334" href="plfa.Equality.html#18318" class="Bound">A</a><a id="18335" class="Symbol">}</a>
  <a id="18339" class="Symbol">→</a> <a id="18341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18328" class="Bound">x</a> <a id="18343" href="plfa.Equality.html#15913" class="Function Operator">≐</a> <a id="18345" href="plfa.Equality.html#18330" class="Bound">y</a>
    <a id="18351" class="Comment">-----</a>
  <a id="18359" class="Symbol">→</a> <a id="18361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18328" class="Bound">x</a> <a id="18363" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="18365" href="plfa.Equality.html#18330" class="Bound">y</a>
<a id="18367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18301" class="Function">≐-implies-≡</a> <a id="18379" class="Symbol">{</a><a id="18380" href="plfa.Equality.html#18380" class="Bound">A</a><a id="18381" class="Symbol">}</a> <a id="18383" class="Symbol">{</a><a id="18384" href="plfa.Equality.html#18384" class="Bound">x</a><a id="18385" class="Symbol">}</a> <a id="18387" class="Symbol">{</a><a id="18388" href="plfa.Equality.html#18388" class="Bound">y</a><a id="18389" class="Symbol">}</a> <a id="18391" href="plfa.Equality.html#18391" class="Bound">x≐y</a>  <a id="18396" class="Symbol">=</a>  <a id="18399" href="plfa.Equality.html#18473" class="Function">Qy</a>
  <a id="18404" class="Keyword">where</a>
    <a id="18414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18414" class="Function">Q</a> <a id="18416" class="Symbol">:</a> <a id="18418" href="plfa.Equality.html#18380" class="Bound">A</a> <a id="18420" class="Symbol">→</a> <a id="18422" class="PrimitiveType">Set</a>
    <a id="18430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18414" class="Function">Q</a> <a id="18432" href="plfa.Equality.html#18432" class="Bound">z</a> <a id="18434" class="Symbol">=</a> <a id="18436" href="plfa.Equality.html#18384" class="Bound">x</a> <a id="18438" href="plfa.Equality.html#724" class="Datatype Operator">≡</a> <a id="18440" href="plfa.Equality.html#18432" class="Bound">z</a>
    <a id="18446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18446" class="Function">Qx</a> <a id="18449" class="Symbol">:</a> <a id="18451" href="plfa.Equality.html#18414" class="Function">Q</a> <a id="18453" href="plfa.Equality.html#18384" class="Bound">x</a>
    <a id="18459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18446" class="Function">Qx</a> <a id="18462" class="Symbol">=</a> <a id="18464" href="plfa.Equality.html#764" class="InductiveConstructor">refl</a>
    <a id="18473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18473" class="Function">Qy</a> <a id="18476" class="Symbol">:</a> <a id="18478" href="plfa.Equality.html#18414" class="Function">Q</a> <a id="18480" href="plfa.Equality.html#18388" class="Bound">y</a>
    <a id="18486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18473" class="Function">Qy</a> <a id="18489" class="Symbol">=</a> <a id="18491" href="plfa.Equality.html#18391" class="Bound">x≐y</a> <a id="18495" href="plfa.Equality.html#18414" class="Function">Q</a> <a id="18497" href="plfa.Equality.html#18446" class="Function">Qx</a>
</pre>{% endraw %}The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.

(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)


## Universe polymorphism {#unipoly}

As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?

The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following:
{% raw %}<pre class="Agda"><a id="19652" class="Keyword">open</a> <a id="19657" class="Keyword">import</a> <a id="19664" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="19670" class="Keyword">using</a> <a id="19676" class="Symbol">(</a><a id="19677" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Primitive.html#408" class="Postulate">Level</a><a id="19682" class="Symbol">;</a> <a id="19684" href="Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="19687" class="Symbol">)</a> <a id="19689" class="Keyword">renaming</a> <a id="19698" class="Symbol">(</a><a id="19699" href="Agda.Primitive.html#611" class="Primitive">zero</a> <a id="19704" class="Symbol">to</a> <a id="19707" href="Agda.Primitive.html#611" class="Primitive">lzero</a><a id="19712" class="Symbol">;</a> <a id="19714" href="Agda.Primitive.html#627" class="Primitive">suc</a> <a id="19718" class="Symbol">to</a> <a id="19721" href="Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="19725" class="Symbol">)</a>
</pre>{% endraw %}We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.

Levels are isomorphic to natural numbers, and have similar constructors:

    lzero : Level
    lsuc  : Level → Level

The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

and so on. There is also an operator

    _⊔_ : Level → Level → Level

that given two levels returns the larger of the two.

Here is the definition of equality, generalised to an arbitrary level:
{% raw %}<pre class="Agda"><a id="20293" class="Keyword">data</a> <a id="_≡′_"></a><a id="20298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20298" class="Datatype Operator">_≡′_</a> <a id="20303" class="Symbol">{</a><a id="20304" href="plfa.Equality.html#20304" class="Bound">ℓ</a> <a id="20306" class="Symbol">:</a> <a id="20308" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20313" class="Symbol">}</a> <a id="20315" class="Symbol">{</a><a id="20316" href="plfa.Equality.html#20316" class="Bound">A</a> <a id="20318" class="Symbol">:</a> <a id="20320" class="PrimitiveType">Set</a> <a id="20324" href="plfa.Equality.html#20304" class="Bound">ℓ</a><a id="20325" class="Symbol">}</a> <a id="20327" class="Symbol">(</a><a id="20328" href="plfa.Equality.html#20328" class="Bound">x</a> <a id="20330" class="Symbol">:</a> <a id="20332" href="plfa.Equality.html#20316" class="Bound">A</a><a id="20333" class="Symbol">)</a> <a id="20335" class="Symbol">:</a> <a id="20337" href="plfa.Equality.html#20316" class="Bound">A</a> <a id="20339" class="Symbol">→</a> <a id="20341" class="PrimitiveType">Set</a> <a id="20345" href="plfa.Equality.html#20304" class="Bound">ℓ</a> <a id="20347" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="20355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20355" class="InductiveConstructor">refl′</a> <a id="20361" class="Symbol">:</a> <a id="20363" href="plfa.Equality.html#20328" class="Bound">x</a> <a id="20365" href="plfa.Equality.html#20298" class="Datatype Operator">≡′</a> <a id="20368" href="plfa.Equality.html#20328" class="Bound">x</a>
</pre>{% endraw %}Similarly, here is the generalised definition of symmetry:
{% raw %}<pre class="Agda"><a id="sym′"></a><a id="20437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20437" class="Function">sym′</a> <a id="20442" class="Symbol">:</a> <a id="20444" class="Symbol">∀</a> <a id="20446" class="Symbol">{</a><a id="20447" href="plfa.Equality.html#20447" class="Bound">ℓ</a> <a id="20449" class="Symbol">:</a> <a id="20451" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20456" class="Symbol">}</a> <a id="20458" class="Symbol">{</a><a id="20459" href="plfa.Equality.html#20459" class="Bound">A</a> <a id="20461" class="Symbol">:</a> <a id="20463" class="PrimitiveType">Set</a> <a id="20467" href="plfa.Equality.html#20447" class="Bound">ℓ</a><a id="20468" class="Symbol">}</a> <a id="20470" class="Symbol">{</a><a id="20471" href="plfa.Equality.html#20471" class="Bound">x</a> <a id="20473" href="plfa.Equality.html#20473" class="Bound">y</a> <a id="20475" class="Symbol">:</a> <a id="20477" href="plfa.Equality.html#20459" class="Bound">A</a><a id="20478" class="Symbol">}</a>
  <a id="20482" class="Symbol">→</a> <a id="20484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20471" class="Bound">x</a> <a id="20486" href="plfa.Equality.html#20298" class="Datatype Operator">≡′</a> <a id="20489" href="plfa.Equality.html#20473" class="Bound">y</a>
    <a id="20495" class="Comment">------</a>
  <a id="20504" class="Symbol">→</a> <a id="20506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20473" class="Bound">y</a> <a id="20508" href="plfa.Equality.html#20298" class="Datatype Operator">≡′</a> <a id="20511" href="plfa.Equality.html#20471" class="Bound">x</a>
<a id="20513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20437" class="Function">sym′</a> <a id="20518" href="plfa.Equality.html#20355" class="InductiveConstructor">refl′</a> <a id="20524" class="Symbol">=</a> <a id="20526" href="plfa.Equality.html#20355" class="InductiveConstructor">refl′</a>
</pre>{% endraw %}For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.

Here is the generalised definition of Leibniz equality:
{% raw %}<pre class="Agda"><a id="_≐′_"></a><a id="20804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20804" class="Function Operator">_≐′_</a> <a id="20809" class="Symbol">:</a> <a id="20811" class="Symbol">∀</a> <a id="20813" class="Symbol">{</a><a id="20814" href="plfa.Equality.html#20814" class="Bound">ℓ</a> <a id="20816" class="Symbol">:</a> <a id="20818" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20823" class="Symbol">}</a> <a id="20825" class="Symbol">{</a><a id="20826" href="plfa.Equality.html#20826" class="Bound">A</a> <a id="20828" class="Symbol">:</a> <a id="20830" class="PrimitiveType">Set</a> <a id="20834" href="plfa.Equality.html#20814" class="Bound">ℓ</a><a id="20835" class="Symbol">}</a> <a id="20837" class="Symbol">(</a><a id="20838" href="plfa.Equality.html#20838" class="Bound">x</a> <a id="20840" href="plfa.Equality.html#20840" class="Bound">y</a> <a id="20842" class="Symbol">:</a> <a id="20844" href="plfa.Equality.html#20826" class="Bound">A</a><a id="20845" class="Symbol">)</a> <a id="20847" class="Symbol">→</a> <a id="20849" class="PrimitiveType">Set</a> <a id="20853" class="Symbol">(</a><a id="20854" href="Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="20859" href="plfa.Equality.html#20814" class="Bound">ℓ</a><a id="20860" class="Symbol">)</a>
<a id="20862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20804" class="Function Operator">_≐′_</a> <a id="20867" class="Symbol">{</a><a id="20868" href="plfa.Equality.html#20868" class="Bound">ℓ</a><a id="20869" class="Symbol">}</a> <a id="20871" class="Symbol">{</a><a id="20872" href="plfa.Equality.html#20872" class="Bound">A</a><a id="20873" class="Symbol">}</a> <a id="20875" href="plfa.Equality.html#20875" class="Bound">x</a> <a id="20877" href="plfa.Equality.html#20877" class="Bound">y</a> <a id="20879" class="Symbol">=</a> <a id="20881" class="Symbol">∀</a> <a id="20883" class="Symbol">(</a><a id="20884" href="plfa.Equality.html#20884" class="Bound">P</a> <a id="20886" class="Symbol">:</a> <a id="20888" href="plfa.Equality.html#20872" class="Bound">A</a> <a id="20890" class="Symbol">→</a> <a id="20892" class="PrimitiveType">Set</a> <a id="20896" href="plfa.Equality.html#20868" class="Bound">ℓ</a><a id="20897" class="Symbol">)</a> <a id="20899" class="Symbol">→</a> <a id="20901" href="plfa.Equality.html#20884" class="Bound">P</a> <a id="20903" href="plfa.Equality.html#20875" class="Bound">x</a> <a id="20905" class="Symbol">→</a> <a id="20907" href="plfa.Equality.html#20884" class="Bound">P</a> <a id="20909" href="plfa.Equality.html#20877" class="Bound">y</a>
</pre>{% endraw %}Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.

Further information on levels can be found in the [Agda Wiki][wiki].

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


## Standard library

Definitions similar to those in this chapter can be found in the
standard library:
{% raw %}<pre class="Agda"><a id="21358" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="21412" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="21476" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>
</pre>{% endraw %}Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.


## Unicode

This chapter uses the following unicode:

    ≡  U+2261  IDENTICAL TO (\==, \equiv)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ⊔  U+2294  SQUARE CUP (\lub)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
