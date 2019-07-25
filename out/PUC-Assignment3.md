---
src: tspl/PUC-Assignment3.lagda.md
title     : "PUC-Assignment3: PUC Assignment 3"
layout    : page
permalink : /PUC-Assignment3/
---

{% raw %}<pre class="Agda"><a id="109" class="Keyword">module</a> <a id="116" href="PUC-Assignment3.html" class="Module">PUC-Assignment3</a> <a id="132" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

Please ensure your files execute correctly under Agda!

## Imports

{% raw %}<pre class="Agda"><a id="558" class="Keyword">import</a> <a id="565" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="603" class="Symbol">as</a> <a id="606" class="Module">Eq</a>
<a id="609" class="Keyword">open</a> <a id="614" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="617" class="Keyword">using</a> <a id="623" class="Symbol">(</a><a id="624" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="627" class="Symbol">;</a> <a id="629" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="633" class="Symbol">;</a> <a id="635" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="639" class="Symbol">;</a> <a id="641" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="644" class="Symbol">)</a>
<a id="646" class="Keyword">open</a> <a id="651" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="666" class="Keyword">using</a> <a id="672" class="Symbol">(</a><a id="673" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="679" class="Symbol">;</a> <a id="681" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="686" class="Symbol">;</a> <a id="688" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="694" class="Symbol">;</a> <a id="696" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="698" class="Symbol">)</a>
<a id="700" class="Keyword">open</a> <a id="705" class="Keyword">import</a> <a id="712" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="727" class="Keyword">using</a> <a id="733" class="Symbol">(</a><a id="734" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="738" class="Symbol">;</a> <a id="740" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="744" class="Symbol">;</a> <a id="746" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="751" class="Symbol">;</a> <a id="753" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="754" class="Symbol">;</a> <a id="756" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="759" class="Symbol">;</a> <a id="761" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="764" class="Symbol">;</a> <a id="766" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="769" class="Symbol">)</a>
<a id="771" class="Keyword">open</a> <a id="776" class="Keyword">import</a> <a id="783" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="792" class="Keyword">using</a> <a id="798" class="Symbol">(</a><a id="799" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="800" class="Symbol">;</a> <a id="802" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="806" class="Symbol">;</a> <a id="808" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="811" class="Symbol">;</a> <a id="813" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="816" class="Symbol">;</a> <a id="818" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="821" class="Symbol">;</a> <a id="823" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="826" class="Symbol">;</a> <a id="828" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="831" class="Symbol">;</a> <a id="833" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="836" class="Symbol">;</a> <a id="838" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="841" class="Symbol">)</a>
<a id="843" class="Keyword">open</a> <a id="848" class="Keyword">import</a> <a id="855" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="875" class="Keyword">using</a>
  <a id="883" class="Symbol">(</a><a id="884" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="891" class="Symbol">;</a> <a id="893" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11679" class="Function">+-identityˡ</a><a id="904" class="Symbol">;</a> <a id="906" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="917" class="Symbol">;</a> <a id="919" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#18464" class="Function">*-assoc</a><a id="926" class="Symbol">;</a> <a id="928" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#17362" class="Function">*-identityˡ</a><a id="939" class="Symbol">;</a> <a id="941" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#17426" class="Function">*-identityʳ</a><a id="952" class="Symbol">)</a>
<a id="954" class="Keyword">open</a> <a id="959" class="Keyword">import</a> <a id="966" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="983" class="Keyword">using</a> <a id="989" class="Symbol">(</a><a id="990" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="992" class="Symbol">;</a> <a id="994" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="997" class="Symbol">;</a> <a id="999" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="1002" class="Symbol">;</a> <a id="1004" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1006" class="Symbol">)</a>
<a id="1008" class="Keyword">open</a> <a id="1013" class="Keyword">import</a> <a id="1020" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1033" class="Keyword">using</a> <a id="1039" class="Symbol">(</a><a id="1040" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1043" class="Symbol">;</a> <a id="1045" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="1046" class="Symbol">;</a> <a id="1048" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="1056" class="Symbol">)</a> <a id="1058" class="Keyword">renaming</a> <a id="1067" class="Symbol">(</a><a id="1068" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1072" class="Symbol">to</a> <a id="1075" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1080" class="Symbol">)</a>
<a id="1082" class="Keyword">open</a> <a id="1087" class="Keyword">import</a> <a id="1094" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1105" class="Keyword">using</a> <a id="1111" class="Symbol">(</a><a id="1112" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1113" class="Symbol">;</a> <a id="1115" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1121" class="Symbol">)</a>
<a id="1123" class="Keyword">open</a> <a id="1128" class="Keyword">import</a> <a id="1135" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="1144" class="Keyword">using</a> <a id="1150" class="Symbol">(</a><a id="1151" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="1154" class="Symbol">)</a>
<a id="1156" class="Keyword">open</a> <a id="1161" class="Keyword">import</a> <a id="1168" href="https://agda.github.io/agda-stdlib/v1.1/Algebra.Structures.html" class="Module">Algebra.Structures</a> <a id="1187" class="Keyword">using</a> <a id="1193" class="Symbol">(</a><a id="1194" href="https://agda.github.io/agda-stdlib/v1.1/Algebra.Structures.html#2215" class="Record">IsMonoid</a><a id="1202" class="Symbol">)</a>
<a id="1204" class="Keyword">open</a> <a id="1209" class="Keyword">import</a> <a id="1216" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="1222" class="Keyword">using</a> <a id="1228" class="Symbol">(</a><a id="1229" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="1234" class="Symbol">)</a>
<a id="1236" class="Keyword">open</a> <a id="1241" class="Keyword">import</a> <a id="1248" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html" class="Module">Relation.Unary</a> <a id="1263" class="Keyword">using</a> <a id="1269" class="Symbol">(</a><a id="1270" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html#3474" class="Function">Decidable</a><a id="1279" class="Symbol">)</a>
<a id="1281" class="Keyword">open</a> <a id="1286" class="Keyword">import</a> <a id="1293" href="plfa.Relations.html" class="Module">plfa.Relations</a> <a id="1308" class="Keyword">using</a> <a id="1314" class="Symbol">(</a><a id="1315" href="plfa.Relations.html#18100" class="Datatype Operator">_&lt;_</a><a id="1318" class="Symbol">;</a> <a id="1320" href="plfa.Relations.html#18127" class="InductiveConstructor">z&lt;s</a><a id="1323" class="Symbol">;</a> <a id="1325" href="plfa.Relations.html#18184" class="InductiveConstructor">s&lt;s</a><a id="1328" class="Symbol">)</a>
<a id="1330" class="Keyword">open</a> <a id="1335" class="Keyword">import</a> <a id="1342" href="plfa.Isomorphism.html" class="Module">plfa.Isomorphism</a> <a id="1359" class="Keyword">using</a> <a id="1365" class="Symbol">(</a><a id="1366" href="plfa.Isomorphism.html#3955" class="Record Operator">_≃_</a><a id="1369" class="Symbol">;</a> <a id="1371" href="plfa.Isomorphism.html#6602" class="Function">≃-sym</a><a id="1376" class="Symbol">;</a> <a id="1378" href="plfa.Isomorphism.html#6927" class="Function">≃-trans</a><a id="1385" class="Symbol">;</a> <a id="1387" href="plfa.Isomorphism.html#8776" class="Record Operator">_≲_</a><a id="1390" class="Symbol">;</a> <a id="1392" href="plfa.Isomorphism.html#2663" class="Postulate">extensionality</a><a id="1406" class="Symbol">)</a>
<a id="1408" class="Keyword">open</a> <a id="1413" href="plfa.Isomorphism.html#8011" class="Module">plfa.Isomorphism.≃-Reasoning</a>
<a id="1442" class="Keyword">open</a> <a id="1447" class="Keyword">import</a> <a id="1454" href="plfa.Lists.html" class="Module">plfa.Lists</a> <a id="1465" class="Keyword">using</a> <a id="1471" class="Symbol">(</a><a id="1472" href="plfa.Lists.html#1055" class="Datatype">List</a><a id="1476" class="Symbol">;</a> <a id="1478" href="plfa.Lists.html#1084" class="InductiveConstructor">[]</a><a id="1480" class="Symbol">;</a> <a id="1482" href="plfa.Lists.html#1099" class="InductiveConstructor Operator">_∷_</a><a id="1485" class="Symbol">;</a> <a id="1487" href="plfa.Lists.html#2815" class="Operator">[_]</a><a id="1490" class="Symbol">;</a> <a id="1492" href="plfa.Lists.html#2838" class="Operator">[_,_]</a><a id="1497" class="Symbol">;</a> <a id="1499" href="plfa.Lists.html#2869" class="Operator">[_,_,_]</a><a id="1506" class="Symbol">;</a> <a id="1508" href="plfa.Lists.html#2908" class="Operator">[_,_,_,_]</a><a id="1517" class="Symbol">;</a>
  <a id="1521" href="plfa.Lists.html#3455" class="Function Operator">_++_</a><a id="1525" class="Symbol">;</a> <a id="1527" href="plfa.Lists.html#8294" class="Function">reverse</a><a id="1534" class="Symbol">;</a> <a id="1536" href="plfa.Lists.html#12979" class="Function">map</a><a id="1539" class="Symbol">;</a> <a id="1541" href="plfa.Lists.html#15448" class="Function">foldr</a><a id="1546" class="Symbol">;</a> <a id="1548" href="plfa.Lists.html#16343" class="Function">sum</a><a id="1551" class="Symbol">;</a> <a id="1553" href="plfa.Lists.html#21045" class="Datatype">All</a><a id="1556" class="Symbol">;</a> <a id="1558" href="plfa.Lists.html#22498" class="Datatype">Any</a><a id="1561" class="Symbol">;</a> <a id="1563" href="plfa.Lists.html#22549" class="InductiveConstructor">here</a><a id="1567" class="Symbol">;</a> <a id="1569" href="plfa.Lists.html#22606" class="InductiveConstructor">there</a><a id="1574" class="Symbol">;</a> <a id="1576" href="plfa.Lists.html#22920" class="Function Operator">_∈_</a><a id="1579" class="Symbol">)</a>
<a id="1581" class="Keyword">open</a> <a id="1586" class="Keyword">import</a> <a id="1593" href="plfa.Lambda.html" class="Module">plfa.Lambda</a> <a id="1605" class="Keyword">hiding</a> <a id="1612" class="Symbol">(</a><a id="1613" href="plfa.Lambda.html#7317" class="Function Operator">ƛ′_⇒_</a><a id="1618" class="Symbol">;</a> <a id="1620" href="plfa.Lambda.html#7438" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a><a id="1641" class="Symbol">;</a> <a id="1643" href="plfa.Lambda.html#7652" class="Function Operator">μ′_⇒_</a><a id="1648" class="Symbol">;</a> <a id="1650" href="plfa.Lambda.html#7836" class="Function">plus′</a><a id="1655" class="Symbol">)</a>
<a id="1657" class="Keyword">open</a> <a id="1662" class="Keyword">import</a> <a id="1669" href="plfa.Properties.html" class="Module">plfa.Properties</a> <a id="1685" class="Keyword">hiding</a> <a id="1692" class="Symbol">(</a><a id="1693" href="plfa.Properties.html#11712" class="Postulate">value?</a><a id="1699" class="Symbol">;</a> <a id="1701" href="plfa.Properties.html#41496" class="Postulate">unstuck</a><a id="1708" class="Symbol">;</a> <a id="1710" href="plfa.Properties.html#41696" class="Postulate">preserves</a><a id="1719" class="Symbol">;</a> <a id="1721" href="plfa.Properties.html#41933" class="Postulate">wttdgs</a><a id="1727" class="Symbol">)</a>
</pre>{% endraw %}
## Lambda

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.


#### Exercise `primed` (stretch)

We can make examples with lambda terms slightly easier to write
by adding the following definitions.
{% raw %}<pre class="Agda"><a id="ƛ′_⇒_"></a><a id="2000" href="PUC-Assignment3.html#2000" class="Function Operator">ƛ′_⇒_</a> <a id="2006" class="Symbol">:</a> <a id="2008" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="2013" class="Symbol">→</a> <a id="2015" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="2020" class="Symbol">→</a> <a id="2022" href="plfa.Lambda.html#3766" class="Datatype">Term</a>
<a id="2027" href="PUC-Assignment3.html#2000" class="Function Operator">ƛ′</a> <a id="2030" class="Symbol">(</a><a id="2031" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="2033" href="PUC-Assignment3.html#2033" class="Bound">x</a><a id="2034" class="Symbol">)</a> <a id="2036" href="PUC-Assignment3.html#2000" class="Function Operator">⇒</a> <a id="2038" href="PUC-Assignment3.html#2038" class="Bound">N</a>  <a id="2041" class="Symbol">=</a>  <a id="2044" href="plfa.Lambda.html#3824" class="InductiveConstructor Operator">ƛ</a> <a id="2046" href="PUC-Assignment3.html#2033" class="Bound">x</a> <a id="2048" href="plfa.Lambda.html#3824" class="InductiveConstructor Operator">⇒</a> <a id="2050" href="PUC-Assignment3.html#2038" class="Bound">N</a>
<a id="2052" href="PUC-Assignment3.html#2000" class="CatchallClause Function Operator">ƛ′</a><a id="2054" class="CatchallClause"> </a><a id="2055" class="CatchallClause Symbol">_</a><a id="2056" class="CatchallClause"> </a><a id="2057" href="PUC-Assignment3.html#2000" class="CatchallClause Function Operator">⇒</a><a id="2058" class="CatchallClause"> </a><a id="2059" class="CatchallClause Symbol">_</a>      <a id="2066" class="Symbol">=</a>  <a id="2069" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="2076" href="PUC-Assignment3.html#2105" class="Postulate">impossible</a>
  <a id="2089" class="Keyword">where</a> <a id="2095" class="Keyword">postulate</a> <a id="2105" href="PUC-Assignment3.html#2105" class="Postulate">impossible</a> <a id="2116" class="Symbol">:</a> <a id="2118" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="2121" href="PUC-Assignment3.html#2121" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="2143" class="Symbol">:</a> <a id="2145" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="2150" class="Symbol">→</a> <a id="2152" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="2157" class="Symbol">→</a> <a id="2159" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="2164" class="Symbol">→</a> <a id="2166" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="2171" class="Symbol">→</a> <a id="2173" href="plfa.Lambda.html#3766" class="Datatype">Term</a>
<a id="2178" href="PUC-Assignment3.html#2121" class="Function Operator">case′</a> <a id="2184" href="PUC-Assignment3.html#2184" class="Bound">L</a> <a id="2186" href="PUC-Assignment3.html#2121" class="Function Operator">[zero⇒</a> <a id="2193" href="PUC-Assignment3.html#2193" class="Bound">M</a> <a id="2195" href="PUC-Assignment3.html#2121" class="Function Operator">|suc</a> <a id="2200" class="Symbol">(</a><a id="2201" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="2203" href="PUC-Assignment3.html#2203" class="Bound">x</a><a id="2204" class="Symbol">)</a> <a id="2206" href="PUC-Assignment3.html#2121" class="Function Operator">⇒</a> <a id="2208" href="PUC-Assignment3.html#2208" class="Bound">N</a> <a id="2210" href="PUC-Assignment3.html#2121" class="Function Operator">]</a>  <a id="2213" class="Symbol">=</a>  <a id="2216" href="plfa.Lambda.html#3993" class="InductiveConstructor Operator">case</a> <a id="2221" href="PUC-Assignment3.html#2184" class="Bound">L</a> <a id="2223" href="plfa.Lambda.html#3993" class="InductiveConstructor Operator">[zero⇒</a> <a id="2230" href="PUC-Assignment3.html#2193" class="Bound">M</a> <a id="2232" href="plfa.Lambda.html#3993" class="InductiveConstructor Operator">|suc</a> <a id="2237" href="PUC-Assignment3.html#2203" class="Bound">x</a> <a id="2239" href="plfa.Lambda.html#3993" class="InductiveConstructor Operator">⇒</a> <a id="2241" href="PUC-Assignment3.html#2208" class="Bound">N</a> <a id="2243" href="plfa.Lambda.html#3993" class="InductiveConstructor Operator">]</a>
<a id="2245" href="PUC-Assignment3.html#2121" class="CatchallClause Function Operator">case′</a><a id="2250" class="CatchallClause"> </a><a id="2251" class="CatchallClause Symbol">_</a><a id="2252" class="CatchallClause"> </a><a id="2253" href="PUC-Assignment3.html#2121" class="CatchallClause Function Operator">[zero⇒</a><a id="2259" class="CatchallClause"> </a><a id="2260" class="CatchallClause Symbol">_</a><a id="2261" class="CatchallClause"> </a><a id="2262" href="PUC-Assignment3.html#2121" class="CatchallClause Function Operator">|suc</a><a id="2266" class="CatchallClause"> </a><a id="2267" class="CatchallClause Symbol">_</a><a id="2268" class="CatchallClause"> </a><a id="2269" href="PUC-Assignment3.html#2121" class="CatchallClause Function Operator">⇒</a><a id="2270" class="CatchallClause"> </a><a id="2271" class="CatchallClause Symbol">_</a><a id="2272" class="CatchallClause"> </a><a id="2273" href="PUC-Assignment3.html#2121" class="CatchallClause Function Operator">]</a>      <a id="2280" class="Symbol">=</a>  <a id="2283" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="2290" href="PUC-Assignment3.html#2319" class="Postulate">impossible</a>
  <a id="2303" class="Keyword">where</a> <a id="2309" class="Keyword">postulate</a> <a id="2319" href="PUC-Assignment3.html#2319" class="Postulate">impossible</a> <a id="2330" class="Symbol">:</a> <a id="2332" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="2335" href="PUC-Assignment3.html#2335" class="Function Operator">μ′_⇒_</a> <a id="2341" class="Symbol">:</a> <a id="2343" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="2348" class="Symbol">→</a> <a id="2350" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="2355" class="Symbol">→</a> <a id="2357" href="plfa.Lambda.html#3766" class="Datatype">Term</a>
<a id="2362" href="PUC-Assignment3.html#2335" class="Function Operator">μ′</a> <a id="2365" class="Symbol">(</a><a id="2366" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="2368" href="PUC-Assignment3.html#2368" class="Bound">x</a><a id="2369" class="Symbol">)</a> <a id="2371" href="PUC-Assignment3.html#2335" class="Function Operator">⇒</a> <a id="2373" href="PUC-Assignment3.html#2373" class="Bound">N</a>  <a id="2376" class="Symbol">=</a>  <a id="2379" href="plfa.Lambda.html#4053" class="InductiveConstructor Operator">μ</a> <a id="2381" href="PUC-Assignment3.html#2368" class="Bound">x</a> <a id="2383" href="plfa.Lambda.html#4053" class="InductiveConstructor Operator">⇒</a> <a id="2385" href="PUC-Assignment3.html#2373" class="Bound">N</a>
<a id="2387" href="PUC-Assignment3.html#2335" class="CatchallClause Function Operator">μ′</a><a id="2389" class="CatchallClause"> </a><a id="2390" class="CatchallClause Symbol">_</a><a id="2391" class="CatchallClause"> </a><a id="2392" href="PUC-Assignment3.html#2335" class="CatchallClause Function Operator">⇒</a><a id="2393" class="CatchallClause"> </a><a id="2394" class="CatchallClause Symbol">_</a>      <a id="2401" class="Symbol">=</a>  <a id="2404" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="2411" href="PUC-Assignment3.html#2440" class="Postulate">impossible</a>
  <a id="2424" class="Keyword">where</a> <a id="2430" class="Keyword">postulate</a> <a id="2440" href="PUC-Assignment3.html#2440" class="Postulate">impossible</a> <a id="2451" class="Symbol">:</a> <a id="2453" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}The definition of `plus` can now be written as follows.
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="2519" href="PUC-Assignment3.html#2519" class="Function">plus′</a> <a id="2525" class="Symbol">:</a> <a id="2527" href="plfa.Lambda.html#3766" class="Datatype">Term</a>
<a id="2532" href="PUC-Assignment3.html#2519" class="Function">plus′</a> <a id="2538" class="Symbol">=</a> <a id="2540" href="PUC-Assignment3.html#2335" class="Function Operator">μ′</a> <a id="2543" href="PUC-Assignment3.html#2650" class="Function">+</a> <a id="2545" href="PUC-Assignment3.html#2335" class="Function Operator">⇒</a> <a id="2547" href="PUC-Assignment3.html#2000" class="Function Operator">ƛ′</a> <a id="2550" href="PUC-Assignment3.html#2664" class="Function">m</a> <a id="2552" href="PUC-Assignment3.html#2000" class="Function Operator">⇒</a> <a id="2554" href="PUC-Assignment3.html#2000" class="Function Operator">ƛ′</a> <a id="2557" href="PUC-Assignment3.html#2678" class="Function">n</a> <a id="2559" href="PUC-Assignment3.html#2000" class="Function Operator">⇒</a>
          <a id="2571" href="PUC-Assignment3.html#2121" class="Function Operator">case′</a> <a id="2577" href="PUC-Assignment3.html#2664" class="Function">m</a>
            <a id="2591" href="PUC-Assignment3.html#2121" class="Function Operator">[zero⇒</a> <a id="2598" href="PUC-Assignment3.html#2678" class="Function">n</a>
            <a id="2612" href="PUC-Assignment3.html#2121" class="Function Operator">|suc</a> <a id="2617" href="PUC-Assignment3.html#2664" class="Function">m</a> <a id="2619" href="PUC-Assignment3.html#2121" class="Function Operator">⇒</a> <a id="2621" href="plfa.Lambda.html#3952" class="InductiveConstructor Operator">`suc</a> <a id="2626" class="Symbol">(</a><a id="2627" href="PUC-Assignment3.html#2650" class="Function">+</a> <a id="2629" href="plfa.Lambda.html#3870" class="InductiveConstructor Operator">·</a> <a id="2631" href="PUC-Assignment3.html#2664" class="Function">m</a> <a id="2633" href="plfa.Lambda.html#3870" class="InductiveConstructor Operator">·</a> <a id="2635" href="PUC-Assignment3.html#2678" class="Function">n</a><a id="2636" class="Symbol">)</a> <a id="2638" href="PUC-Assignment3.html#2121" class="Function Operator">]</a>
  <a id="2642" class="Keyword">where</a>
  <a id="2650" href="PUC-Assignment3.html#2650" class="Function">+</a>  <a id="2653" class="Symbol">=</a>  <a id="2656" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="2658" class="String">&quot;+&quot;</a>
  <a id="2664" href="PUC-Assignment3.html#2664" class="Function">m</a>  <a id="2667" class="Symbol">=</a>  <a id="2670" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="2672" class="String">&quot;m&quot;</a>
  <a id="2678" href="PUC-Assignment3.html#2678" class="Function">n</a>  <a id="2681" class="Symbol">=</a>  <a id="2684" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="2686" class="String">&quot;n&quot;</a>
</pre>{% endraw %}Write out the definition of multiplication in the same style.

#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a with clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.


#### Exercise `—↠≲—↠′`

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?


#### Exercise `plus-example`

Write out the reduction sequence demonstrating that one plus one is two.


#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well-typed.


## Properties


#### Exercise `Progress-≃`

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.


#### Exercise `progress′`

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.


#### Exercise `value?`

Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value.
{% raw %}<pre class="Agda"><a id="3829" class="Keyword">postulate</a>
  <a id="value?"></a><a id="3841" href="PUC-Assignment3.html#3841" class="Postulate">value?</a> <a id="3848" class="Symbol">:</a> <a id="3850" class="Symbol">∀</a> <a id="3852" class="Symbol">{</a><a id="3853" href="PUC-Assignment3.html#3853" class="Bound">A</a> <a id="3855" href="PUC-Assignment3.html#3855" class="Bound">M</a><a id="3856" class="Symbol">}</a> <a id="3858" class="Symbol">→</a> <a id="3860" href="plfa.Lambda.html#30706" class="InductiveConstructor">∅</a> <a id="3862" href="plfa.Lambda.html#33069" class="Datatype Operator">⊢</a> <a id="3864" href="PUC-Assignment3.html#3855" class="Bound">M</a> <a id="3866" href="plfa.Lambda.html#33069" class="Datatype Operator">⦂</a> <a id="3868" href="PUC-Assignment3.html#3853" class="Bound">A</a> <a id="3870" class="Symbol">→</a> <a id="3872" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="3876" class="Symbol">(</a><a id="3877" href="plfa.Lambda.html#11539" class="Datatype">Value</a> <a id="3883" href="PUC-Assignment3.html#3855" class="Bound">M</a><a id="3884" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.


#### Exercise `mul-example` (recommended)

Using the evaluator, confirm that two times two is four.


#### Exercise: `progress-preservation`

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.


#### Exercise `subject-expansion`

We say that `M` _reduces_ to `N` if `M —→ N`,
and conversely that `M` _expands_ to `N` if `N —→ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.


#### Exercise `stuck`

Give an example of an ill-typed term that does get stuck.


#### Exercise `unstuck` (recommended)

Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.
