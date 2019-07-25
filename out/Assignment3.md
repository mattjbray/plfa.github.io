---
src: tspl/Assignment3.lagda.md
title     : "Assignment3: TSPL Assignment 3"
layout    : page
permalink : /Assignment3/
---

{% raw %}<pre class="Agda"><a id="102" class="Keyword">module</a> <a id="109" href="Assignment3.html" class="Module">Assignment3</a> <a id="121" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

<!-- This assignment is due **4pm Thursday 1 November** (Week 7). -->

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

<!-- Submit your homework using the "submit" command. -->
Please ensure your files execute correctly under Agda!

## Imports

{% raw %}<pre class="Agda"><a id="676" class="Keyword">import</a> <a id="683" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="721" class="Symbol">as</a> <a id="724" class="Module">Eq</a>
<a id="727" class="Keyword">open</a> <a id="732" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="735" class="Keyword">using</a> <a id="741" class="Symbol">(</a><a id="742" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="745" class="Symbol">;</a> <a id="747" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="751" class="Symbol">;</a> <a id="753" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="757" class="Symbol">;</a> <a id="759" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="762" class="Symbol">)</a>
<a id="764" class="Keyword">open</a> <a id="769" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="784" class="Keyword">using</a> <a id="790" class="Symbol">(</a><a id="791" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="797" class="Symbol">;</a> <a id="799" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="804" class="Symbol">;</a> <a id="806" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="812" class="Symbol">;</a> <a id="814" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="816" class="Symbol">)</a>
<a id="818" class="Keyword">open</a> <a id="823" class="Keyword">import</a> <a id="830" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="845" class="Keyword">using</a> <a id="851" class="Symbol">(</a><a id="852" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="856" class="Symbol">;</a> <a id="858" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="862" class="Symbol">;</a> <a id="864" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="869" class="Symbol">;</a> <a id="871" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="872" class="Symbol">;</a> <a id="874" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="877" class="Symbol">;</a> <a id="879" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="882" class="Symbol">;</a> <a id="884" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="887" class="Symbol">)</a>
<a id="889" class="Keyword">open</a> <a id="894" class="Keyword">import</a> <a id="901" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="910" class="Keyword">using</a> <a id="916" class="Symbol">(</a><a id="917" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="918" class="Symbol">;</a> <a id="920" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="924" class="Symbol">;</a> <a id="926" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="929" class="Symbol">;</a> <a id="931" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="934" class="Symbol">;</a> <a id="936" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="939" class="Symbol">;</a> <a id="941" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="944" class="Symbol">;</a> <a id="946" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="949" class="Symbol">;</a> <a id="951" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="954" class="Symbol">;</a> <a id="956" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="959" class="Symbol">)</a>
<a id="961" class="Keyword">open</a> <a id="966" class="Keyword">import</a> <a id="973" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="993" class="Keyword">using</a>
  <a id="1001" class="Symbol">(</a><a id="1002" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="1009" class="Symbol">;</a> <a id="1011" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11679" class="Function">+-identityˡ</a><a id="1022" class="Symbol">;</a> <a id="1024" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="1035" class="Symbol">;</a> <a id="1037" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#18464" class="Function">*-assoc</a><a id="1044" class="Symbol">;</a> <a id="1046" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#17362" class="Function">*-identityˡ</a><a id="1057" class="Symbol">;</a> <a id="1059" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#17426" class="Function">*-identityʳ</a><a id="1070" class="Symbol">)</a>
<a id="1072" class="Keyword">open</a> <a id="1077" class="Keyword">import</a> <a id="1084" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1101" class="Keyword">using</a> <a id="1107" class="Symbol">(</a><a id="1108" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1110" class="Symbol">;</a> <a id="1112" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="1115" class="Symbol">;</a> <a id="1117" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="1120" class="Symbol">;</a> <a id="1122" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1124" class="Symbol">)</a>
<a id="1126" class="Keyword">open</a> <a id="1131" class="Keyword">import</a> <a id="1138" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1151" class="Keyword">using</a> <a id="1157" class="Symbol">(</a><a id="1158" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1161" class="Symbol">;</a> <a id="1163" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="1164" class="Symbol">;</a> <a id="1166" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="1174" class="Symbol">)</a> <a id="1176" class="Keyword">renaming</a> <a id="1185" class="Symbol">(</a><a id="1186" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1190" class="Symbol">to</a> <a id="1193" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1198" class="Symbol">)</a>
<a id="1200" class="Keyword">open</a> <a id="1205" class="Keyword">import</a> <a id="1212" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1223" class="Keyword">using</a> <a id="1229" class="Symbol">(</a><a id="1230" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1231" class="Symbol">;</a> <a id="1233" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1239" class="Symbol">)</a>
<a id="1241" class="Keyword">open</a> <a id="1246" class="Keyword">import</a> <a id="1253" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="1262" class="Keyword">using</a> <a id="1268" class="Symbol">(</a><a id="1269" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="1272" class="Symbol">)</a>
<a id="1274" class="Keyword">open</a> <a id="1279" class="Keyword">import</a> <a id="1286" href="https://agda.github.io/agda-stdlib/v1.1/Algebra.Structures.html" class="Module">Algebra.Structures</a> <a id="1305" class="Keyword">using</a> <a id="1311" class="Symbol">(</a><a id="1312" href="https://agda.github.io/agda-stdlib/v1.1/Algebra.Structures.html#2215" class="Record">IsMonoid</a><a id="1320" class="Symbol">)</a>
<a id="1322" class="Keyword">open</a> <a id="1327" class="Keyword">import</a> <a id="1334" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="1340" class="Keyword">using</a> <a id="1346" class="Symbol">(</a><a id="1347" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="1352" class="Symbol">)</a>
<a id="1354" class="Keyword">open</a> <a id="1359" class="Keyword">import</a> <a id="1366" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html" class="Module">Relation.Unary</a> <a id="1381" class="Keyword">using</a> <a id="1387" class="Symbol">(</a><a id="1388" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html#3474" class="Function">Decidable</a><a id="1397" class="Symbol">)</a>
<a id="1399" class="Keyword">open</a> <a id="1404" class="Keyword">import</a> <a id="1411" href="plfa.Relations.html" class="Module">plfa.Relations</a> <a id="1426" class="Keyword">using</a> <a id="1432" class="Symbol">(</a><a id="1433" href="plfa.Relations.html#18100" class="Datatype Operator">_&lt;_</a><a id="1436" class="Symbol">;</a> <a id="1438" href="plfa.Relations.html#18127" class="InductiveConstructor">z&lt;s</a><a id="1441" class="Symbol">;</a> <a id="1443" href="plfa.Relations.html#18184" class="InductiveConstructor">s&lt;s</a><a id="1446" class="Symbol">)</a>
<a id="1448" class="Keyword">open</a> <a id="1453" class="Keyword">import</a> <a id="1460" href="plfa.Isomorphism.html" class="Module">plfa.Isomorphism</a> <a id="1477" class="Keyword">using</a> <a id="1483" class="Symbol">(</a><a id="1484" href="plfa.Isomorphism.html#3955" class="Record Operator">_≃_</a><a id="1487" class="Symbol">;</a> <a id="1489" href="plfa.Isomorphism.html#6602" class="Function">≃-sym</a><a id="1494" class="Symbol">;</a> <a id="1496" href="plfa.Isomorphism.html#6927" class="Function">≃-trans</a><a id="1503" class="Symbol">;</a> <a id="1505" href="plfa.Isomorphism.html#8776" class="Record Operator">_≲_</a><a id="1508" class="Symbol">;</a> <a id="1510" href="plfa.Isomorphism.html#2663" class="Postulate">extensionality</a><a id="1524" class="Symbol">)</a>
<a id="1526" class="Keyword">open</a> <a id="1531" href="plfa.Isomorphism.html#8011" class="Module">plfa.Isomorphism.≃-Reasoning</a>
<a id="1560" class="Keyword">open</a> <a id="1565" class="Keyword">import</a> <a id="1572" href="plfa.Lists.html" class="Module">plfa.Lists</a> <a id="1583" class="Keyword">using</a> <a id="1589" class="Symbol">(</a><a id="1590" href="plfa.Lists.html#1055" class="Datatype">List</a><a id="1594" class="Symbol">;</a> <a id="1596" href="plfa.Lists.html#1084" class="InductiveConstructor">[]</a><a id="1598" class="Symbol">;</a> <a id="1600" href="plfa.Lists.html#1099" class="InductiveConstructor Operator">_∷_</a><a id="1603" class="Symbol">;</a> <a id="1605" href="plfa.Lists.html#2815" class="Operator">[_]</a><a id="1608" class="Symbol">;</a> <a id="1610" href="plfa.Lists.html#2838" class="Operator">[_,_]</a><a id="1615" class="Symbol">;</a> <a id="1617" href="plfa.Lists.html#2869" class="Operator">[_,_,_]</a><a id="1624" class="Symbol">;</a> <a id="1626" href="plfa.Lists.html#2908" class="Operator">[_,_,_,_]</a><a id="1635" class="Symbol">;</a>
  <a id="1639" href="plfa.Lists.html#3455" class="Function Operator">_++_</a><a id="1643" class="Symbol">;</a> <a id="1645" href="plfa.Lists.html#8294" class="Function">reverse</a><a id="1652" class="Symbol">;</a> <a id="1654" href="plfa.Lists.html#12979" class="Function">map</a><a id="1657" class="Symbol">;</a> <a id="1659" href="plfa.Lists.html#15448" class="Function">foldr</a><a id="1664" class="Symbol">;</a> <a id="1666" href="plfa.Lists.html#16343" class="Function">sum</a><a id="1669" class="Symbol">;</a> <a id="1671" href="plfa.Lists.html#21045" class="Datatype">All</a><a id="1674" class="Symbol">;</a> <a id="1676" href="plfa.Lists.html#22498" class="Datatype">Any</a><a id="1679" class="Symbol">;</a> <a id="1681" href="plfa.Lists.html#22549" class="InductiveConstructor">here</a><a id="1685" class="Symbol">;</a> <a id="1687" href="plfa.Lists.html#22606" class="InductiveConstructor">there</a><a id="1692" class="Symbol">;</a> <a id="1694" href="plfa.Lists.html#22920" class="Function Operator">_∈_</a><a id="1697" class="Symbol">)</a>
<a id="1699" class="Keyword">open</a> <a id="1704" class="Keyword">import</a> <a id="1711" href="plfa.Lambda.html" class="Module">plfa.Lambda</a> <a id="1723" class="Keyword">hiding</a> <a id="1730" class="Symbol">(</a><a id="1731" href="plfa.Lambda.html#7317" class="Function Operator">ƛ′_⇒_</a><a id="1736" class="Symbol">;</a> <a id="1738" href="plfa.Lambda.html#7438" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a><a id="1759" class="Symbol">;</a> <a id="1761" href="plfa.Lambda.html#7652" class="Function Operator">μ′_⇒_</a><a id="1766" class="Symbol">;</a> <a id="1768" href="plfa.Lambda.html#7836" class="Function">plus′</a><a id="1773" class="Symbol">)</a>
<a id="1775" class="Keyword">open</a> <a id="1780" class="Keyword">import</a> <a id="1787" href="plfa.Properties.html" class="Module">plfa.Properties</a> <a id="1803" class="Keyword">hiding</a> <a id="1810" class="Symbol">(</a><a id="1811" href="plfa.Properties.html#11712" class="Postulate">value?</a><a id="1817" class="Symbol">;</a> <a id="1819" href="plfa.Properties.html#41496" class="Postulate">unstuck</a><a id="1826" class="Symbol">;</a> <a id="1828" href="plfa.Properties.html#41696" class="Postulate">preserves</a><a id="1837" class="Symbol">;</a> <a id="1839" href="plfa.Properties.html#41933" class="Postulate">wttdgs</a><a id="1845" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `reverse-++-commute` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first.
{% raw %}<pre class="Agda"><a id="2027" class="Keyword">postulate</a>
  <a id="reverse-++-commute"></a><a id="2039" href="Assignment3.html#2039" class="Postulate">reverse-++-commute</a> <a id="2058" class="Symbol">:</a> <a id="2060" class="Symbol">∀</a> <a id="2062" class="Symbol">{</a><a id="2063" href="Assignment3.html#2063" class="Bound">A</a> <a id="2065" class="Symbol">:</a> <a id="2067" class="PrimitiveType">Set</a><a id="2070" class="Symbol">}</a> <a id="2072" class="Symbol">{</a><a id="2073" href="Assignment3.html#2073" class="Bound">xs</a> <a id="2076" href="Assignment3.html#2076" class="Bound">ys</a> <a id="2079" class="Symbol">:</a> <a id="2081" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="2086" href="Assignment3.html#2063" class="Bound">A</a><a id="2087" class="Symbol">}</a>
    <a id="2093" class="Symbol">→</a> <a id="2095" href="plfa.Lists.html#8294" class="Function">reverse</a> <a id="2103" class="Symbol">(</a><a id="2104" href="Assignment3.html#2073" class="Bound">xs</a> <a id="2107" href="plfa.Lists.html#3455" class="Function Operator">++</a> <a id="2110" href="Assignment3.html#2076" class="Bound">ys</a><a id="2112" class="Symbol">)</a> <a id="2114" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="2116" href="plfa.Lists.html#8294" class="Function">reverse</a> <a id="2124" href="Assignment3.html#2076" class="Bound">ys</a> <a id="2127" href="plfa.Lists.html#3455" class="Function Operator">++</a> <a id="2130" href="plfa.Lists.html#8294" class="Function">reverse</a> <a id="2138" href="Assignment3.html#2073" class="Bound">xs</a>
</pre>{% endraw %}
#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution.
{% raw %}<pre class="Agda"><a id="2323" class="Keyword">postulate</a>
  <a id="reverse-involutive"></a><a id="2335" href="Assignment3.html#2335" class="Postulate">reverse-involutive</a> <a id="2354" class="Symbol">:</a> <a id="2356" class="Symbol">∀</a> <a id="2358" class="Symbol">{</a><a id="2359" href="Assignment3.html#2359" class="Bound">A</a> <a id="2361" class="Symbol">:</a> <a id="2363" class="PrimitiveType">Set</a><a id="2366" class="Symbol">}</a> <a id="2368" class="Symbol">{</a><a id="2369" href="Assignment3.html#2369" class="Bound">xs</a> <a id="2372" class="Symbol">:</a> <a id="2374" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="2379" href="Assignment3.html#2359" class="Bound">A</a><a id="2380" class="Symbol">}</a>
    <a id="2386" class="Symbol">→</a> <a id="2388" href="plfa.Lists.html#8294" class="Function">reverse</a> <a id="2396" class="Symbol">(</a><a id="2397" href="plfa.Lists.html#8294" class="Function">reverse</a> <a id="2405" href="Assignment3.html#2369" class="Bound">xs</a><a id="2407" class="Symbol">)</a> <a id="2409" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="2411" href="Assignment3.html#2369" class="Bound">xs</a>
</pre>{% endraw %}
#### Exercise `map-compose`

Prove that the map of a composition is equal to the composition of two maps.
{% raw %}<pre class="Agda"><a id="2529" class="Keyword">postulate</a>
  <a id="map-compose"></a><a id="2541" href="Assignment3.html#2541" class="Postulate">map-compose</a> <a id="2553" class="Symbol">:</a> <a id="2555" class="Symbol">∀</a> <a id="2557" class="Symbol">{</a><a id="2558" href="Assignment3.html#2558" class="Bound">A</a> <a id="2560" href="Assignment3.html#2560" class="Bound">B</a> <a id="2562" href="Assignment3.html#2562" class="Bound">C</a> <a id="2564" class="Symbol">:</a> <a id="2566" class="PrimitiveType">Set</a><a id="2569" class="Symbol">}</a> <a id="2571" class="Symbol">{</a><a id="2572" href="Assignment3.html#2572" class="Bound">f</a> <a id="2574" class="Symbol">:</a> <a id="2576" href="Assignment3.html#2558" class="Bound">A</a> <a id="2578" class="Symbol">→</a> <a id="2580" href="Assignment3.html#2560" class="Bound">B</a><a id="2581" class="Symbol">}</a> <a id="2583" class="Symbol">{</a><a id="2584" href="Assignment3.html#2584" class="Bound">g</a> <a id="2586" class="Symbol">:</a> <a id="2588" href="Assignment3.html#2560" class="Bound">B</a> <a id="2590" class="Symbol">→</a> <a id="2592" href="Assignment3.html#2562" class="Bound">C</a><a id="2593" class="Symbol">}</a>
    <a id="2599" class="Symbol">→</a> <a id="2601" href="plfa.Lists.html#12979" class="Function">map</a> <a id="2605" class="Symbol">(</a><a id="2606" href="Assignment3.html#2584" class="Bound">g</a> <a id="2608" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="2610" href="Assignment3.html#2572" class="Bound">f</a><a id="2611" class="Symbol">)</a> <a id="2613" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="2615" href="plfa.Lists.html#12979" class="Function">map</a> <a id="2619" href="Assignment3.html#2584" class="Bound">g</a> <a id="2621" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="2623" href="plfa.Lists.html#12979" class="Function">map</a> <a id="2627" href="Assignment3.html#2572" class="Bound">f</a>
</pre>{% endraw %}The last step of the proof requires extensionality.

#### Exercise `map-++-commute`

Prove the following relationship between map and append.
{% raw %}<pre class="Agda"><a id="2779" class="Keyword">postulate</a>
  <a id="map-++-commute"></a><a id="2791" href="Assignment3.html#2791" class="Postulate">map-++-commute</a> <a id="2806" class="Symbol">:</a> <a id="2808" class="Symbol">∀</a> <a id="2810" class="Symbol">{</a><a id="2811" href="Assignment3.html#2811" class="Bound">A</a> <a id="2813" href="Assignment3.html#2813" class="Bound">B</a> <a id="2815" class="Symbol">:</a> <a id="2817" class="PrimitiveType">Set</a><a id="2820" class="Symbol">}</a> <a id="2822" class="Symbol">{</a><a id="2823" href="Assignment3.html#2823" class="Bound">f</a> <a id="2825" class="Symbol">:</a> <a id="2827" href="Assignment3.html#2811" class="Bound">A</a> <a id="2829" class="Symbol">→</a> <a id="2831" href="Assignment3.html#2813" class="Bound">B</a><a id="2832" class="Symbol">}</a> <a id="2834" class="Symbol">{</a><a id="2835" href="Assignment3.html#2835" class="Bound">xs</a> <a id="2838" href="Assignment3.html#2838" class="Bound">ys</a> <a id="2841" class="Symbol">:</a> <a id="2843" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="2848" href="Assignment3.html#2811" class="Bound">A</a><a id="2849" class="Symbol">}</a>
   <a id="2854" class="Symbol">→</a>  <a id="2857" href="plfa.Lists.html#12979" class="Function">map</a> <a id="2861" href="Assignment3.html#2823" class="Bound">f</a> <a id="2863" class="Symbol">(</a><a id="2864" href="Assignment3.html#2835" class="Bound">xs</a> <a id="2867" href="plfa.Lists.html#3455" class="Function Operator">++</a> <a id="2870" href="Assignment3.html#2838" class="Bound">ys</a><a id="2872" class="Symbol">)</a> <a id="2874" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="2876" href="plfa.Lists.html#12979" class="Function">map</a> <a id="2880" href="Assignment3.html#2823" class="Bound">f</a> <a id="2882" href="Assignment3.html#2835" class="Bound">xs</a> <a id="2885" href="plfa.Lists.html#3455" class="Function Operator">++</a> <a id="2888" href="plfa.Lists.html#12979" class="Function">map</a> <a id="2892" href="Assignment3.html#2823" class="Bound">f</a> <a id="2894" href="Assignment3.html#2838" class="Bound">ys</a>
</pre>{% endraw %}
#### Exercise `map-Tree`

Define a type of trees with leaves of type `A` and internal
nodes of type `B`.
{% raw %}<pre class="Agda"><a id="3011" class="Keyword">data</a> <a id="Tree"></a><a id="3016" href="Assignment3.html#3016" class="Datatype">Tree</a> <a id="3021" class="Symbol">(</a><a id="3022" href="Assignment3.html#3022" class="Bound">A</a> <a id="3024" href="Assignment3.html#3024" class="Bound">B</a> <a id="3026" class="Symbol">:</a> <a id="3028" class="PrimitiveType">Set</a><a id="3031" class="Symbol">)</a> <a id="3033" class="Symbol">:</a> <a id="3035" class="PrimitiveType">Set</a> <a id="3039" class="Keyword">where</a>
  <a id="Tree.leaf"></a><a id="3047" href="Assignment3.html#3047" class="InductiveConstructor">leaf</a> <a id="3052" class="Symbol">:</a> <a id="3054" href="Assignment3.html#3022" class="Bound">A</a> <a id="3056" class="Symbol">→</a> <a id="3058" href="Assignment3.html#3016" class="Datatype">Tree</a> <a id="3063" href="Assignment3.html#3022" class="Bound">A</a> <a id="3065" href="Assignment3.html#3024" class="Bound">B</a>
  <a id="Tree.node"></a><a id="3069" href="Assignment3.html#3069" class="InductiveConstructor">node</a> <a id="3074" class="Symbol">:</a> <a id="3076" href="Assignment3.html#3016" class="Datatype">Tree</a> <a id="3081" href="Assignment3.html#3022" class="Bound">A</a> <a id="3083" href="Assignment3.html#3024" class="Bound">B</a> <a id="3085" class="Symbol">→</a> <a id="3087" href="Assignment3.html#3024" class="Bound">B</a> <a id="3089" class="Symbol">→</a> <a id="3091" href="Assignment3.html#3016" class="Datatype">Tree</a> <a id="3096" href="Assignment3.html#3022" class="Bound">A</a> <a id="3098" href="Assignment3.html#3024" class="Bound">B</a> <a id="3100" class="Symbol">→</a> <a id="3102" href="Assignment3.html#3016" class="Datatype">Tree</a> <a id="3107" href="Assignment3.html#3022" class="Bound">A</a> <a id="3109" href="Assignment3.html#3024" class="Bound">B</a>
</pre>{% endraw %}Define a suitable map operator over trees.
{% raw %}<pre class="Agda"><a id="3162" class="Keyword">postulate</a>
  <a id="map-Tree"></a><a id="3174" href="Assignment3.html#3174" class="Postulate">map-Tree</a> <a id="3183" class="Symbol">:</a> <a id="3185" class="Symbol">∀</a> <a id="3187" class="Symbol">{</a><a id="3188" href="Assignment3.html#3188" class="Bound">A</a> <a id="3190" href="Assignment3.html#3190" class="Bound">B</a> <a id="3192" href="Assignment3.html#3192" class="Bound">C</a> <a id="3194" href="Assignment3.html#3194" class="Bound">D</a> <a id="3196" class="Symbol">:</a> <a id="3198" class="PrimitiveType">Set</a><a id="3201" class="Symbol">}</a>
    <a id="3207" class="Symbol">→</a> <a id="3209" class="Symbol">(</a><a id="3210" href="Assignment3.html#3188" class="Bound">A</a> <a id="3212" class="Symbol">→</a> <a id="3214" href="Assignment3.html#3192" class="Bound">C</a><a id="3215" class="Symbol">)</a> <a id="3217" class="Symbol">→</a> <a id="3219" class="Symbol">(</a><a id="3220" href="Assignment3.html#3190" class="Bound">B</a> <a id="3222" class="Symbol">→</a> <a id="3224" href="Assignment3.html#3194" class="Bound">D</a><a id="3225" class="Symbol">)</a> <a id="3227" class="Symbol">→</a> <a id="3229" href="Assignment3.html#3016" class="Datatype">Tree</a> <a id="3234" href="Assignment3.html#3188" class="Bound">A</a> <a id="3236" href="Assignment3.html#3190" class="Bound">B</a> <a id="3238" class="Symbol">→</a> <a id="3240" href="Assignment3.html#3016" class="Datatype">Tree</a> <a id="3245" href="Assignment3.html#3192" class="Bound">C</a> <a id="3247" href="Assignment3.html#3194" class="Bound">D</a>
</pre>{% endraw %}
#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example,

    product [ 1 , 2 , 3 , 4 ] ≡ 24

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows.
{% raw %}<pre class="Agda"><a id="3509" class="Keyword">postulate</a>
  <a id="foldr-++"></a><a id="3521" href="Assignment3.html#3521" class="Postulate">foldr-++</a> <a id="3530" class="Symbol">:</a> <a id="3532" class="Symbol">∀</a> <a id="3534" class="Symbol">{</a><a id="3535" href="Assignment3.html#3535" class="Bound">A</a> <a id="3537" href="Assignment3.html#3537" class="Bound">B</a> <a id="3539" class="Symbol">:</a> <a id="3541" class="PrimitiveType">Set</a><a id="3544" class="Symbol">}</a> <a id="3546" class="Symbol">(</a><a id="3547" href="Assignment3.html#3547" class="Bound Operator">_⊗_</a> <a id="3551" class="Symbol">:</a> <a id="3553" href="Assignment3.html#3535" class="Bound">A</a> <a id="3555" class="Symbol">→</a> <a id="3557" href="Assignment3.html#3537" class="Bound">B</a> <a id="3559" class="Symbol">→</a> <a id="3561" href="Assignment3.html#3537" class="Bound">B</a><a id="3562" class="Symbol">)</a> <a id="3564" class="Symbol">(</a><a id="3565" href="Assignment3.html#3565" class="Bound">e</a> <a id="3567" class="Symbol">:</a> <a id="3569" href="Assignment3.html#3537" class="Bound">B</a><a id="3570" class="Symbol">)</a> <a id="3572" class="Symbol">(</a><a id="3573" href="Assignment3.html#3573" class="Bound">xs</a> <a id="3576" href="Assignment3.html#3576" class="Bound">ys</a> <a id="3579" class="Symbol">:</a> <a id="3581" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="3586" href="Assignment3.html#3535" class="Bound">A</a><a id="3587" class="Symbol">)</a> <a id="3589" class="Symbol">→</a>
    <a id="3595" href="plfa.Lists.html#15448" class="Function">foldr</a> <a id="3601" href="Assignment3.html#3547" class="Bound Operator">_⊗_</a> <a id="3605" href="Assignment3.html#3565" class="Bound">e</a> <a id="3607" class="Symbol">(</a><a id="3608" href="Assignment3.html#3573" class="Bound">xs</a> <a id="3611" href="plfa.Lists.html#3455" class="Function Operator">++</a> <a id="3614" href="Assignment3.html#3576" class="Bound">ys</a><a id="3616" class="Symbol">)</a> <a id="3618" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3620" href="plfa.Lists.html#15448" class="Function">foldr</a> <a id="3626" href="Assignment3.html#3547" class="Bound Operator">_⊗_</a> <a id="3630" class="Symbol">(</a><a id="3631" href="plfa.Lists.html#15448" class="Function">foldr</a> <a id="3637" href="Assignment3.html#3547" class="Bound Operator">_⊗_</a> <a id="3641" href="Assignment3.html#3565" class="Bound">e</a> <a id="3643" href="Assignment3.html#3576" class="Bound">ys</a><a id="3645" class="Symbol">)</a> <a id="3647" href="Assignment3.html#3573" class="Bound">xs</a>
</pre>{% endraw %}

#### Exercise `map-is-foldr`

Show that map can be defined using fold.
{% raw %}<pre class="Agda"><a id="3731" class="Keyword">postulate</a>
  <a id="map-is-foldr"></a><a id="3743" href="Assignment3.html#3743" class="Postulate">map-is-foldr</a> <a id="3756" class="Symbol">:</a> <a id="3758" class="Symbol">∀</a> <a id="3760" class="Symbol">{</a><a id="3761" href="Assignment3.html#3761" class="Bound">A</a> <a id="3763" href="Assignment3.html#3763" class="Bound">B</a> <a id="3765" class="Symbol">:</a> <a id="3767" class="PrimitiveType">Set</a><a id="3770" class="Symbol">}</a> <a id="3772" class="Symbol">{</a><a id="3773" href="Assignment3.html#3773" class="Bound">f</a> <a id="3775" class="Symbol">:</a> <a id="3777" href="Assignment3.html#3761" class="Bound">A</a> <a id="3779" class="Symbol">→</a> <a id="3781" href="Assignment3.html#3763" class="Bound">B</a><a id="3782" class="Symbol">}</a> <a id="3784" class="Symbol">→</a>
    <a id="3790" href="plfa.Lists.html#12979" class="Function">map</a> <a id="3794" href="Assignment3.html#3773" class="Bound">f</a> <a id="3796" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3798" href="plfa.Lists.html#15448" class="Function">foldr</a> <a id="3804" class="Symbol">(λ</a> <a id="3807" href="Assignment3.html#3807" class="Bound">x</a> <a id="3809" href="Assignment3.html#3809" class="Bound">xs</a> <a id="3812" class="Symbol">→</a> <a id="3814" href="Assignment3.html#3773" class="Bound">f</a> <a id="3816" href="Assignment3.html#3807" class="Bound">x</a> <a id="3818" href="plfa.Lists.html#1099" class="InductiveConstructor Operator">∷</a> <a id="3820" href="Assignment3.html#3809" class="Bound">xs</a><a id="3822" class="Symbol">)</a> <a id="3824" href="plfa.Lists.html#1084" class="InductiveConstructor">[]</a>
</pre>{% endraw %}This requires extensionality.

#### Exercise `fold-Tree`

Define a suitable fold function for the type of trees given earlier.
{% raw %}<pre class="Agda"><a id="3962" class="Keyword">postulate</a>
  <a id="fold-Tree"></a><a id="3974" href="Assignment3.html#3974" class="Postulate">fold-Tree</a> <a id="3984" class="Symbol">:</a> <a id="3986" class="Symbol">∀</a> <a id="3988" class="Symbol">{</a><a id="3989" href="Assignment3.html#3989" class="Bound">A</a> <a id="3991" href="Assignment3.html#3991" class="Bound">B</a> <a id="3993" href="Assignment3.html#3993" class="Bound">C</a> <a id="3995" class="Symbol">:</a> <a id="3997" class="PrimitiveType">Set</a><a id="4000" class="Symbol">}</a>
    <a id="4006" class="Symbol">→</a> <a id="4008" class="Symbol">(</a><a id="4009" href="Assignment3.html#3989" class="Bound">A</a> <a id="4011" class="Symbol">→</a> <a id="4013" href="Assignment3.html#3993" class="Bound">C</a><a id="4014" class="Symbol">)</a> <a id="4016" class="Symbol">→</a> <a id="4018" class="Symbol">(</a><a id="4019" href="Assignment3.html#3993" class="Bound">C</a> <a id="4021" class="Symbol">→</a> <a id="4023" href="Assignment3.html#3991" class="Bound">B</a> <a id="4025" class="Symbol">→</a> <a id="4027" href="Assignment3.html#3993" class="Bound">C</a> <a id="4029" class="Symbol">→</a> <a id="4031" href="Assignment3.html#3993" class="Bound">C</a><a id="4032" class="Symbol">)</a> <a id="4034" class="Symbol">→</a> <a id="4036" href="Assignment3.html#3016" class="Datatype">Tree</a> <a id="4041" href="Assignment3.html#3989" class="Bound">A</a> <a id="4043" href="Assignment3.html#3991" class="Bound">B</a> <a id="4045" class="Symbol">→</a> <a id="4047" href="Assignment3.html#3993" class="Bound">C</a>
</pre>{% endraw %}
#### Exercise `map-is-fold-Tree`

Demonstrate an analogue of `map-is-foldr` for the type of trees.

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows.
{% raw %}<pre class="Agda"><a id="downFrom"></a><a id="4245" href="Assignment3.html#4245" class="Function">downFrom</a> <a id="4254" class="Symbol">:</a> <a id="4256" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="4258" class="Symbol">→</a> <a id="4260" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="4265" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="4267" href="Assignment3.html#4245" class="Function">downFrom</a> <a id="4276" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="4285" class="Symbol">=</a>  <a id="4288" href="plfa.Lists.html#1084" class="InductiveConstructor">[]</a>
<a id="4291" href="Assignment3.html#4245" class="Function">downFrom</a> <a id="4300" class="Symbol">(</a><a id="4301" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4305" href="Assignment3.html#4305" class="Bound">n</a><a id="4306" class="Symbol">)</a>  <a id="4309" class="Symbol">=</a>  <a id="4312" href="Assignment3.html#4305" class="Bound">n</a> <a id="4314" href="plfa.Lists.html#1099" class="InductiveConstructor Operator">∷</a> <a id="4316" href="Assignment3.html#4245" class="Function">downFrom</a> <a id="4325" href="Assignment3.html#4305" class="Bound">n</a>
</pre>{% endraw %}For example,
{% raw %}<pre class="Agda"><a id="4348" href="Assignment3.html#4348" class="Function">_</a> <a id="4350" class="Symbol">:</a> <a id="4352" href="Assignment3.html#4245" class="Function">downFrom</a> <a id="4361" class="Number">3</a> <a id="4363" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="4365" href="plfa.Lists.html#2869" class="InductiveConstructor Operator">[</a> <a id="4367" class="Number">2</a> <a id="4369" href="plfa.Lists.html#2869" class="InductiveConstructor Operator">,</a> <a id="4371" class="Number">1</a> <a id="4373" href="plfa.Lists.html#2869" class="InductiveConstructor Operator">,</a> <a id="4375" class="Number">0</a> <a id="4377" href="plfa.Lists.html#2869" class="InductiveConstructor Operator">]</a>
<a id="4379" class="Symbol">_</a> <a id="4381" class="Symbol">=</a> <a id="4383" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`.
{% raw %}<pre class="Agda"><a id="4479" class="Keyword">postulate</a>
  <a id="sum-downFrom"></a><a id="4491" href="Assignment3.html#4491" class="Postulate">sum-downFrom</a> <a id="4504" class="Symbol">:</a> <a id="4506" class="Symbol">∀</a> <a id="4508" class="Symbol">(</a><a id="4509" href="Assignment3.html#4509" class="Bound">n</a> <a id="4511" class="Symbol">:</a> <a id="4513" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="4514" class="Symbol">)</a>
    <a id="4520" class="Symbol">→</a> <a id="4522" href="plfa.Lists.html#16343" class="Function">sum</a> <a id="4526" class="Symbol">(</a><a id="4527" href="Assignment3.html#4245" class="Function">downFrom</a> <a id="4536" href="Assignment3.html#4509" class="Bound">n</a><a id="4537" class="Symbol">)</a> <a id="4539" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="4541" class="Number">2</a> <a id="4543" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="4545" href="Assignment3.html#4509" class="Bound">n</a> <a id="4547" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="4549" class="Symbol">(</a><a id="4550" href="Assignment3.html#4509" class="Bound">n</a> <a id="4552" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">∸</a> <a id="4554" class="Number">1</a><a id="4555" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `foldl`

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example,

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z


#### Exercise `foldr-monoid-foldl`

Show that if `_⊕_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.


#### Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-↔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.


#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.


#### Exercise `¬Any≃All¬` (stretch)

First generalise composition to arbitrary levels, using
[universe polymorphism][plfa.Equality#unipoly].
{% raw %}<pre class="Agda"><a id="_∘′_"></a><a id="5459" href="Assignment3.html#5459" class="Function Operator">_∘′_</a> <a id="5464" class="Symbol">:</a> <a id="5466" class="Symbol">∀</a> <a id="5468" class="Symbol">{</a><a id="5469" href="Assignment3.html#5469" class="Bound">ℓ₁</a> <a id="5472" href="Assignment3.html#5472" class="Bound">ℓ₂</a> <a id="5475" href="Assignment3.html#5475" class="Bound">ℓ₃</a> <a id="5478" class="Symbol">:</a> <a id="5480" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="5485" class="Symbol">}</a> <a id="5487" class="Symbol">{</a><a id="5488" href="Assignment3.html#5488" class="Bound">A</a> <a id="5490" class="Symbol">:</a> <a id="5492" class="PrimitiveType">Set</a> <a id="5496" href="Assignment3.html#5469" class="Bound">ℓ₁</a><a id="5498" class="Symbol">}</a> <a id="5500" class="Symbol">{</a><a id="5501" href="Assignment3.html#5501" class="Bound">B</a> <a id="5503" class="Symbol">:</a> <a id="5505" class="PrimitiveType">Set</a> <a id="5509" href="Assignment3.html#5472" class="Bound">ℓ₂</a><a id="5511" class="Symbol">}</a> <a id="5513" class="Symbol">{</a><a id="5514" href="Assignment3.html#5514" class="Bound">C</a> <a id="5516" class="Symbol">:</a> <a id="5518" class="PrimitiveType">Set</a> <a id="5522" href="Assignment3.html#5475" class="Bound">ℓ₃</a><a id="5524" class="Symbol">}</a>
  <a id="5528" class="Symbol">→</a> <a id="5530" class="Symbol">(</a><a id="5531" href="Assignment3.html#5501" class="Bound">B</a> <a id="5533" class="Symbol">→</a> <a id="5535" href="Assignment3.html#5514" class="Bound">C</a><a id="5536" class="Symbol">)</a> <a id="5538" class="Symbol">→</a> <a id="5540" class="Symbol">(</a><a id="5541" href="Assignment3.html#5488" class="Bound">A</a> <a id="5543" class="Symbol">→</a> <a id="5545" href="Assignment3.html#5501" class="Bound">B</a><a id="5546" class="Symbol">)</a> <a id="5548" class="Symbol">→</a> <a id="5550" href="Assignment3.html#5488" class="Bound">A</a> <a id="5552" class="Symbol">→</a> <a id="5554" href="Assignment3.html#5514" class="Bound">C</a>
<a id="5556" class="Symbol">(</a><a id="5557" href="Assignment3.html#5557" class="Bound">g</a> <a id="5559" href="Assignment3.html#5459" class="Function Operator">∘′</a> <a id="5562" href="Assignment3.html#5562" class="Bound">f</a><a id="5563" class="Symbol">)</a> <a id="5565" href="Assignment3.html#5565" class="Bound">x</a>  <a id="5568" class="Symbol">=</a>  <a id="5571" href="Assignment3.html#5557" class="Bound">g</a> <a id="5573" class="Symbol">(</a><a id="5574" href="Assignment3.html#5562" class="Bound">f</a> <a id="5576" href="Assignment3.html#5565" class="Bound">x</a><a id="5577" class="Symbol">)</a>
</pre>{% endraw %}
Show that `Any` and `All` satisfy a version of De Morgan's Law.
{% raw %}<pre class="Agda"><a id="5652" class="Keyword">postulate</a>
  <a id="¬Any≃All¬"></a><a id="5664" href="Assignment3.html#5664" class="Postulate">¬Any≃All¬</a> <a id="5674" class="Symbol">:</a> <a id="5676" class="Symbol">∀</a> <a id="5678" class="Symbol">{</a><a id="5679" href="Assignment3.html#5679" class="Bound">A</a> <a id="5681" class="Symbol">:</a> <a id="5683" class="PrimitiveType">Set</a><a id="5686" class="Symbol">}</a> <a id="5688" class="Symbol">(</a><a id="5689" href="Assignment3.html#5689" class="Bound">P</a> <a id="5691" class="Symbol">:</a> <a id="5693" href="Assignment3.html#5679" class="Bound">A</a> <a id="5695" class="Symbol">→</a> <a id="5697" class="PrimitiveType">Set</a><a id="5700" class="Symbol">)</a> <a id="5702" class="Symbol">(</a><a id="5703" href="Assignment3.html#5703" class="Bound">xs</a> <a id="5706" class="Symbol">:</a> <a id="5708" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="5713" href="Assignment3.html#5679" class="Bound">A</a><a id="5714" class="Symbol">)</a>
    <a id="5720" class="Symbol">→</a> <a id="5722" class="Symbol">(</a><a id="5723" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="5726" href="Assignment3.html#5459" class="Function Operator">∘′</a> <a id="5729" href="plfa.Lists.html#22498" class="Datatype">Any</a> <a id="5733" href="Assignment3.html#5689" class="Bound">P</a><a id="5734" class="Symbol">)</a> <a id="5736" href="Assignment3.html#5703" class="Bound">xs</a> <a id="5739" href="plfa.Isomorphism.html#3955" class="Record Operator">≃</a> <a id="5741" href="plfa.Lists.html#21045" class="Datatype">All</a> <a id="5745" class="Symbol">(</a><a id="5746" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="5749" href="Assignment3.html#5459" class="Function Operator">∘′</a> <a id="5752" href="Assignment3.html#5689" class="Bound">P</a><a id="5753" class="Symbol">)</a> <a id="5755" href="Assignment3.html#5703" class="Bound">xs</a>
</pre>{% endraw %}
Do we also have the following?
{% raw %}<pre class="Agda"><a id="5798" class="Keyword">postulate</a>
  <a id="¬All≃Any¬"></a><a id="5810" href="Assignment3.html#5810" class="Postulate">¬All≃Any¬</a> <a id="5820" class="Symbol">:</a> <a id="5822" class="Symbol">∀</a> <a id="5824" class="Symbol">{</a><a id="5825" href="Assignment3.html#5825" class="Bound">A</a> <a id="5827" class="Symbol">:</a> <a id="5829" class="PrimitiveType">Set</a><a id="5832" class="Symbol">}</a> <a id="5834" class="Symbol">(</a><a id="5835" href="Assignment3.html#5835" class="Bound">P</a> <a id="5837" class="Symbol">:</a> <a id="5839" href="Assignment3.html#5825" class="Bound">A</a> <a id="5841" class="Symbol">→</a> <a id="5843" class="PrimitiveType">Set</a><a id="5846" class="Symbol">)</a> <a id="5848" class="Symbol">(</a><a id="5849" href="Assignment3.html#5849" class="Bound">xs</a> <a id="5852" class="Symbol">:</a> <a id="5854" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="5859" href="Assignment3.html#5825" class="Bound">A</a><a id="5860" class="Symbol">)</a>
    <a id="5866" class="Symbol">→</a> <a id="5868" class="Symbol">(</a><a id="5869" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="5872" href="Assignment3.html#5459" class="Function Operator">∘′</a> <a id="5875" href="plfa.Lists.html#21045" class="Datatype">All</a> <a id="5879" href="Assignment3.html#5835" class="Bound">P</a><a id="5880" class="Symbol">)</a> <a id="5882" href="Assignment3.html#5849" class="Bound">xs</a> <a id="5885" href="plfa.Isomorphism.html#3955" class="Record Operator">≃</a> <a id="5887" href="plfa.Lists.html#22498" class="Datatype">Any</a> <a id="5891" class="Symbol">(</a><a id="5892" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="5895" href="Assignment3.html#5459" class="Function Operator">∘′</a> <a id="5898" href="Assignment3.html#5835" class="Bound">P</a><a id="5899" class="Symbol">)</a> <a id="5901" href="Assignment3.html#5849" class="Bound">xs</a>
</pre>{% endraw %}If so, prove; if not, explain why.


#### Exercise `any?` (stretch)

Just as `All` has analogues `all` and `all?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `any?` which determine whether a predicates holds
for some element of a list.  Give their definitions.


#### Exercise `filter?` (stretch)

Define the following variant of the traditional `filter` function on lists,
which given a list and a decidable predicate returns all elements of the
list satisfying the predicate.
{% raw %}<pre class="Agda"><a id="6456" class="Keyword">postulate</a>
  <a id="filter?"></a><a id="6468" href="Assignment3.html#6468" class="Postulate">filter?</a> <a id="6476" class="Symbol">:</a> <a id="6478" class="Symbol">∀</a> <a id="6480" class="Symbol">{</a><a id="6481" href="Assignment3.html#6481" class="Bound">A</a> <a id="6483" class="Symbol">:</a> <a id="6485" class="PrimitiveType">Set</a><a id="6488" class="Symbol">}</a> <a id="6490" class="Symbol">{</a><a id="6491" href="Assignment3.html#6491" class="Bound">P</a> <a id="6493" class="Symbol">:</a> <a id="6495" href="Assignment3.html#6481" class="Bound">A</a> <a id="6497" class="Symbol">→</a> <a id="6499" class="PrimitiveType">Set</a><a id="6502" class="Symbol">}</a>
    <a id="6508" class="Symbol">→</a> <a id="6510" class="Symbol">(</a><a id="6511" href="Assignment3.html#6511" class="Bound">P?</a> <a id="6514" class="Symbol">:</a> <a id="6516" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html#3474" class="Function">Decidable</a> <a id="6526" href="Assignment3.html#6491" class="Bound">P</a><a id="6527" class="Symbol">)</a> <a id="6529" class="Symbol">→</a> <a id="6531" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="6536" href="Assignment3.html#6481" class="Bound">A</a> <a id="6538" class="Symbol">→</a> <a id="6540" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6543" href="Assignment3.html#6543" class="Bound">ys</a> <a id="6546" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a><a id="6547" class="Symbol">(</a> <a id="6549" href="plfa.Lists.html#21045" class="Datatype">All</a> <a id="6553" href="Assignment3.html#6491" class="Bound">P</a> <a id="6555" href="Assignment3.html#6543" class="Bound">ys</a> <a id="6558" class="Symbol">)</a>
</pre>{% endraw %}

## Lambda

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.


#### Exercise `primed` (stretch)

We can make examples with lambda terms slightly easier to write
by adding the following definitions.
{% raw %}<pre class="Agda"><a id="ƛ′_⇒_"></a><a id="6832" href="Assignment3.html#6832" class="Function Operator">ƛ′_⇒_</a> <a id="6838" class="Symbol">:</a> <a id="6840" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="6845" class="Symbol">→</a> <a id="6847" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="6852" class="Symbol">→</a> <a id="6854" href="plfa.Lambda.html#3766" class="Datatype">Term</a>
<a id="6859" href="Assignment3.html#6832" class="Function Operator">ƛ′</a> <a id="6862" class="Symbol">(</a><a id="6863" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="6865" href="Assignment3.html#6865" class="Bound">x</a><a id="6866" class="Symbol">)</a> <a id="6868" href="Assignment3.html#6832" class="Function Operator">⇒</a> <a id="6870" href="Assignment3.html#6870" class="Bound">N</a>  <a id="6873" class="Symbol">=</a>  <a id="6876" href="plfa.Lambda.html#3824" class="InductiveConstructor Operator">ƛ</a> <a id="6878" href="Assignment3.html#6865" class="Bound">x</a> <a id="6880" href="plfa.Lambda.html#3824" class="InductiveConstructor Operator">⇒</a> <a id="6882" href="Assignment3.html#6870" class="Bound">N</a>
<a id="6884" href="Assignment3.html#6832" class="CatchallClause Function Operator">ƛ′</a><a id="6886" class="CatchallClause"> </a><a id="6887" class="CatchallClause Symbol">_</a><a id="6888" class="CatchallClause"> </a><a id="6889" href="Assignment3.html#6832" class="CatchallClause Function Operator">⇒</a><a id="6890" class="CatchallClause"> </a><a id="6891" class="CatchallClause Symbol">_</a>      <a id="6898" class="Symbol">=</a>  <a id="6901" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="6908" href="Assignment3.html#6937" class="Postulate">impossible</a>
  <a id="6921" class="Keyword">where</a> <a id="6927" class="Keyword">postulate</a> <a id="6937" href="Assignment3.html#6937" class="Postulate">impossible</a> <a id="6948" class="Symbol">:</a> <a id="6950" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="6953" href="Assignment3.html#6953" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="6975" class="Symbol">:</a> <a id="6977" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="6982" class="Symbol">→</a> <a id="6984" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="6989" class="Symbol">→</a> <a id="6991" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="6996" class="Symbol">→</a> <a id="6998" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="7003" class="Symbol">→</a> <a id="7005" href="plfa.Lambda.html#3766" class="Datatype">Term</a>
<a id="7010" href="Assignment3.html#6953" class="Function Operator">case′</a> <a id="7016" href="Assignment3.html#7016" class="Bound">L</a> <a id="7018" href="Assignment3.html#6953" class="Function Operator">[zero⇒</a> <a id="7025" href="Assignment3.html#7025" class="Bound">M</a> <a id="7027" href="Assignment3.html#6953" class="Function Operator">|suc</a> <a id="7032" class="Symbol">(</a><a id="7033" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="7035" href="Assignment3.html#7035" class="Bound">x</a><a id="7036" class="Symbol">)</a> <a id="7038" href="Assignment3.html#6953" class="Function Operator">⇒</a> <a id="7040" href="Assignment3.html#7040" class="Bound">N</a> <a id="7042" href="Assignment3.html#6953" class="Function Operator">]</a>  <a id="7045" class="Symbol">=</a>  <a id="7048" href="plfa.Lambda.html#3993" class="InductiveConstructor Operator">case</a> <a id="7053" href="Assignment3.html#7016" class="Bound">L</a> <a id="7055" href="plfa.Lambda.html#3993" class="InductiveConstructor Operator">[zero⇒</a> <a id="7062" href="Assignment3.html#7025" class="Bound">M</a> <a id="7064" href="plfa.Lambda.html#3993" class="InductiveConstructor Operator">|suc</a> <a id="7069" href="Assignment3.html#7035" class="Bound">x</a> <a id="7071" href="plfa.Lambda.html#3993" class="InductiveConstructor Operator">⇒</a> <a id="7073" href="Assignment3.html#7040" class="Bound">N</a> <a id="7075" href="plfa.Lambda.html#3993" class="InductiveConstructor Operator">]</a>
<a id="7077" href="Assignment3.html#6953" class="CatchallClause Function Operator">case′</a><a id="7082" class="CatchallClause"> </a><a id="7083" class="CatchallClause Symbol">_</a><a id="7084" class="CatchallClause"> </a><a id="7085" href="Assignment3.html#6953" class="CatchallClause Function Operator">[zero⇒</a><a id="7091" class="CatchallClause"> </a><a id="7092" class="CatchallClause Symbol">_</a><a id="7093" class="CatchallClause"> </a><a id="7094" href="Assignment3.html#6953" class="CatchallClause Function Operator">|suc</a><a id="7098" class="CatchallClause"> </a><a id="7099" class="CatchallClause Symbol">_</a><a id="7100" class="CatchallClause"> </a><a id="7101" href="Assignment3.html#6953" class="CatchallClause Function Operator">⇒</a><a id="7102" class="CatchallClause"> </a><a id="7103" class="CatchallClause Symbol">_</a><a id="7104" class="CatchallClause"> </a><a id="7105" href="Assignment3.html#6953" class="CatchallClause Function Operator">]</a>      <a id="7112" class="Symbol">=</a>  <a id="7115" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7122" href="Assignment3.html#7151" class="Postulate">impossible</a>
  <a id="7135" class="Keyword">where</a> <a id="7141" class="Keyword">postulate</a> <a id="7151" href="Assignment3.html#7151" class="Postulate">impossible</a> <a id="7162" class="Symbol">:</a> <a id="7164" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="7167" href="Assignment3.html#7167" class="Function Operator">μ′_⇒_</a> <a id="7173" class="Symbol">:</a> <a id="7175" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="7180" class="Symbol">→</a> <a id="7182" href="plfa.Lambda.html#3766" class="Datatype">Term</a> <a id="7187" class="Symbol">→</a> <a id="7189" href="plfa.Lambda.html#3766" class="Datatype">Term</a>
<a id="7194" href="Assignment3.html#7167" class="Function Operator">μ′</a> <a id="7197" class="Symbol">(</a><a id="7198" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="7200" href="Assignment3.html#7200" class="Bound">x</a><a id="7201" class="Symbol">)</a> <a id="7203" href="Assignment3.html#7167" class="Function Operator">⇒</a> <a id="7205" href="Assignment3.html#7205" class="Bound">N</a>  <a id="7208" class="Symbol">=</a>  <a id="7211" href="plfa.Lambda.html#4053" class="InductiveConstructor Operator">μ</a> <a id="7213" href="Assignment3.html#7200" class="Bound">x</a> <a id="7215" href="plfa.Lambda.html#4053" class="InductiveConstructor Operator">⇒</a> <a id="7217" href="Assignment3.html#7205" class="Bound">N</a>
<a id="7219" href="Assignment3.html#7167" class="CatchallClause Function Operator">μ′</a><a id="7221" class="CatchallClause"> </a><a id="7222" class="CatchallClause Symbol">_</a><a id="7223" class="CatchallClause"> </a><a id="7224" href="Assignment3.html#7167" class="CatchallClause Function Operator">⇒</a><a id="7225" class="CatchallClause"> </a><a id="7226" class="CatchallClause Symbol">_</a>      <a id="7233" class="Symbol">=</a>  <a id="7236" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7243" href="Assignment3.html#7272" class="Postulate">impossible</a>
  <a id="7256" class="Keyword">where</a> <a id="7262" class="Keyword">postulate</a> <a id="7272" href="Assignment3.html#7272" class="Postulate">impossible</a> <a id="7283" class="Symbol">:</a> <a id="7285" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}The definition of `plus` can now be written as follows.
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="7351" href="Assignment3.html#7351" class="Function">plus′</a> <a id="7357" class="Symbol">:</a> <a id="7359" href="plfa.Lambda.html#3766" class="Datatype">Term</a>
<a id="7364" href="Assignment3.html#7351" class="Function">plus′</a> <a id="7370" class="Symbol">=</a> <a id="7372" href="Assignment3.html#7167" class="Function Operator">μ′</a> <a id="7375" href="Assignment3.html#7482" class="Function">+</a> <a id="7377" href="Assignment3.html#7167" class="Function Operator">⇒</a> <a id="7379" href="Assignment3.html#6832" class="Function Operator">ƛ′</a> <a id="7382" href="Assignment3.html#7496" class="Function">m</a> <a id="7384" href="Assignment3.html#6832" class="Function Operator">⇒</a> <a id="7386" href="Assignment3.html#6832" class="Function Operator">ƛ′</a> <a id="7389" href="Assignment3.html#7510" class="Function">n</a> <a id="7391" href="Assignment3.html#6832" class="Function Operator">⇒</a>
          <a id="7403" href="Assignment3.html#6953" class="Function Operator">case′</a> <a id="7409" href="Assignment3.html#7496" class="Function">m</a>
            <a id="7423" href="Assignment3.html#6953" class="Function Operator">[zero⇒</a> <a id="7430" href="Assignment3.html#7510" class="Function">n</a>
            <a id="7444" href="Assignment3.html#6953" class="Function Operator">|suc</a> <a id="7449" href="Assignment3.html#7496" class="Function">m</a> <a id="7451" href="Assignment3.html#6953" class="Function Operator">⇒</a> <a id="7453" href="plfa.Lambda.html#3952" class="InductiveConstructor Operator">`suc</a> <a id="7458" class="Symbol">(</a><a id="7459" href="Assignment3.html#7482" class="Function">+</a> <a id="7461" href="plfa.Lambda.html#3870" class="InductiveConstructor Operator">·</a> <a id="7463" href="Assignment3.html#7496" class="Function">m</a> <a id="7465" href="plfa.Lambda.html#3870" class="InductiveConstructor Operator">·</a> <a id="7467" href="Assignment3.html#7510" class="Function">n</a><a id="7468" class="Symbol">)</a> <a id="7470" href="Assignment3.html#6953" class="Function Operator">]</a>
  <a id="7474" class="Keyword">where</a>
  <a id="7482" href="Assignment3.html#7482" class="Function">+</a>  <a id="7485" class="Symbol">=</a>  <a id="7488" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="7490" class="String">&quot;+&quot;</a>
  <a id="7496" href="Assignment3.html#7496" class="Function">m</a>  <a id="7499" class="Symbol">=</a>  <a id="7502" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="7504" class="String">&quot;m&quot;</a>
  <a id="7510" href="Assignment3.html#7510" class="Function">n</a>  <a id="7513" class="Symbol">=</a>  <a id="7516" href="plfa.Lambda.html#3785" class="InductiveConstructor Operator">`</a> <a id="7518" class="String">&quot;n&quot;</a>
</pre>{% endraw %}Write out the definition of multiplication in the same style.

#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a with clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.


#### Exercise `—↠≃—↠′`

Show that the two notions of reflexive and transitive closure
above are isomorphic.


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
{% raw %}<pre class="Agda"><a id="8623" class="Keyword">postulate</a>
  <a id="value?"></a><a id="8635" href="Assignment3.html#8635" class="Postulate">value?</a> <a id="8642" class="Symbol">:</a> <a id="8644" class="Symbol">∀</a> <a id="8646" class="Symbol">{</a><a id="8647" href="Assignment3.html#8647" class="Bound">A</a> <a id="8649" href="Assignment3.html#8649" class="Bound">M</a><a id="8650" class="Symbol">}</a> <a id="8652" class="Symbol">→</a> <a id="8654" href="plfa.Lambda.html#30706" class="InductiveConstructor">∅</a> <a id="8656" href="plfa.Lambda.html#33069" class="Datatype Operator">⊢</a> <a id="8658" href="Assignment3.html#8649" class="Bound">M</a> <a id="8660" href="plfa.Lambda.html#33069" class="Datatype Operator">⦂</a> <a id="8662" href="Assignment3.html#8647" class="Bound">A</a> <a id="8664" class="Symbol">→</a> <a id="8666" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8670" class="Symbol">(</a><a id="8671" href="plfa.Lambda.html#11539" class="Datatype">Value</a> <a id="8677" href="Assignment3.html#8649" class="Bound">M</a><a id="8678" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.


#### Exercise `mul-eval` (recommended)

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
