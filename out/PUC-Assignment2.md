---
src: tspl/PUC-Assignment2.lagda.md
title     : "PUC-Assignment2: PUC Assignment 2"
layout    : page
permalink : /PUC-Assignment2/
---

{% raw %}<pre class="Agda"><a id="109" class="Keyword">module</a> <a id="116" href="PUC-Assignment2.html" class="Module">PUC-Assignment2</a> <a id="132" class="Keyword">where</a>
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
<a id="700" class="Keyword">open</a> <a id="705" class="Keyword">import</a> <a id="712" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="721" class="Keyword">using</a> <a id="727" class="Symbol">(</a><a id="728" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="729" class="Symbol">;</a> <a id="731" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="735" class="Symbol">;</a> <a id="737" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="740" class="Symbol">;</a> <a id="742" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="745" class="Symbol">;</a> <a id="747" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="750" class="Symbol">;</a> <a id="752" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="755" class="Symbol">;</a> <a id="757" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="760" class="Symbol">;</a> <a id="762" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="765" class="Symbol">;</a> <a id="767" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="770" class="Symbol">)</a>
<a id="772" class="Keyword">open</a> <a id="777" class="Keyword">import</a> <a id="784" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="804" class="Keyword">using</a> <a id="810" class="Symbol">(</a><a id="811" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="818" class="Symbol">;</a> <a id="820" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="831" class="Symbol">;</a> <a id="833" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="838" class="Symbol">;</a> <a id="840" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="846" class="Symbol">;</a>
  <a id="850" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="856" class="Symbol">;</a> <a id="858" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="865" class="Symbol">;</a> <a id="867" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="876" class="Symbol">;</a> <a id="878" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="885" class="Symbol">;</a> <a id="887" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="896" class="Symbol">;</a> <a id="898" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="907" class="Symbol">;</a> <a id="909" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="917" class="Symbol">)</a>
<a id="919" class="Keyword">open</a> <a id="924" class="Keyword">import</a> <a id="931" href="plfa.Relations.html" class="Module">plfa.Relations</a> <a id="946" class="Keyword">using</a> <a id="952" class="Symbol">(</a><a id="953" href="plfa.Relations.html#18100" class="Datatype Operator">_&lt;_</a><a id="956" class="Symbol">;</a> <a id="958" href="plfa.Relations.html#18127" class="InductiveConstructor">z&lt;s</a><a id="961" class="Symbol">;</a> <a id="963" href="plfa.Relations.html#18184" class="InductiveConstructor">s&lt;s</a><a id="966" class="Symbol">)</a>
<a id="968" class="Keyword">open</a> <a id="973" class="Keyword">import</a> <a id="980" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="993" class="Keyword">using</a> <a id="999" class="Symbol">(</a><a id="1000" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1003" class="Symbol">;</a> <a id="1005" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="1010" class="Symbol">;</a> <a id="1012" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="1017" class="Symbol">)</a> <a id="1019" class="Keyword">renaming</a> <a id="1028" class="Symbol">(</a><a id="1029" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1033" class="Symbol">to</a> <a id="1036" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1041" class="Symbol">)</a>
<a id="1043" class="Keyword">open</a> <a id="1048" class="Keyword">import</a> <a id="1055" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1068" class="Keyword">using</a> <a id="1074" class="Symbol">(</a><a id="1075" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="1076" class="Symbol">;</a> <a id="1078" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="1079" class="Symbol">;</a> <a id="1081" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="1089" class="Symbol">;</a> <a id="1091" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="1099" class="Symbol">)</a>
<a id="1101" class="Keyword">open</a> <a id="1106" class="Keyword">import</a> <a id="1113" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="1123" class="Keyword">using</a> <a id="1129" class="Symbol">(</a><a id="1130" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="1131" class="Symbol">;</a> <a id="1133" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="1135" class="Symbol">)</a>
<a id="1137" class="Keyword">open</a> <a id="1142" class="Keyword">import</a> <a id="1149" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="1158" class="Keyword">using</a> <a id="1164" class="Symbol">(</a><a id="1165" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="1168" class="Symbol">;</a> <a id="1170" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="1174" class="Symbol">;</a> <a id="1176" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="1180" class="Symbol">)</a> <a id="1182" class="Keyword">renaming</a> <a id="1191" class="Symbol">(</a><a id="1192" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="1198" class="Symbol">to</a> <a id="1201" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="1207" class="Symbol">)</a>
<a id="1209" class="Keyword">open</a> <a id="1214" class="Keyword">import</a> <a id="1221" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1232" class="Keyword">using</a> <a id="1238" class="Symbol">(</a><a id="1239" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1240" class="Symbol">;</a> <a id="1242" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1248" class="Symbol">)</a>
<a id="1250" class="Keyword">open</a> <a id="1255" class="Keyword">import</a> <a id="1262" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="1277" class="Keyword">using</a> <a id="1283" class="Symbol">(</a><a id="1284" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="1288" class="Symbol">;</a> <a id="1290" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="1294" class="Symbol">;</a> <a id="1296" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="1301" class="Symbol">;</a> <a id="1303" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="1304" class="Symbol">;</a> <a id="1306" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="1309" class="Symbol">;</a> <a id="1311" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="1314" class="Symbol">;</a> <a id="1316" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="1319" class="Symbol">)</a>
<a id="1321" class="Keyword">open</a> <a id="1326" class="Keyword">import</a> <a id="1333" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1350" class="Keyword">using</a> <a id="1356" class="Symbol">(</a><a id="1357" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1359" class="Symbol">;</a> <a id="1361" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="1364" class="Symbol">;</a> <a id="1366" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="1369" class="Symbol">;</a> <a id="1371" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1373" class="Symbol">)</a>
<a id="1375" class="Keyword">open</a> <a id="1380" class="Keyword">import</a> <a id="1387" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.html" class="Module">Relation.Nullary.Decidable</a> <a id="1414" class="Keyword">using</a> <a id="1420" class="Symbol">(</a><a id="1421" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊_⌋</a><a id="1424" class="Symbol">;</a> <a id="1426" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#926" class="Function">toWitness</a><a id="1435" class="Symbol">;</a> <a id="1437" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#1062" class="Function">fromWitness</a><a id="1448" class="Symbol">)</a>
<a id="1450" class="Keyword">open</a> <a id="1455" class="Keyword">import</a> <a id="1462" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1488" class="Keyword">using</a> <a id="1494" class="Symbol">(</a><a id="1495" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a><a id="1497" class="Symbol">)</a>
<a id="1499" class="Keyword">open</a> <a id="1504" class="Keyword">import</a> <a id="1511" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html" class="Module">Relation.Nullary.Product</a> <a id="1536" class="Keyword">using</a> <a id="1542" class="Symbol">(</a><a id="1543" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">_×-dec_</a><a id="1550" class="Symbol">)</a>
<a id="1552" class="Keyword">open</a> <a id="1557" class="Keyword">import</a> <a id="1564" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html" class="Module">Relation.Nullary.Sum</a> <a id="1585" class="Keyword">using</a> <a id="1591" class="Symbol">(</a><a id="1592" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">_⊎-dec_</a><a id="1599" class="Symbol">)</a>
<a id="1601" class="Keyword">open</a> <a id="1606" class="Keyword">import</a> <a id="1613" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1639" class="Keyword">using</a> <a id="1645" class="Symbol">(</a><a id="1646" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#880" class="Function">contraposition</a><a id="1660" class="Symbol">)</a>
<a id="1662" class="Keyword">open</a> <a id="1667" class="Keyword">import</a> <a id="1674" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html" class="Module">Relation.Unary</a> <a id="1689" class="Keyword">using</a> <a id="1695" class="Symbol">(</a><a id="1696" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html#3474" class="Function">Decidable</a><a id="1705" class="Symbol">)</a>
<a id="1707" class="Keyword">open</a> <a id="1712" class="Keyword">import</a> <a id="1719" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="1728" class="Keyword">using</a> <a id="1734" class="Symbol">(</a><a id="1735" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="1738" class="Symbol">)</a>
<a id="1740" class="Keyword">open</a> <a id="1745" class="Keyword">import</a> <a id="1752" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="1758" class="Keyword">using</a> <a id="1764" class="Symbol">(</a><a id="1765" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="1770" class="Symbol">)</a>
<a id="1772" class="Keyword">open</a> <a id="1777" class="Keyword">import</a> <a id="1784" href="plfa.Relations.html" class="Module">plfa.Relations</a> <a id="1799" class="Keyword">using</a> <a id="1805" class="Symbol">(</a><a id="1806" href="plfa.Relations.html#18100" class="Datatype Operator">_&lt;_</a><a id="1809" class="Symbol">;</a> <a id="1811" href="plfa.Relations.html#18127" class="InductiveConstructor">z&lt;s</a><a id="1814" class="Symbol">;</a> <a id="1816" href="plfa.Relations.html#18184" class="InductiveConstructor">s&lt;s</a><a id="1819" class="Symbol">)</a>
<a id="1821" class="Keyword">open</a> <a id="1826" class="Keyword">import</a> <a id="1833" href="plfa.Isomorphism.html" class="Module">plfa.Isomorphism</a> <a id="1850" class="Keyword">using</a> <a id="1856" class="Symbol">(</a><a id="1857" href="plfa.Isomorphism.html#3955" class="Record Operator">_≃_</a><a id="1860" class="Symbol">;</a> <a id="1862" href="plfa.Isomorphism.html#6602" class="Function">≃-sym</a><a id="1867" class="Symbol">;</a> <a id="1869" href="plfa.Isomorphism.html#6927" class="Function">≃-trans</a><a id="1876" class="Symbol">;</a> <a id="1878" href="plfa.Isomorphism.html#8776" class="Record Operator">_≲_</a><a id="1881" class="Symbol">;</a> <a id="1883" href="plfa.Isomorphism.html#2663" class="Postulate">extensionality</a><a id="1897" class="Symbol">)</a>
<a id="1899" class="Keyword">open</a> <a id="1904" href="plfa.Isomorphism.html#8011" class="Module">plfa.Isomorphism.≃-Reasoning</a>
<a id="1933" class="Keyword">open</a> <a id="1938" class="Keyword">import</a> <a id="1945" href="plfa.Lists.html" class="Module">plfa.Lists</a> <a id="1956" class="Keyword">using</a> <a id="1962" class="Symbol">(</a><a id="1963" href="plfa.Lists.html#1055" class="Datatype">List</a><a id="1967" class="Symbol">;</a> <a id="1969" href="plfa.Lists.html#1084" class="InductiveConstructor">[]</a><a id="1971" class="Symbol">;</a> <a id="1973" href="plfa.Lists.html#1099" class="InductiveConstructor Operator">_∷_</a><a id="1976" class="Symbol">;</a> <a id="1978" href="plfa.Lists.html#2815" class="Operator">[_]</a><a id="1981" class="Symbol">;</a> <a id="1983" href="plfa.Lists.html#2838" class="Operator">[_,_]</a><a id="1988" class="Symbol">;</a> <a id="1990" href="plfa.Lists.html#2869" class="Operator">[_,_,_]</a><a id="1997" class="Symbol">;</a> <a id="1999" href="plfa.Lists.html#2908" class="Operator">[_,_,_,_]</a><a id="2008" class="Symbol">;</a>
  <a id="2012" href="plfa.Lists.html#3455" class="Function Operator">_++_</a><a id="2016" class="Symbol">;</a> <a id="2018" href="plfa.Lists.html#8294" class="Function">reverse</a><a id="2025" class="Symbol">;</a> <a id="2027" href="plfa.Lists.html#12979" class="Function">map</a><a id="2030" class="Symbol">;</a> <a id="2032" href="plfa.Lists.html#15448" class="Function">foldr</a><a id="2037" class="Symbol">;</a> <a id="2039" href="plfa.Lists.html#16343" class="Function">sum</a><a id="2042" class="Symbol">;</a> <a id="2044" href="plfa.Lists.html#21045" class="Datatype">All</a><a id="2047" class="Symbol">;</a> <a id="2049" href="plfa.Lists.html#22498" class="Datatype">Any</a><a id="2052" class="Symbol">;</a> <a id="2054" href="plfa.Lists.html#22549" class="InductiveConstructor">here</a><a id="2058" class="Symbol">;</a> <a id="2060" href="plfa.Lists.html#22606" class="InductiveConstructor">there</a><a id="2065" class="Symbol">;</a> <a id="2067" href="plfa.Lists.html#22920" class="Function Operator">_∈_</a><a id="2070" class="Symbol">)</a>
</pre>{% endraw %}
## Equality

#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations][plfa.Relations]
can be written in a more readable form by using an analogue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.



## Isomorphism

#### Exercise `≃-implies-≲`

Show that every isomorphism implies an embedding.
{% raw %}<pre class="Agda"><a id="2569" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="2581" href="PUC-Assignment2.html#2581" class="Postulate">≃-implies-≲</a> <a id="2593" class="Symbol">:</a> <a id="2595" class="Symbol">∀</a> <a id="2597" class="Symbol">{</a><a id="2598" href="PUC-Assignment2.html#2598" class="Bound">A</a> <a id="2600" href="PUC-Assignment2.html#2600" class="Bound">B</a> <a id="2602" class="Symbol">:</a> <a id="2604" class="PrimitiveType">Set</a><a id="2607" class="Symbol">}</a>
    <a id="2613" class="Symbol">→</a> <a id="2615" href="PUC-Assignment2.html#2598" class="Bound">A</a> <a id="2617" href="plfa.Isomorphism.html#3955" class="Record Operator">≃</a> <a id="2619" href="PUC-Assignment2.html#2600" class="Bound">B</a>
      <a id="2627" class="Comment">-----</a>
    <a id="2637" class="Symbol">→</a> <a id="2639" href="PUC-Assignment2.html#2598" class="Bound">A</a> <a id="2641" href="plfa.Isomorphism.html#8776" class="Record Operator">≲</a> <a id="2643" href="PUC-Assignment2.html#2600" class="Bound">B</a>
</pre>{% endraw %}
#### Exercise `_⇔_` (recommended) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows.
{% raw %}<pre class="Agda"><a id="2776" class="Keyword">record</a> <a id="_⇔_"></a><a id="2783" href="PUC-Assignment2.html#2783" class="Record Operator">_⇔_</a> <a id="2787" class="Symbol">(</a><a id="2788" href="PUC-Assignment2.html#2788" class="Bound">A</a> <a id="2790" href="PUC-Assignment2.html#2790" class="Bound">B</a> <a id="2792" class="Symbol">:</a> <a id="2794" class="PrimitiveType">Set</a><a id="2797" class="Symbol">)</a> <a id="2799" class="Symbol">:</a> <a id="2801" class="PrimitiveType">Set</a> <a id="2805" class="Keyword">where</a>
  <a id="2813" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="2823" href="PUC-Assignment2.html#2823" class="Field">to</a>   <a id="2828" class="Symbol">:</a> <a id="2830" href="PUC-Assignment2.html#2788" class="Bound">A</a> <a id="2832" class="Symbol">→</a> <a id="2834" href="PUC-Assignment2.html#2790" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="2840" href="PUC-Assignment2.html#2840" class="Field">from</a> <a id="2845" class="Symbol">:</a> <a id="2847" href="PUC-Assignment2.html#2790" class="Bound">B</a> <a id="2849" class="Symbol">→</a> <a id="2851" href="PUC-Assignment2.html#2788" class="Bound">A</a>

<a id="2854" class="Keyword">open</a> <a id="2859" href="PUC-Assignment2.html#2783" class="Module Operator">_⇔_</a>
</pre>{% endraw %}Show that equivalence is reflexive, symmetric, and transitive.

#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin][plfa.Naturals#Bin] and
[Bin-laws][plfa.Induction#Bin-laws]
define a datatype of bitstrings representing natural numbers.
{% raw %}<pre class="Agda"><a id="3142" class="Keyword">data</a> <a id="Bin"></a><a id="3147" href="PUC-Assignment2.html#3147" class="Datatype">Bin</a> <a id="3151" class="Symbol">:</a> <a id="3153" class="PrimitiveType">Set</a> <a id="3157" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="3165" href="PUC-Assignment2.html#3165" class="InductiveConstructor">nil</a> <a id="3169" class="Symbol">:</a> <a id="3171" href="PUC-Assignment2.html#3147" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="3177" href="PUC-Assignment2.html#3177" class="InductiveConstructor Operator">x0_</a> <a id="3181" class="Symbol">:</a> <a id="3183" href="PUC-Assignment2.html#3147" class="Datatype">Bin</a> <a id="3187" class="Symbol">→</a> <a id="3189" href="PUC-Assignment2.html#3147" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="3195" href="PUC-Assignment2.html#3195" class="InductiveConstructor Operator">x1_</a> <a id="3199" class="Symbol">:</a> <a id="3201" href="PUC-Assignment2.html#3147" class="Datatype">Bin</a> <a id="3205" class="Symbol">→</a> <a id="3207" href="PUC-Assignment2.html#3147" class="Datatype">Bin</a>
</pre>{% endraw %}And ask you to define the following functions:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
Why is there not an isomorphism?


## Connectives

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier][plfa.Isomorphism#iff]
is isomorphic to `(A → B) × (B → A)`.

#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

#### Exercise `⊎-assoc`

Show sum is associative up to isomorphism.

#### Exercise `⊥-identityˡ` (recommended)

Show zero is the left identity of addition.

#### Exercise `⊥-identityʳ`

Show zero is the right identity of addition.

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds.
{% raw %}<pre class="Agda"><a id="4017" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="4029" href="PUC-Assignment2.html#4029" class="Postulate">⊎-weak-×</a> <a id="4038" class="Symbol">:</a> <a id="4040" class="Symbol">∀</a> <a id="4042" class="Symbol">{</a><a id="4043" href="PUC-Assignment2.html#4043" class="Bound">A</a> <a id="4045" href="PUC-Assignment2.html#4045" class="Bound">B</a> <a id="4047" href="PUC-Assignment2.html#4047" class="Bound">C</a> <a id="4049" class="Symbol">:</a> <a id="4051" class="PrimitiveType">Set</a><a id="4054" class="Symbol">}</a> <a id="4056" class="Symbol">→</a> <a id="4058" class="Symbol">(</a><a id="4059" href="PUC-Assignment2.html#4043" class="Bound">A</a> <a id="4061" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4063" href="PUC-Assignment2.html#4045" class="Bound">B</a><a id="4064" class="Symbol">)</a> <a id="4066" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4068" href="PUC-Assignment2.html#4047" class="Bound">C</a> <a id="4070" class="Symbol">→</a> <a id="4072" href="PUC-Assignment2.html#4043" class="Bound">A</a> <a id="4074" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4076" class="Symbol">(</a><a id="4077" href="PUC-Assignment2.html#4045" class="Bound">B</a> <a id="4079" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4081" href="PUC-Assignment2.html#4047" class="Bound">C</a><a id="4082" class="Symbol">)</a>
</pre>{% endraw %}This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

#### Exercise `⊎×-implies-×⊎`

Show that a disjunct of conjuncts implies a conjunct of disjuncts.
{% raw %}<pre class="Agda"><a id="4322" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="4334" href="PUC-Assignment2.html#4334" class="Postulate">⊎×-implies-×⊎</a> <a id="4348" class="Symbol">:</a> <a id="4350" class="Symbol">∀</a> <a id="4352" class="Symbol">{</a><a id="4353" href="PUC-Assignment2.html#4353" class="Bound">A</a> <a id="4355" href="PUC-Assignment2.html#4355" class="Bound">B</a> <a id="4357" href="PUC-Assignment2.html#4357" class="Bound">C</a> <a id="4359" href="PUC-Assignment2.html#4359" class="Bound">D</a> <a id="4361" class="Symbol">:</a> <a id="4363" class="PrimitiveType">Set</a><a id="4366" class="Symbol">}</a> <a id="4368" class="Symbol">→</a> <a id="4370" class="Symbol">(</a><a id="4371" href="PUC-Assignment2.html#4353" class="Bound">A</a> <a id="4373" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4375" href="PUC-Assignment2.html#4355" class="Bound">B</a><a id="4376" class="Symbol">)</a> <a id="4378" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4380" class="Symbol">(</a><a id="4381" href="PUC-Assignment2.html#4357" class="Bound">C</a> <a id="4383" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4385" href="PUC-Assignment2.html#4359" class="Bound">D</a><a id="4386" class="Symbol">)</a> <a id="4388" class="Symbol">→</a> <a id="4390" class="Symbol">(</a><a id="4391" href="PUC-Assignment2.html#4353" class="Bound">A</a> <a id="4393" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4395" href="PUC-Assignment2.html#4357" class="Bound">C</a><a id="4396" class="Symbol">)</a> <a id="4398" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4400" class="Symbol">(</a><a id="4401" href="PUC-Assignment2.html#4355" class="Bound">B</a> <a id="4403" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4405" href="PUC-Assignment2.html#4359" class="Bound">D</a><a id="4406" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, give a counterexample.


## Negation

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality][plfa.Relations#strict-inequality]
is irreflexive, that is, `n < n` holds for no `n`.


#### Exercise `trichotomy`

Show that strict inequality satisfies
[trichotomy][plfa.Relations#trichotomy],
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that one of the three must hold, and each implies the
negation of the other two.


#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, give a variant that does hold.


#### Exercise `Classical` (stretch)

Consider the following principles.

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it.
{% raw %}<pre class="Agda"><a id="Stable"></a><a id="5888" href="PUC-Assignment2.html#5888" class="Function">Stable</a> <a id="5895" class="Symbol">:</a> <a id="5897" class="PrimitiveType">Set</a> <a id="5901" class="Symbol">→</a> <a id="5903" class="PrimitiveType">Set</a>
<a id="5907" href="PUC-Assignment2.html#5888" class="Function">Stable</a> <a id="5914" href="PUC-Assignment2.html#5914" class="Bound">A</a> <a id="5916" class="Symbol">=</a> <a id="5918" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="5920" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="5922" href="PUC-Assignment2.html#5914" class="Bound">A</a> <a id="5924" class="Symbol">→</a> <a id="5926" href="PUC-Assignment2.html#5914" class="Bound">A</a>
</pre>{% endraw %}Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.


## Quantifiers

#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction.
{% raw %}<pre class="Agda"><a id="6147" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="6159" href="PUC-Assignment2.html#6159" class="Postulate">∀-distrib-×</a> <a id="6171" class="Symbol">:</a> <a id="6173" class="Symbol">∀</a> <a id="6175" class="Symbol">{</a><a id="6176" href="PUC-Assignment2.html#6176" class="Bound">A</a> <a id="6178" class="Symbol">:</a> <a id="6180" class="PrimitiveType">Set</a><a id="6183" class="Symbol">}</a> <a id="6185" class="Symbol">{</a><a id="6186" href="PUC-Assignment2.html#6186" class="Bound">B</a> <a id="6188" href="PUC-Assignment2.html#6188" class="Bound">C</a> <a id="6190" class="Symbol">:</a> <a id="6192" href="PUC-Assignment2.html#6176" class="Bound">A</a> <a id="6194" class="Symbol">→</a> <a id="6196" class="PrimitiveType">Set</a><a id="6199" class="Symbol">}</a> <a id="6201" class="Symbol">→</a>
    <a id="6207" class="Symbol">(∀</a> <a id="6210" class="Symbol">(</a><a id="6211" href="PUC-Assignment2.html#6211" class="Bound">x</a> <a id="6213" class="Symbol">:</a> <a id="6215" href="PUC-Assignment2.html#6176" class="Bound">A</a><a id="6216" class="Symbol">)</a> <a id="6218" class="Symbol">→</a> <a id="6220" href="PUC-Assignment2.html#6186" class="Bound">B</a> <a id="6222" href="PUC-Assignment2.html#6211" class="Bound">x</a> <a id="6224" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6226" href="PUC-Assignment2.html#6188" class="Bound">C</a> <a id="6228" href="PUC-Assignment2.html#6211" class="Bound">x</a><a id="6229" class="Symbol">)</a> <a id="6231" href="plfa.Isomorphism.html#3955" class="Record Operator">≃</a> <a id="6233" class="Symbol">(∀</a> <a id="6236" class="Symbol">(</a><a id="6237" href="PUC-Assignment2.html#6237" class="Bound">x</a> <a id="6239" class="Symbol">:</a> <a id="6241" href="PUC-Assignment2.html#6176" class="Bound">A</a><a id="6242" class="Symbol">)</a> <a id="6244" class="Symbol">→</a> <a id="6246" href="PUC-Assignment2.html#6186" class="Bound">B</a> <a id="6248" href="PUC-Assignment2.html#6237" class="Bound">x</a><a id="6249" class="Symbol">)</a> <a id="6251" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6253" class="Symbol">(∀</a> <a id="6256" class="Symbol">(</a><a id="6257" href="PUC-Assignment2.html#6257" class="Bound">x</a> <a id="6259" class="Symbol">:</a> <a id="6261" href="PUC-Assignment2.html#6176" class="Bound">A</a><a id="6262" class="Symbol">)</a> <a id="6264" class="Symbol">→</a> <a id="6266" href="PUC-Assignment2.html#6188" class="Bound">C</a> <a id="6268" href="PUC-Assignment2.html#6257" class="Bound">x</a><a id="6269" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives][plfa.Connectives].

#### Exercise `⊎∀-implies-∀⊎`

Show that a disjunction of universals implies a universal of disjunctions.
{% raw %}<pre class="Agda"><a id="6475" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="6487" href="PUC-Assignment2.html#6487" class="Postulate">⊎∀-implies-∀⊎</a> <a id="6501" class="Symbol">:</a> <a id="6503" class="Symbol">∀</a> <a id="6505" class="Symbol">{</a><a id="6506" href="PUC-Assignment2.html#6506" class="Bound">A</a> <a id="6508" class="Symbol">:</a> <a id="6510" class="PrimitiveType">Set</a><a id="6513" class="Symbol">}</a> <a id="6515" class="Symbol">{</a> <a id="6517" href="PUC-Assignment2.html#6517" class="Bound">B</a> <a id="6519" href="PUC-Assignment2.html#6519" class="Bound">C</a> <a id="6521" class="Symbol">:</a> <a id="6523" href="PUC-Assignment2.html#6506" class="Bound">A</a> <a id="6525" class="Symbol">→</a> <a id="6527" class="PrimitiveType">Set</a> <a id="6531" class="Symbol">}</a> <a id="6533" class="Symbol">→</a>
    <a id="6539" class="Symbol">(∀</a> <a id="6542" class="Symbol">(</a><a id="6543" href="PUC-Assignment2.html#6543" class="Bound">x</a> <a id="6545" class="Symbol">:</a> <a id="6547" href="PUC-Assignment2.html#6506" class="Bound">A</a><a id="6548" class="Symbol">)</a> <a id="6550" class="Symbol">→</a> <a id="6552" href="PUC-Assignment2.html#6517" class="Bound">B</a> <a id="6554" href="PUC-Assignment2.html#6543" class="Bound">x</a><a id="6555" class="Symbol">)</a> <a id="6557" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6559" class="Symbol">(∀</a> <a id="6562" class="Symbol">(</a><a id="6563" href="PUC-Assignment2.html#6563" class="Bound">x</a> <a id="6565" class="Symbol">:</a> <a id="6567" href="PUC-Assignment2.html#6506" class="Bound">A</a><a id="6568" class="Symbol">)</a> <a id="6570" class="Symbol">→</a> <a id="6572" href="PUC-Assignment2.html#6519" class="Bound">C</a> <a id="6574" href="PUC-Assignment2.html#6563" class="Bound">x</a><a id="6575" class="Symbol">)</a>  <a id="6578" class="Symbol">→</a>  <a id="6581" class="Symbol">∀</a> <a id="6583" class="Symbol">(</a><a id="6584" href="PUC-Assignment2.html#6584" class="Bound">x</a> <a id="6586" class="Symbol">:</a> <a id="6588" href="PUC-Assignment2.html#6506" class="Bound">A</a><a id="6589" class="Symbol">)</a> <a id="6591" class="Symbol">→</a> <a id="6593" href="PUC-Assignment2.html#6517" class="Bound">B</a> <a id="6595" href="PUC-Assignment2.html#6584" class="Bound">x</a> <a id="6597" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6599" href="PUC-Assignment2.html#6519" class="Bound">C</a> <a id="6601" href="PUC-Assignment2.html#6584" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction.
{% raw %}<pre class="Agda"><a id="6766" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="6778" href="PUC-Assignment2.html#6778" class="Postulate">∃-distrib-⊎</a> <a id="6790" class="Symbol">:</a> <a id="6792" class="Symbol">∀</a> <a id="6794" class="Symbol">{</a><a id="6795" href="PUC-Assignment2.html#6795" class="Bound">A</a> <a id="6797" class="Symbol">:</a> <a id="6799" class="PrimitiveType">Set</a><a id="6802" class="Symbol">}</a> <a id="6804" class="Symbol">{</a><a id="6805" href="PUC-Assignment2.html#6805" class="Bound">B</a> <a id="6807" href="PUC-Assignment2.html#6807" class="Bound">C</a> <a id="6809" class="Symbol">:</a> <a id="6811" href="PUC-Assignment2.html#6795" class="Bound">A</a> <a id="6813" class="Symbol">→</a> <a id="6815" class="PrimitiveType">Set</a><a id="6818" class="Symbol">}</a> <a id="6820" class="Symbol">→</a>
    <a id="6826" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6829" href="PUC-Assignment2.html#6829" class="Bound">x</a> <a id="6831" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6833" class="Symbol">(</a><a id="6834" href="PUC-Assignment2.html#6805" class="Bound">B</a> <a id="6836" href="PUC-Assignment2.html#6829" class="Bound">x</a> <a id="6838" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6840" href="PUC-Assignment2.html#6807" class="Bound">C</a> <a id="6842" href="PUC-Assignment2.html#6829" class="Bound">x</a><a id="6843" class="Symbol">)</a> <a id="6845" href="plfa.Isomorphism.html#3955" class="Record Operator">≃</a> <a id="6847" class="Symbol">(</a><a id="6848" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6851" href="PUC-Assignment2.html#6851" class="Bound">x</a> <a id="6853" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6855" href="PUC-Assignment2.html#6805" class="Bound">B</a> <a id="6857" href="PUC-Assignment2.html#6851" class="Bound">x</a><a id="6858" class="Symbol">)</a> <a id="6860" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6862" class="Symbol">(</a><a id="6863" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6866" href="PUC-Assignment2.html#6866" class="Bound">x</a> <a id="6868" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6870" href="PUC-Assignment2.html#6807" class="Bound">C</a> <a id="6872" href="PUC-Assignment2.html#6866" class="Bound">x</a><a id="6873" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `∃×-implies-×∃`

Show that an existential of conjunctions implies a conjunction of existentials.
{% raw %}<pre class="Agda"><a id="6995" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="7007" href="PUC-Assignment2.html#7007" class="Postulate">∃×-implies-×∃</a> <a id="7021" class="Symbol">:</a> <a id="7023" class="Symbol">∀</a> <a id="7025" class="Symbol">{</a><a id="7026" href="PUC-Assignment2.html#7026" class="Bound">A</a> <a id="7028" class="Symbol">:</a> <a id="7030" class="PrimitiveType">Set</a><a id="7033" class="Symbol">}</a> <a id="7035" class="Symbol">{</a> <a id="7037" href="PUC-Assignment2.html#7037" class="Bound">B</a> <a id="7039" href="PUC-Assignment2.html#7039" class="Bound">C</a> <a id="7041" class="Symbol">:</a> <a id="7043" href="PUC-Assignment2.html#7026" class="Bound">A</a> <a id="7045" class="Symbol">→</a> <a id="7047" class="PrimitiveType">Set</a> <a id="7051" class="Symbol">}</a> <a id="7053" class="Symbol">→</a>
    <a id="7059" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7062" href="PUC-Assignment2.html#7062" class="Bound">x</a> <a id="7064" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7066" class="Symbol">(</a><a id="7067" href="PUC-Assignment2.html#7037" class="Bound">B</a> <a id="7069" href="PUC-Assignment2.html#7062" class="Bound">x</a> <a id="7071" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="7073" href="PUC-Assignment2.html#7039" class="Bound">C</a> <a id="7075" href="PUC-Assignment2.html#7062" class="Bound">x</a><a id="7076" class="Symbol">)</a> <a id="7078" class="Symbol">→</a> <a id="7080" class="Symbol">(</a><a id="7081" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7084" href="PUC-Assignment2.html#7084" class="Bound">x</a> <a id="7086" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7088" href="PUC-Assignment2.html#7037" class="Bound">B</a> <a id="7090" href="PUC-Assignment2.html#7084" class="Bound">x</a><a id="7091" class="Symbol">)</a> <a id="7093" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="7095" class="Symbol">(</a><a id="7096" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7099" href="PUC-Assignment2.html#7099" class="Bound">x</a> <a id="7101" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7103" href="PUC-Assignment2.html#7039" class="Bound">C</a> <a id="7105" href="PUC-Assignment2.html#7099" class="Bound">x</a><a id="7106" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-even-odd`

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

#### Exercise `∃-|-≤`

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal.
{% raw %}<pre class="Agda"><a id="7601" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="7613" href="PUC-Assignment2.html#7613" class="Postulate">∃¬-implies-¬∀</a> <a id="7627" class="Symbol">:</a> <a id="7629" class="Symbol">∀</a> <a id="7631" class="Symbol">{</a><a id="7632" href="PUC-Assignment2.html#7632" class="Bound">A</a> <a id="7634" class="Symbol">:</a> <a id="7636" class="PrimitiveType">Set</a><a id="7639" class="Symbol">}</a> <a id="7641" class="Symbol">{</a><a id="7642" href="PUC-Assignment2.html#7642" class="Bound">B</a> <a id="7644" class="Symbol">:</a> <a id="7646" href="PUC-Assignment2.html#7632" class="Bound">A</a> <a id="7648" class="Symbol">→</a> <a id="7650" class="PrimitiveType">Set</a><a id="7653" class="Symbol">}</a>
    <a id="7659" class="Symbol">→</a> <a id="7661" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7664" href="PUC-Assignment2.html#7664" class="Bound">x</a> <a id="7666" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7668" class="Symbol">(</a><a id="7669" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7671" href="PUC-Assignment2.html#7642" class="Bound">B</a> <a id="7673" href="PUC-Assignment2.html#7664" class="Bound">x</a><a id="7674" class="Symbol">)</a>
      <a id="7682" class="Comment">--------------</a>
    <a id="7701" class="Symbol">→</a> <a id="7703" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7705" class="Symbol">(∀</a> <a id="7708" href="PUC-Assignment2.html#7708" class="Bound">x</a> <a id="7710" class="Symbol">→</a> <a id="7712" href="PUC-Assignment2.html#7642" class="Bound">B</a> <a id="7714" href="PUC-Assignment2.html#7708" class="Bound">x</a><a id="7715" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin][plfa.Naturals#Bin],
[Bin-laws][plfa.Induction#Bin-laws], and
[Bin-predicates][plfa.Relations#Bin-predicates]
define a datatype of bitstrings representing natural numbers.

    data Bin : Set where
      nil : Bin
      x0_ : Bin → Bin
      x1_ : Bin → Bin

And ask you to define the following functions and predicates.

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties.

    from (to n) ≡ n

    ----------
    Can (to n)

    Can x
    ---------------
    to (from x) ≡ x

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ x ](Can x)`.


## Decidable

#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality.
{% raw %}<pre class="Agda"><a id="8625" class="Keyword">postulate</a>
  <a id="_&lt;?_"></a><a id="8637" href="PUC-Assignment2.html#8637" class="Postulate Operator">_&lt;?_</a> <a id="8642" class="Symbol">:</a> <a id="8644" class="Symbol">∀</a> <a id="8646" class="Symbol">(</a><a id="8647" href="PUC-Assignment2.html#8647" class="Bound">m</a> <a id="8649" href="PUC-Assignment2.html#8649" class="Bound">n</a> <a id="8651" class="Symbol">:</a> <a id="8653" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8654" class="Symbol">)</a> <a id="8656" class="Symbol">→</a> <a id="8658" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8662" class="Symbol">(</a><a id="8663" href="PUC-Assignment2.html#8647" class="Bound">m</a> <a id="8665" href="plfa.Relations.html#18100" class="Datatype Operator">&lt;</a> <a id="8667" href="PUC-Assignment2.html#8649" class="Bound">n</a><a id="8668" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `_≡ℕ?_`

Define a function to decide whether two naturals are equal.
{% raw %}<pre class="Agda"><a id="8762" class="Keyword">postulate</a>
  <a id="_≡ℕ?_"></a><a id="8774" href="PUC-Assignment2.html#8774" class="Postulate Operator">_≡ℕ?_</a> <a id="8780" class="Symbol">:</a> <a id="8782" class="Symbol">∀</a> <a id="8784" class="Symbol">(</a><a id="8785" href="PUC-Assignment2.html#8785" class="Bound">m</a> <a id="8787" href="PUC-Assignment2.html#8787" class="Bound">n</a> <a id="8789" class="Symbol">:</a> <a id="8791" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8792" class="Symbol">)</a> <a id="8794" class="Symbol">→</a> <a id="8796" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8800" class="Symbol">(</a><a id="8801" href="PUC-Assignment2.html#8785" class="Bound">m</a> <a id="8803" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8805" href="PUC-Assignment2.html#8787" class="Bound">n</a><a id="8806" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `erasure`

Show that erasure relates corresponding boolean and decidable operations.
{% raw %}<pre class="Agda"><a id="8917" class="Keyword">postulate</a>
  <a id="∧-×"></a><a id="8929" href="PUC-Assignment2.html#8929" class="Postulate">∧-×</a> <a id="8933" class="Symbol">:</a> <a id="8935" class="Symbol">∀</a> <a id="8937" class="Symbol">{</a><a id="8938" href="PUC-Assignment2.html#8938" class="Bound">A</a> <a id="8940" href="PUC-Assignment2.html#8940" class="Bound">B</a> <a id="8942" class="Symbol">:</a> <a id="8944" class="PrimitiveType">Set</a><a id="8947" class="Symbol">}</a> <a id="8949" class="Symbol">(</a><a id="8950" href="PUC-Assignment2.html#8950" class="Bound">x</a> <a id="8952" class="Symbol">:</a> <a id="8954" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8958" href="PUC-Assignment2.html#8938" class="Bound">A</a><a id="8959" class="Symbol">)</a> <a id="8961" class="Symbol">(</a><a id="8962" href="PUC-Assignment2.html#8962" class="Bound">y</a> <a id="8964" class="Symbol">:</a> <a id="8966" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8970" href="PUC-Assignment2.html#8940" class="Bound">B</a><a id="8971" class="Symbol">)</a> <a id="8973" class="Symbol">→</a> <a id="8975" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8977" href="PUC-Assignment2.html#8950" class="Bound">x</a> <a id="8979" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8981" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">∧</a> <a id="8983" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8985" href="PUC-Assignment2.html#8962" class="Bound">y</a> <a id="8987" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8989" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8991" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8993" href="PUC-Assignment2.html#8950" class="Bound">x</a> <a id="8995" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">×-dec</a> <a id="9001" href="PUC-Assignment2.html#8962" class="Bound">y</a> <a id="9003" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="∨-×"></a><a id="9007" href="PUC-Assignment2.html#9007" class="Postulate">∨-×</a> <a id="9011" class="Symbol">:</a> <a id="9013" class="Symbol">∀</a> <a id="9015" class="Symbol">{</a><a id="9016" href="PUC-Assignment2.html#9016" class="Bound">A</a> <a id="9018" href="PUC-Assignment2.html#9018" class="Bound">B</a> <a id="9020" class="Symbol">:</a> <a id="9022" class="PrimitiveType">Set</a><a id="9025" class="Symbol">}</a> <a id="9027" class="Symbol">(</a><a id="9028" href="PUC-Assignment2.html#9028" class="Bound">x</a> <a id="9030" class="Symbol">:</a> <a id="9032" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9036" href="PUC-Assignment2.html#9016" class="Bound">A</a><a id="9037" class="Symbol">)</a> <a id="9039" class="Symbol">(</a><a id="9040" href="PUC-Assignment2.html#9040" class="Bound">y</a> <a id="9042" class="Symbol">:</a> <a id="9044" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9048" href="PUC-Assignment2.html#9018" class="Bound">B</a><a id="9049" class="Symbol">)</a> <a id="9051" class="Symbol">→</a> <a id="9053" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9055" href="PUC-Assignment2.html#9028" class="Bound">x</a> <a id="9057" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9059" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">∨</a> <a id="9061" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9063" href="PUC-Assignment2.html#9040" class="Bound">y</a> <a id="9065" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9067" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9069" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9071" href="PUC-Assignment2.html#9028" class="Bound">x</a> <a id="9073" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">⊎-dec</a> <a id="9079" href="PUC-Assignment2.html#9040" class="Bound">y</a> <a id="9081" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="not-¬"></a><a id="9085" href="PUC-Assignment2.html#9085" class="Postulate">not-¬</a> <a id="9091" class="Symbol">:</a> <a id="9093" class="Symbol">∀</a> <a id="9095" class="Symbol">{</a><a id="9096" href="PUC-Assignment2.html#9096" class="Bound">A</a> <a id="9098" class="Symbol">:</a> <a id="9100" class="PrimitiveType">Set</a><a id="9103" class="Symbol">}</a> <a id="9105" class="Symbol">(</a><a id="9106" href="PUC-Assignment2.html#9106" class="Bound">x</a> <a id="9108" class="Symbol">:</a> <a id="9110" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9114" href="PUC-Assignment2.html#9096" class="Bound">A</a><a id="9115" class="Symbol">)</a> <a id="9117" class="Symbol">→</a> <a id="9119" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a> <a id="9123" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9125" href="PUC-Assignment2.html#9106" class="Bound">x</a> <a id="9127" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9129" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9131" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9133" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a> <a id="9136" href="PUC-Assignment2.html#9106" class="Bound">x</a> <a id="9138" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from
Chapter [Isomorphism][plfa.Isomorphism#iff],
operation on booleans and decidables, and also show the corresponding erasure.
{% raw %}<pre class="Agda"><a id="9359" class="Keyword">postulate</a>
  <a id="_iff_"></a><a id="9371" href="PUC-Assignment2.html#9371" class="Postulate Operator">_iff_</a> <a id="9377" class="Symbol">:</a> <a id="9379" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="9384" class="Symbol">→</a> <a id="9386" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="9391" class="Symbol">→</a> <a id="9393" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a>
  <a id="_⇔-dec_"></a><a id="9400" href="PUC-Assignment2.html#9400" class="Postulate Operator">_⇔-dec_</a> <a id="9408" class="Symbol">:</a> <a id="9410" class="Symbol">∀</a> <a id="9412" class="Symbol">{</a><a id="9413" href="PUC-Assignment2.html#9413" class="Bound">A</a> <a id="9415" href="PUC-Assignment2.html#9415" class="Bound">B</a> <a id="9417" class="Symbol">:</a> <a id="9419" class="PrimitiveType">Set</a><a id="9422" class="Symbol">}</a> <a id="9424" class="Symbol">→</a> <a id="9426" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9430" href="PUC-Assignment2.html#9413" class="Bound">A</a> <a id="9432" class="Symbol">→</a> <a id="9434" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9438" href="PUC-Assignment2.html#9415" class="Bound">B</a> <a id="9440" class="Symbol">→</a> <a id="9442" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9446" class="Symbol">(</a><a id="9447" href="PUC-Assignment2.html#9413" class="Bound">A</a> <a id="9449" href="PUC-Assignment2.html#2783" class="Record Operator">⇔</a> <a id="9451" href="PUC-Assignment2.html#9415" class="Bound">B</a><a id="9452" class="Symbol">)</a>
  <a id="iff-⇔"></a><a id="9456" href="PUC-Assignment2.html#9456" class="Postulate">iff-⇔</a> <a id="9462" class="Symbol">:</a> <a id="9464" class="Symbol">∀</a> <a id="9466" class="Symbol">{</a><a id="9467" href="PUC-Assignment2.html#9467" class="Bound">A</a> <a id="9469" href="PUC-Assignment2.html#9469" class="Bound">B</a> <a id="9471" class="Symbol">:</a> <a id="9473" class="PrimitiveType">Set</a><a id="9476" class="Symbol">}</a> <a id="9478" class="Symbol">(</a><a id="9479" href="PUC-Assignment2.html#9479" class="Bound">x</a> <a id="9481" class="Symbol">:</a> <a id="9483" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9487" href="PUC-Assignment2.html#9467" class="Bound">A</a><a id="9488" class="Symbol">)</a> <a id="9490" class="Symbol">(</a><a id="9491" href="PUC-Assignment2.html#9491" class="Bound">y</a> <a id="9493" class="Symbol">:</a> <a id="9495" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9499" href="PUC-Assignment2.html#9469" class="Bound">B</a><a id="9500" class="Symbol">)</a> <a id="9502" class="Symbol">→</a> <a id="9504" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9506" href="PUC-Assignment2.html#9479" class="Bound">x</a> <a id="9508" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9510" href="PUC-Assignment2.html#9371" class="Postulate Operator">iff</a> <a id="9514" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9516" href="PUC-Assignment2.html#9491" class="Bound">y</a> <a id="9518" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9520" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9522" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9524" href="PUC-Assignment2.html#9479" class="Bound">x</a> <a id="9526" href="PUC-Assignment2.html#9400" class="Postulate Operator">⇔-dec</a> <a id="9532" href="PUC-Assignment2.html#9491" class="Bound">y</a> <a id="9534" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
## Lists

#### Exercise `reverse-++-commute` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first.
{% raw %}<pre class="Agda"><a id="9726" class="Keyword">postulate</a>
  <a id="reverse-++-commute"></a><a id="9738" href="PUC-Assignment2.html#9738" class="Postulate">reverse-++-commute</a> <a id="9757" class="Symbol">:</a> <a id="9759" class="Symbol">∀</a> <a id="9761" class="Symbol">{</a><a id="9762" href="PUC-Assignment2.html#9762" class="Bound">A</a> <a id="9764" class="Symbol">:</a> <a id="9766" class="PrimitiveType">Set</a><a id="9769" class="Symbol">}</a> <a id="9771" class="Symbol">{</a><a id="9772" href="PUC-Assignment2.html#9772" class="Bound">xs</a> <a id="9775" href="PUC-Assignment2.html#9775" class="Bound">ys</a> <a id="9778" class="Symbol">:</a> <a id="9780" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="9785" href="PUC-Assignment2.html#9762" class="Bound">A</a><a id="9786" class="Symbol">}</a>
    <a id="9792" class="Symbol">→</a> <a id="9794" href="plfa.Lists.html#8294" class="Function">reverse</a> <a id="9802" class="Symbol">(</a><a id="9803" href="PUC-Assignment2.html#9772" class="Bound">xs</a> <a id="9806" href="plfa.Lists.html#3455" class="Function Operator">++</a> <a id="9809" href="PUC-Assignment2.html#9775" class="Bound">ys</a><a id="9811" class="Symbol">)</a> <a id="9813" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9815" href="plfa.Lists.html#8294" class="Function">reverse</a> <a id="9823" href="PUC-Assignment2.html#9775" class="Bound">ys</a> <a id="9826" href="plfa.Lists.html#3455" class="Function Operator">++</a> <a id="9829" href="plfa.Lists.html#8294" class="Function">reverse</a> <a id="9837" href="PUC-Assignment2.html#9772" class="Bound">xs</a>
</pre>{% endraw %}
#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution.
{% raw %}<pre class="Agda"><a id="10022" class="Keyword">postulate</a>
  <a id="reverse-involutive"></a><a id="10034" href="PUC-Assignment2.html#10034" class="Postulate">reverse-involutive</a> <a id="10053" class="Symbol">:</a> <a id="10055" class="Symbol">∀</a> <a id="10057" class="Symbol">{</a><a id="10058" href="PUC-Assignment2.html#10058" class="Bound">A</a> <a id="10060" class="Symbol">:</a> <a id="10062" class="PrimitiveType">Set</a><a id="10065" class="Symbol">}</a> <a id="10067" class="Symbol">{</a><a id="10068" href="PUC-Assignment2.html#10068" class="Bound">xs</a> <a id="10071" class="Symbol">:</a> <a id="10073" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="10078" href="PUC-Assignment2.html#10058" class="Bound">A</a><a id="10079" class="Symbol">}</a>
    <a id="10085" class="Symbol">→</a> <a id="10087" href="plfa.Lists.html#8294" class="Function">reverse</a> <a id="10095" class="Symbol">(</a><a id="10096" href="plfa.Lists.html#8294" class="Function">reverse</a> <a id="10104" href="PUC-Assignment2.html#10068" class="Bound">xs</a><a id="10106" class="Symbol">)</a> <a id="10108" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10110" href="PUC-Assignment2.html#10068" class="Bound">xs</a>
</pre>{% endraw %}
#### Exercise `map-compose`

Prove that the map of a composition is equal to the composition of two maps.
{% raw %}<pre class="Agda"><a id="10228" class="Keyword">postulate</a>
  <a id="map-compose"></a><a id="10240" href="PUC-Assignment2.html#10240" class="Postulate">map-compose</a> <a id="10252" class="Symbol">:</a> <a id="10254" class="Symbol">∀</a> <a id="10256" class="Symbol">{</a><a id="10257" href="PUC-Assignment2.html#10257" class="Bound">A</a> <a id="10259" href="PUC-Assignment2.html#10259" class="Bound">B</a> <a id="10261" href="PUC-Assignment2.html#10261" class="Bound">C</a> <a id="10263" class="Symbol">:</a> <a id="10265" class="PrimitiveType">Set</a><a id="10268" class="Symbol">}</a> <a id="10270" class="Symbol">{</a><a id="10271" href="PUC-Assignment2.html#10271" class="Bound">f</a> <a id="10273" class="Symbol">:</a> <a id="10275" href="PUC-Assignment2.html#10257" class="Bound">A</a> <a id="10277" class="Symbol">→</a> <a id="10279" href="PUC-Assignment2.html#10259" class="Bound">B</a><a id="10280" class="Symbol">}</a> <a id="10282" class="Symbol">{</a><a id="10283" href="PUC-Assignment2.html#10283" class="Bound">g</a> <a id="10285" class="Symbol">:</a> <a id="10287" href="PUC-Assignment2.html#10259" class="Bound">B</a> <a id="10289" class="Symbol">→</a> <a id="10291" href="PUC-Assignment2.html#10261" class="Bound">C</a><a id="10292" class="Symbol">}</a>
    <a id="10298" class="Symbol">→</a> <a id="10300" href="plfa.Lists.html#12979" class="Function">map</a> <a id="10304" class="Symbol">(</a><a id="10305" href="PUC-Assignment2.html#10283" class="Bound">g</a> <a id="10307" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="10309" href="PUC-Assignment2.html#10271" class="Bound">f</a><a id="10310" class="Symbol">)</a> <a id="10312" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10314" href="plfa.Lists.html#12979" class="Function">map</a> <a id="10318" href="PUC-Assignment2.html#10283" class="Bound">g</a> <a id="10320" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="10322" href="plfa.Lists.html#12979" class="Function">map</a> <a id="10326" href="PUC-Assignment2.html#10271" class="Bound">f</a>
</pre>{% endraw %}The last step of the proof requires extensionality.

#### Exercise `map-++-commute`

Prove the following relationship between map and append.
{% raw %}<pre class="Agda"><a id="10478" class="Keyword">postulate</a>
  <a id="map-++-commute"></a><a id="10490" href="PUC-Assignment2.html#10490" class="Postulate">map-++-commute</a> <a id="10505" class="Symbol">:</a> <a id="10507" class="Symbol">∀</a> <a id="10509" class="Symbol">{</a><a id="10510" href="PUC-Assignment2.html#10510" class="Bound">A</a> <a id="10512" href="PUC-Assignment2.html#10512" class="Bound">B</a> <a id="10514" class="Symbol">:</a> <a id="10516" class="PrimitiveType">Set</a><a id="10519" class="Symbol">}</a> <a id="10521" class="Symbol">{</a><a id="10522" href="PUC-Assignment2.html#10522" class="Bound">f</a> <a id="10524" class="Symbol">:</a> <a id="10526" href="PUC-Assignment2.html#10510" class="Bound">A</a> <a id="10528" class="Symbol">→</a> <a id="10530" href="PUC-Assignment2.html#10512" class="Bound">B</a><a id="10531" class="Symbol">}</a> <a id="10533" class="Symbol">{</a><a id="10534" href="PUC-Assignment2.html#10534" class="Bound">xs</a> <a id="10537" href="PUC-Assignment2.html#10537" class="Bound">ys</a> <a id="10540" class="Symbol">:</a> <a id="10542" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="10547" href="PUC-Assignment2.html#10510" class="Bound">A</a><a id="10548" class="Symbol">}</a>
   <a id="10553" class="Symbol">→</a>  <a id="10556" href="plfa.Lists.html#12979" class="Function">map</a> <a id="10560" href="PUC-Assignment2.html#10522" class="Bound">f</a> <a id="10562" class="Symbol">(</a><a id="10563" href="PUC-Assignment2.html#10534" class="Bound">xs</a> <a id="10566" href="plfa.Lists.html#3455" class="Function Operator">++</a> <a id="10569" href="PUC-Assignment2.html#10537" class="Bound">ys</a><a id="10571" class="Symbol">)</a> <a id="10573" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="10575" href="plfa.Lists.html#12979" class="Function">map</a> <a id="10579" href="PUC-Assignment2.html#10522" class="Bound">f</a> <a id="10581" href="PUC-Assignment2.html#10534" class="Bound">xs</a> <a id="10584" href="plfa.Lists.html#3455" class="Function Operator">++</a> <a id="10587" href="plfa.Lists.html#12979" class="Function">map</a> <a id="10591" href="PUC-Assignment2.html#10522" class="Bound">f</a> <a id="10593" href="PUC-Assignment2.html#10537" class="Bound">ys</a>
</pre>{% endraw %}
#### Exercise `map-Tree`

Define a type of trees with leaves of type `A` and internal
nodes of type `B`.
{% raw %}<pre class="Agda"><a id="10710" class="Keyword">data</a> <a id="Tree"></a><a id="10715" href="PUC-Assignment2.html#10715" class="Datatype">Tree</a> <a id="10720" class="Symbol">(</a><a id="10721" href="PUC-Assignment2.html#10721" class="Bound">A</a> <a id="10723" href="PUC-Assignment2.html#10723" class="Bound">B</a> <a id="10725" class="Symbol">:</a> <a id="10727" class="PrimitiveType">Set</a><a id="10730" class="Symbol">)</a> <a id="10732" class="Symbol">:</a> <a id="10734" class="PrimitiveType">Set</a> <a id="10738" class="Keyword">where</a>
  <a id="Tree.leaf"></a><a id="10746" href="PUC-Assignment2.html#10746" class="InductiveConstructor">leaf</a> <a id="10751" class="Symbol">:</a> <a id="10753" href="PUC-Assignment2.html#10721" class="Bound">A</a> <a id="10755" class="Symbol">→</a> <a id="10757" href="PUC-Assignment2.html#10715" class="Datatype">Tree</a> <a id="10762" href="PUC-Assignment2.html#10721" class="Bound">A</a> <a id="10764" href="PUC-Assignment2.html#10723" class="Bound">B</a>
  <a id="Tree.node"></a><a id="10768" href="PUC-Assignment2.html#10768" class="InductiveConstructor">node</a> <a id="10773" class="Symbol">:</a> <a id="10775" href="PUC-Assignment2.html#10715" class="Datatype">Tree</a> <a id="10780" href="PUC-Assignment2.html#10721" class="Bound">A</a> <a id="10782" href="PUC-Assignment2.html#10723" class="Bound">B</a> <a id="10784" class="Symbol">→</a> <a id="10786" href="PUC-Assignment2.html#10723" class="Bound">B</a> <a id="10788" class="Symbol">→</a> <a id="10790" href="PUC-Assignment2.html#10715" class="Datatype">Tree</a> <a id="10795" href="PUC-Assignment2.html#10721" class="Bound">A</a> <a id="10797" href="PUC-Assignment2.html#10723" class="Bound">B</a> <a id="10799" class="Symbol">→</a> <a id="10801" href="PUC-Assignment2.html#10715" class="Datatype">Tree</a> <a id="10806" href="PUC-Assignment2.html#10721" class="Bound">A</a> <a id="10808" href="PUC-Assignment2.html#10723" class="Bound">B</a>
</pre>{% endraw %}Define a suitable map operator over trees.
{% raw %}<pre class="Agda"><a id="10861" class="Keyword">postulate</a>
  <a id="map-Tree"></a><a id="10873" href="PUC-Assignment2.html#10873" class="Postulate">map-Tree</a> <a id="10882" class="Symbol">:</a> <a id="10884" class="Symbol">∀</a> <a id="10886" class="Symbol">{</a><a id="10887" href="PUC-Assignment2.html#10887" class="Bound">A</a> <a id="10889" href="PUC-Assignment2.html#10889" class="Bound">B</a> <a id="10891" href="PUC-Assignment2.html#10891" class="Bound">C</a> <a id="10893" href="PUC-Assignment2.html#10893" class="Bound">D</a> <a id="10895" class="Symbol">:</a> <a id="10897" class="PrimitiveType">Set</a><a id="10900" class="Symbol">}</a>
    <a id="10906" class="Symbol">→</a> <a id="10908" class="Symbol">(</a><a id="10909" href="PUC-Assignment2.html#10887" class="Bound">A</a> <a id="10911" class="Symbol">→</a> <a id="10913" href="PUC-Assignment2.html#10891" class="Bound">C</a><a id="10914" class="Symbol">)</a> <a id="10916" class="Symbol">→</a> <a id="10918" class="Symbol">(</a><a id="10919" href="PUC-Assignment2.html#10889" class="Bound">B</a> <a id="10921" class="Symbol">→</a> <a id="10923" href="PUC-Assignment2.html#10893" class="Bound">D</a><a id="10924" class="Symbol">)</a> <a id="10926" class="Symbol">→</a> <a id="10928" href="PUC-Assignment2.html#10715" class="Datatype">Tree</a> <a id="10933" href="PUC-Assignment2.html#10887" class="Bound">A</a> <a id="10935" href="PUC-Assignment2.html#10889" class="Bound">B</a> <a id="10937" class="Symbol">→</a> <a id="10939" href="PUC-Assignment2.html#10715" class="Datatype">Tree</a> <a id="10944" href="PUC-Assignment2.html#10891" class="Bound">C</a> <a id="10946" href="PUC-Assignment2.html#10893" class="Bound">D</a>
</pre>{% endraw %}
#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example,

    product [ 1 , 2 , 3 , 4 ] ≡ 24

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows.
{% raw %}<pre class="Agda"><a id="11208" class="Keyword">postulate</a>
  <a id="foldr-++"></a><a id="11220" href="PUC-Assignment2.html#11220" class="Postulate">foldr-++</a> <a id="11229" class="Symbol">:</a> <a id="11231" class="Symbol">∀</a> <a id="11233" class="Symbol">{</a><a id="11234" href="PUC-Assignment2.html#11234" class="Bound">A</a> <a id="11236" href="PUC-Assignment2.html#11236" class="Bound">B</a> <a id="11238" class="Symbol">:</a> <a id="11240" class="PrimitiveType">Set</a><a id="11243" class="Symbol">}</a> <a id="11245" class="Symbol">(</a><a id="11246" href="PUC-Assignment2.html#11246" class="Bound Operator">_⊗_</a> <a id="11250" class="Symbol">:</a> <a id="11252" href="PUC-Assignment2.html#11234" class="Bound">A</a> <a id="11254" class="Symbol">→</a> <a id="11256" href="PUC-Assignment2.html#11236" class="Bound">B</a> <a id="11258" class="Symbol">→</a> <a id="11260" href="PUC-Assignment2.html#11236" class="Bound">B</a><a id="11261" class="Symbol">)</a> <a id="11263" class="Symbol">(</a><a id="11264" href="PUC-Assignment2.html#11264" class="Bound">e</a> <a id="11266" class="Symbol">:</a> <a id="11268" href="PUC-Assignment2.html#11236" class="Bound">B</a><a id="11269" class="Symbol">)</a> <a id="11271" class="Symbol">(</a><a id="11272" href="PUC-Assignment2.html#11272" class="Bound">xs</a> <a id="11275" href="PUC-Assignment2.html#11275" class="Bound">ys</a> <a id="11278" class="Symbol">:</a> <a id="11280" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="11285" href="PUC-Assignment2.html#11234" class="Bound">A</a><a id="11286" class="Symbol">)</a> <a id="11288" class="Symbol">→</a>
    <a id="11294" href="plfa.Lists.html#15448" class="Function">foldr</a> <a id="11300" href="PUC-Assignment2.html#11246" class="Bound Operator">_⊗_</a> <a id="11304" href="PUC-Assignment2.html#11264" class="Bound">e</a> <a id="11306" class="Symbol">(</a><a id="11307" href="PUC-Assignment2.html#11272" class="Bound">xs</a> <a id="11310" href="plfa.Lists.html#3455" class="Function Operator">++</a> <a id="11313" href="PUC-Assignment2.html#11275" class="Bound">ys</a><a id="11315" class="Symbol">)</a> <a id="11317" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11319" href="plfa.Lists.html#15448" class="Function">foldr</a> <a id="11325" href="PUC-Assignment2.html#11246" class="Bound Operator">_⊗_</a> <a id="11329" class="Symbol">(</a><a id="11330" href="plfa.Lists.html#15448" class="Function">foldr</a> <a id="11336" href="PUC-Assignment2.html#11246" class="Bound Operator">_⊗_</a> <a id="11340" href="PUC-Assignment2.html#11264" class="Bound">e</a> <a id="11342" href="PUC-Assignment2.html#11275" class="Bound">ys</a><a id="11344" class="Symbol">)</a> <a id="11346" href="PUC-Assignment2.html#11272" class="Bound">xs</a>
</pre>{% endraw %}

#### Exercise `map-is-foldr`

Show that map can be defined using fold.
{% raw %}<pre class="Agda"><a id="11430" class="Keyword">postulate</a>
  <a id="map-is-foldr"></a><a id="11442" href="PUC-Assignment2.html#11442" class="Postulate">map-is-foldr</a> <a id="11455" class="Symbol">:</a> <a id="11457" class="Symbol">∀</a> <a id="11459" class="Symbol">{</a><a id="11460" href="PUC-Assignment2.html#11460" class="Bound">A</a> <a id="11462" href="PUC-Assignment2.html#11462" class="Bound">B</a> <a id="11464" class="Symbol">:</a> <a id="11466" class="PrimitiveType">Set</a><a id="11469" class="Symbol">}</a> <a id="11471" class="Symbol">{</a><a id="11472" href="PUC-Assignment2.html#11472" class="Bound">f</a> <a id="11474" class="Symbol">:</a> <a id="11476" href="PUC-Assignment2.html#11460" class="Bound">A</a> <a id="11478" class="Symbol">→</a> <a id="11480" href="PUC-Assignment2.html#11462" class="Bound">B</a><a id="11481" class="Symbol">}</a> <a id="11483" class="Symbol">→</a>
    <a id="11489" href="plfa.Lists.html#12979" class="Function">map</a> <a id="11493" href="PUC-Assignment2.html#11472" class="Bound">f</a> <a id="11495" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11497" href="plfa.Lists.html#15448" class="Function">foldr</a> <a id="11503" class="Symbol">(λ</a> <a id="11506" href="PUC-Assignment2.html#11506" class="Bound">x</a> <a id="11508" href="PUC-Assignment2.html#11508" class="Bound">xs</a> <a id="11511" class="Symbol">→</a> <a id="11513" href="PUC-Assignment2.html#11472" class="Bound">f</a> <a id="11515" href="PUC-Assignment2.html#11506" class="Bound">x</a> <a id="11517" href="plfa.Lists.html#1099" class="InductiveConstructor Operator">∷</a> <a id="11519" href="PUC-Assignment2.html#11508" class="Bound">xs</a><a id="11521" class="Symbol">)</a> <a id="11523" href="plfa.Lists.html#1084" class="InductiveConstructor">[]</a>
</pre>{% endraw %}This requires extensionality.

#### Exercise `fold-Tree`

Define a suitable fold function for the type of trees given earlier.
{% raw %}<pre class="Agda"><a id="11661" class="Keyword">postulate</a>
  <a id="fold-Tree"></a><a id="11673" href="PUC-Assignment2.html#11673" class="Postulate">fold-Tree</a> <a id="11683" class="Symbol">:</a> <a id="11685" class="Symbol">∀</a> <a id="11687" class="Symbol">{</a><a id="11688" href="PUC-Assignment2.html#11688" class="Bound">A</a> <a id="11690" href="PUC-Assignment2.html#11690" class="Bound">B</a> <a id="11692" href="PUC-Assignment2.html#11692" class="Bound">C</a> <a id="11694" class="Symbol">:</a> <a id="11696" class="PrimitiveType">Set</a><a id="11699" class="Symbol">}</a>
    <a id="11705" class="Symbol">→</a> <a id="11707" class="Symbol">(</a><a id="11708" href="PUC-Assignment2.html#11688" class="Bound">A</a> <a id="11710" class="Symbol">→</a> <a id="11712" href="PUC-Assignment2.html#11692" class="Bound">C</a><a id="11713" class="Symbol">)</a> <a id="11715" class="Symbol">→</a> <a id="11717" class="Symbol">(</a><a id="11718" href="PUC-Assignment2.html#11692" class="Bound">C</a> <a id="11720" class="Symbol">→</a> <a id="11722" href="PUC-Assignment2.html#11690" class="Bound">B</a> <a id="11724" class="Symbol">→</a> <a id="11726" href="PUC-Assignment2.html#11692" class="Bound">C</a> <a id="11728" class="Symbol">→</a> <a id="11730" href="PUC-Assignment2.html#11692" class="Bound">C</a><a id="11731" class="Symbol">)</a> <a id="11733" class="Symbol">→</a> <a id="11735" href="PUC-Assignment2.html#10715" class="Datatype">Tree</a> <a id="11740" href="PUC-Assignment2.html#11688" class="Bound">A</a> <a id="11742" href="PUC-Assignment2.html#11690" class="Bound">B</a> <a id="11744" class="Symbol">→</a> <a id="11746" href="PUC-Assignment2.html#11692" class="Bound">C</a>
</pre>{% endraw %}
#### Exercise `map-is-fold-Tree`

Demonstrate an analogue of `map-is-foldr` for the type of trees.

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows.
{% raw %}<pre class="Agda"><a id="downFrom"></a><a id="11944" href="PUC-Assignment2.html#11944" class="Function">downFrom</a> <a id="11953" class="Symbol">:</a> <a id="11955" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="11957" class="Symbol">→</a> <a id="11959" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="11964" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="11966" href="PUC-Assignment2.html#11944" class="Function">downFrom</a> <a id="11975" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="11984" class="Symbol">=</a>  <a id="11987" href="plfa.Lists.html#1084" class="InductiveConstructor">[]</a>
<a id="11990" href="PUC-Assignment2.html#11944" class="Function">downFrom</a> <a id="11999" class="Symbol">(</a><a id="12000" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="12004" href="PUC-Assignment2.html#12004" class="Bound">n</a><a id="12005" class="Symbol">)</a>  <a id="12008" class="Symbol">=</a>  <a id="12011" href="PUC-Assignment2.html#12004" class="Bound">n</a> <a id="12013" href="plfa.Lists.html#1099" class="InductiveConstructor Operator">∷</a> <a id="12015" href="PUC-Assignment2.html#11944" class="Function">downFrom</a> <a id="12024" href="PUC-Assignment2.html#12004" class="Bound">n</a>
</pre>{% endraw %}For example,
{% raw %}<pre class="Agda"><a id="12047" href="PUC-Assignment2.html#12047" class="Function">_</a> <a id="12049" class="Symbol">:</a> <a id="12051" href="PUC-Assignment2.html#11944" class="Function">downFrom</a> <a id="12060" class="Number">3</a> <a id="12062" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="12064" href="plfa.Lists.html#2869" class="InductiveConstructor Operator">[</a> <a id="12066" class="Number">2</a> <a id="12068" href="plfa.Lists.html#2869" class="InductiveConstructor Operator">,</a> <a id="12070" class="Number">1</a> <a id="12072" href="plfa.Lists.html#2869" class="InductiveConstructor Operator">,</a> <a id="12074" class="Number">0</a> <a id="12076" href="plfa.Lists.html#2869" class="InductiveConstructor Operator">]</a>
<a id="12078" class="Symbol">_</a> <a id="12080" class="Symbol">=</a> <a id="12082" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`.
{% raw %}<pre class="Agda"><a id="12178" class="Keyword">postulate</a>
  <a id="sum-downFrom"></a><a id="12190" href="PUC-Assignment2.html#12190" class="Postulate">sum-downFrom</a> <a id="12203" class="Symbol">:</a> <a id="12205" class="Symbol">∀</a> <a id="12207" class="Symbol">(</a><a id="12208" href="PUC-Assignment2.html#12208" class="Bound">n</a> <a id="12210" class="Symbol">:</a> <a id="12212" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12213" class="Symbol">)</a>
    <a id="12219" class="Symbol">→</a> <a id="12221" href="plfa.Lists.html#16343" class="Function">sum</a> <a id="12225" class="Symbol">(</a><a id="12226" href="PUC-Assignment2.html#11944" class="Function">downFrom</a> <a id="12235" href="PUC-Assignment2.html#12208" class="Bound">n</a><a id="12236" class="Symbol">)</a> <a id="12238" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="12240" class="Number">2</a> <a id="12242" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="12244" href="PUC-Assignment2.html#12208" class="Bound">n</a> <a id="12246" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="12248" class="Symbol">(</a><a id="12249" href="PUC-Assignment2.html#12208" class="Bound">n</a> <a id="12251" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">∸</a> <a id="12253" class="Number">1</a><a id="12254" class="Symbol">)</a>
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

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.


#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.


#### Exercise `¬Any≃All¬` (stretch)

First generalise composition to arbitrary levels, using
[universe polymorphism][plfa.Equality#unipoly].
{% raw %}<pre class="Agda"><a id="_∘′_"></a><a id="13158" href="PUC-Assignment2.html#13158" class="Function Operator">_∘′_</a> <a id="13163" class="Symbol">:</a> <a id="13165" class="Symbol">∀</a> <a id="13167" class="Symbol">{</a><a id="13168" href="PUC-Assignment2.html#13168" class="Bound">ℓ₁</a> <a id="13171" href="PUC-Assignment2.html#13171" class="Bound">ℓ₂</a> <a id="13174" href="PUC-Assignment2.html#13174" class="Bound">ℓ₃</a> <a id="13177" class="Symbol">:</a> <a id="13179" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="13184" class="Symbol">}</a> <a id="13186" class="Symbol">{</a><a id="13187" href="PUC-Assignment2.html#13187" class="Bound">A</a> <a id="13189" class="Symbol">:</a> <a id="13191" class="PrimitiveType">Set</a> <a id="13195" href="PUC-Assignment2.html#13168" class="Bound">ℓ₁</a><a id="13197" class="Symbol">}</a> <a id="13199" class="Symbol">{</a><a id="13200" href="PUC-Assignment2.html#13200" class="Bound">B</a> <a id="13202" class="Symbol">:</a> <a id="13204" class="PrimitiveType">Set</a> <a id="13208" href="PUC-Assignment2.html#13171" class="Bound">ℓ₂</a><a id="13210" class="Symbol">}</a> <a id="13212" class="Symbol">{</a><a id="13213" href="PUC-Assignment2.html#13213" class="Bound">C</a> <a id="13215" class="Symbol">:</a> <a id="13217" class="PrimitiveType">Set</a> <a id="13221" href="PUC-Assignment2.html#13174" class="Bound">ℓ₃</a><a id="13223" class="Symbol">}</a>
  <a id="13227" class="Symbol">→</a> <a id="13229" class="Symbol">(</a><a id="13230" href="PUC-Assignment2.html#13200" class="Bound">B</a> <a id="13232" class="Symbol">→</a> <a id="13234" href="PUC-Assignment2.html#13213" class="Bound">C</a><a id="13235" class="Symbol">)</a> <a id="13237" class="Symbol">→</a> <a id="13239" class="Symbol">(</a><a id="13240" href="PUC-Assignment2.html#13187" class="Bound">A</a> <a id="13242" class="Symbol">→</a> <a id="13244" href="PUC-Assignment2.html#13200" class="Bound">B</a><a id="13245" class="Symbol">)</a> <a id="13247" class="Symbol">→</a> <a id="13249" href="PUC-Assignment2.html#13187" class="Bound">A</a> <a id="13251" class="Symbol">→</a> <a id="13253" href="PUC-Assignment2.html#13213" class="Bound">C</a>
<a id="13255" class="Symbol">(</a><a id="13256" href="PUC-Assignment2.html#13256" class="Bound">g</a> <a id="13258" href="PUC-Assignment2.html#13158" class="Function Operator">∘′</a> <a id="13261" href="PUC-Assignment2.html#13261" class="Bound">f</a><a id="13262" class="Symbol">)</a> <a id="13264" href="PUC-Assignment2.html#13264" class="Bound">x</a>  <a id="13267" class="Symbol">=</a>  <a id="13270" href="PUC-Assignment2.html#13256" class="Bound">g</a> <a id="13272" class="Symbol">(</a><a id="13273" href="PUC-Assignment2.html#13261" class="Bound">f</a> <a id="13275" href="PUC-Assignment2.html#13264" class="Bound">x</a><a id="13276" class="Symbol">)</a>
</pre>{% endraw %}
Show that `Any` and `All` satisfy a version of De Morgan's Law.
{% raw %}<pre class="Agda"><a id="13351" class="Keyword">postulate</a>
  <a id="¬Any≃All¬"></a><a id="13363" href="PUC-Assignment2.html#13363" class="Postulate">¬Any≃All¬</a> <a id="13373" class="Symbol">:</a> <a id="13375" class="Symbol">∀</a> <a id="13377" class="Symbol">{</a><a id="13378" href="PUC-Assignment2.html#13378" class="Bound">A</a> <a id="13380" class="Symbol">:</a> <a id="13382" class="PrimitiveType">Set</a><a id="13385" class="Symbol">}</a> <a id="13387" class="Symbol">(</a><a id="13388" href="PUC-Assignment2.html#13388" class="Bound">P</a> <a id="13390" class="Symbol">:</a> <a id="13392" href="PUC-Assignment2.html#13378" class="Bound">A</a> <a id="13394" class="Symbol">→</a> <a id="13396" class="PrimitiveType">Set</a><a id="13399" class="Symbol">)</a> <a id="13401" class="Symbol">(</a><a id="13402" href="PUC-Assignment2.html#13402" class="Bound">xs</a> <a id="13405" class="Symbol">:</a> <a id="13407" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="13412" href="PUC-Assignment2.html#13378" class="Bound">A</a><a id="13413" class="Symbol">)</a>
    <a id="13419" class="Symbol">→</a> <a id="13421" class="Symbol">(</a><a id="13422" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="13425" href="PUC-Assignment2.html#13158" class="Function Operator">∘′</a> <a id="13428" href="plfa.Lists.html#22498" class="Datatype">Any</a> <a id="13432" href="PUC-Assignment2.html#13388" class="Bound">P</a><a id="13433" class="Symbol">)</a> <a id="13435" href="PUC-Assignment2.html#13402" class="Bound">xs</a> <a id="13438" href="plfa.Isomorphism.html#3955" class="Record Operator">≃</a> <a id="13440" href="plfa.Lists.html#21045" class="Datatype">All</a> <a id="13444" class="Symbol">(</a><a id="13445" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="13448" href="PUC-Assignment2.html#13158" class="Function Operator">∘′</a> <a id="13451" href="PUC-Assignment2.html#13388" class="Bound">P</a><a id="13452" class="Symbol">)</a> <a id="13454" href="PUC-Assignment2.html#13402" class="Bound">xs</a>
</pre>{% endraw %}
Do we also have the following?
{% raw %}<pre class="Agda"><a id="13497" class="Keyword">postulate</a>
  <a id="¬All≃Any¬"></a><a id="13509" href="PUC-Assignment2.html#13509" class="Postulate">¬All≃Any¬</a> <a id="13519" class="Symbol">:</a> <a id="13521" class="Symbol">∀</a> <a id="13523" class="Symbol">{</a><a id="13524" href="PUC-Assignment2.html#13524" class="Bound">A</a> <a id="13526" class="Symbol">:</a> <a id="13528" class="PrimitiveType">Set</a><a id="13531" class="Symbol">}</a> <a id="13533" class="Symbol">(</a><a id="13534" href="PUC-Assignment2.html#13534" class="Bound">P</a> <a id="13536" class="Symbol">:</a> <a id="13538" href="PUC-Assignment2.html#13524" class="Bound">A</a> <a id="13540" class="Symbol">→</a> <a id="13542" class="PrimitiveType">Set</a><a id="13545" class="Symbol">)</a> <a id="13547" class="Symbol">(</a><a id="13548" href="PUC-Assignment2.html#13548" class="Bound">xs</a> <a id="13551" class="Symbol">:</a> <a id="13553" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="13558" href="PUC-Assignment2.html#13524" class="Bound">A</a><a id="13559" class="Symbol">)</a>
    <a id="13565" class="Symbol">→</a> <a id="13567" class="Symbol">(</a><a id="13568" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="13571" href="PUC-Assignment2.html#13158" class="Function Operator">∘′</a> <a id="13574" href="plfa.Lists.html#21045" class="Datatype">All</a> <a id="13578" href="PUC-Assignment2.html#13534" class="Bound">P</a><a id="13579" class="Symbol">)</a> <a id="13581" href="PUC-Assignment2.html#13548" class="Bound">xs</a> <a id="13584" href="plfa.Isomorphism.html#3955" class="Record Operator">≃</a> <a id="13586" href="plfa.Lists.html#22498" class="Datatype">Any</a> <a id="13590" class="Symbol">(</a><a id="13591" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a> <a id="13594" href="PUC-Assignment2.html#13158" class="Function Operator">∘′</a> <a id="13597" href="PUC-Assignment2.html#13534" class="Bound">P</a><a id="13598" class="Symbol">)</a> <a id="13600" href="PUC-Assignment2.html#13548" class="Bound">xs</a>
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
{% raw %}<pre class="Agda"><a id="14155" class="Keyword">postulate</a>
  <a id="filter?"></a><a id="14167" href="PUC-Assignment2.html#14167" class="Postulate">filter?</a> <a id="14175" class="Symbol">:</a> <a id="14177" class="Symbol">∀</a> <a id="14179" class="Symbol">{</a><a id="14180" href="PUC-Assignment2.html#14180" class="Bound">A</a> <a id="14182" class="Symbol">:</a> <a id="14184" class="PrimitiveType">Set</a><a id="14187" class="Symbol">}</a> <a id="14189" class="Symbol">{</a><a id="14190" href="PUC-Assignment2.html#14190" class="Bound">P</a> <a id="14192" class="Symbol">:</a> <a id="14194" href="PUC-Assignment2.html#14180" class="Bound">A</a> <a id="14196" class="Symbol">→</a> <a id="14198" class="PrimitiveType">Set</a><a id="14201" class="Symbol">}</a>
    <a id="14207" class="Symbol">→</a> <a id="14209" class="Symbol">(</a><a id="14210" href="PUC-Assignment2.html#14210" class="Bound">P?</a> <a id="14213" class="Symbol">:</a> <a id="14215" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Unary.html#3474" class="Function">Decidable</a> <a id="14225" href="PUC-Assignment2.html#14190" class="Bound">P</a><a id="14226" class="Symbol">)</a> <a id="14228" class="Symbol">→</a> <a id="14230" href="plfa.Lists.html#1055" class="Datatype">List</a> <a id="14235" href="PUC-Assignment2.html#14180" class="Bound">A</a> <a id="14237" class="Symbol">→</a> <a id="14239" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="14242" href="PUC-Assignment2.html#14242" class="Bound">ys</a> <a id="14245" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a><a id="14246" class="Symbol">(</a> <a id="14248" href="plfa.Lists.html#21045" class="Datatype">All</a> <a id="14252" href="PUC-Assignment2.html#14190" class="Bound">P</a> <a id="14254" href="PUC-Assignment2.html#14242" class="Bound">ys</a> <a id="14257" class="Symbol">)</a>
</pre>{% endraw %}