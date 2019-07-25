---
src: tspl/Assignment2.lagda.md
title     : "Assignment2: TSPL Assignment 2"
layout    : page
permalink : /Assignment2/
---

{% raw %}<pre class="Agda"><a id="102" class="Keyword">module</a> <a id="109" href="Assignment2.html" class="Module">Assignment2</a> <a id="121" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

<!-- This assignment is due **4pm Thursday 18 October** (Week 5). -->

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
<a id="818" class="Keyword">open</a> <a id="823" class="Keyword">import</a> <a id="830" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="839" class="Keyword">using</a> <a id="845" class="Symbol">(</a><a id="846" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="847" class="Symbol">;</a> <a id="849" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="853" class="Symbol">;</a> <a id="855" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="858" class="Symbol">;</a> <a id="860" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="863" class="Symbol">;</a> <a id="865" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="868" class="Symbol">;</a> <a id="870" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="873" class="Symbol">;</a> <a id="875" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="878" class="Symbol">;</a> <a id="880" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="883" class="Symbol">;</a> <a id="885" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="888" class="Symbol">)</a>
<a id="890" class="Keyword">open</a> <a id="895" class="Keyword">import</a> <a id="902" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="922" class="Keyword">using</a> <a id="928" class="Symbol">(</a><a id="929" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="936" class="Symbol">;</a> <a id="938" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="949" class="Symbol">;</a> <a id="951" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="956" class="Symbol">;</a> <a id="958" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="964" class="Symbol">;</a>
  <a id="968" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="974" class="Symbol">;</a> <a id="976" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="983" class="Symbol">;</a> <a id="985" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="994" class="Symbol">;</a> <a id="996" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="1003" class="Symbol">;</a> <a id="1005" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="1014" class="Symbol">;</a> <a id="1016" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="1025" class="Symbol">;</a> <a id="1027" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="1035" class="Symbol">)</a>
<a id="1037" class="Keyword">open</a> <a id="1042" class="Keyword">import</a> <a id="1049" href="plfa.Relations.html" class="Module">plfa.Relations</a> <a id="1064" class="Keyword">using</a> <a id="1070" class="Symbol">(</a><a id="1071" href="plfa.Relations.html#18100" class="Datatype Operator">_&lt;_</a><a id="1074" class="Symbol">;</a> <a id="1076" href="plfa.Relations.html#18127" class="InductiveConstructor">z&lt;s</a><a id="1079" class="Symbol">;</a> <a id="1081" href="plfa.Relations.html#18184" class="InductiveConstructor">s&lt;s</a><a id="1084" class="Symbol">)</a>
<a id="1086" class="Keyword">open</a> <a id="1091" class="Keyword">import</a> <a id="1098" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1111" class="Keyword">using</a> <a id="1117" class="Symbol">(</a><a id="1118" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="1121" class="Symbol">;</a> <a id="1123" href="Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="1128" class="Symbol">;</a> <a id="1130" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="1135" class="Symbol">)</a> <a id="1137" class="Keyword">renaming</a> <a id="1146" class="Symbol">(</a><a id="1147" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1151" class="Symbol">to</a> <a id="1154" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1159" class="Symbol">)</a>
<a id="1161" class="Keyword">open</a> <a id="1166" class="Keyword">import</a> <a id="1173" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="1183" class="Keyword">using</a> <a id="1189" class="Symbol">(</a><a id="1190" href="Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="1191" class="Symbol">;</a> <a id="1193" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="1195" class="Symbol">)</a>
<a id="1197" class="Keyword">open</a> <a id="1202" class="Keyword">import</a> <a id="1209" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="1218" class="Keyword">using</a> <a id="1224" class="Symbol">(</a><a id="1225" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="1228" class="Symbol">;</a> <a id="1230" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="1234" class="Symbol">;</a> <a id="1236" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="1240" class="Symbol">)</a> <a id="1242" class="Keyword">renaming</a> <a id="1251" class="Symbol">(</a><a id="1252" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="1258" class="Symbol">to</a> <a id="1261" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="1267" class="Symbol">)</a>
<a id="1269" class="Keyword">open</a> <a id="1274" class="Keyword">import</a> <a id="1281" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1292" class="Keyword">using</a> <a id="1298" class="Symbol">(</a><a id="1299" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1300" class="Symbol">;</a> <a id="1302" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1308" class="Symbol">)</a>
<a id="1310" class="Keyword">open</a> <a id="1315" class="Keyword">import</a> <a id="1322" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="1337" class="Keyword">using</a> <a id="1343" class="Symbol">(</a><a id="1344" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="1348" class="Symbol">;</a> <a id="1350" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="1354" class="Symbol">;</a> <a id="1356" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="1361" class="Symbol">;</a> <a id="1363" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="1364" class="Symbol">;</a> <a id="1366" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="1369" class="Symbol">;</a> <a id="1371" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="1374" class="Symbol">;</a> <a id="1376" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="1379" class="Symbol">)</a>
<a id="1381" class="Keyword">open</a> <a id="1386" class="Keyword">import</a> <a id="1393" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1410" class="Keyword">using</a> <a id="1416" class="Symbol">(</a><a id="1417" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1419" class="Symbol">;</a> <a id="1421" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="1424" class="Symbol">;</a> <a id="1426" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="1429" class="Symbol">;</a> <a id="1431" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="1433" class="Symbol">)</a>
<a id="1435" class="Keyword">open</a> <a id="1440" class="Keyword">import</a> <a id="1447" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.html" class="Module">Relation.Nullary.Decidable</a> <a id="1474" class="Keyword">using</a> <a id="1480" class="Symbol">(</a><a id="1481" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊_⌋</a><a id="1484" class="Symbol">;</a> <a id="1486" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#926" class="Function">toWitness</a><a id="1495" class="Symbol">;</a> <a id="1497" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#1062" class="Function">fromWitness</a><a id="1508" class="Symbol">)</a>
<a id="1510" class="Keyword">open</a> <a id="1515" class="Keyword">import</a> <a id="1522" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1548" class="Keyword">using</a> <a id="1554" class="Symbol">(</a><a id="1555" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a><a id="1557" class="Symbol">)</a>
<a id="1559" class="Keyword">open</a> <a id="1564" class="Keyword">import</a> <a id="1571" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html" class="Module">Relation.Nullary.Product</a> <a id="1596" class="Keyword">using</a> <a id="1602" class="Symbol">(</a><a id="1603" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">_×-dec_</a><a id="1610" class="Symbol">)</a>
<a id="1612" class="Keyword">open</a> <a id="1617" class="Keyword">import</a> <a id="1624" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html" class="Module">Relation.Nullary.Sum</a> <a id="1645" class="Keyword">using</a> <a id="1651" class="Symbol">(</a><a id="1652" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">_⊎-dec_</a><a id="1659" class="Symbol">)</a>
<a id="1661" class="Keyword">open</a> <a id="1666" class="Keyword">import</a> <a id="1673" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1699" class="Keyword">using</a> <a id="1705" class="Symbol">(</a><a id="1706" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#880" class="Function">contraposition</a><a id="1720" class="Symbol">)</a>
<a id="1722" class="Keyword">open</a> <a id="1727" class="Keyword">import</a> <a id="1734" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="1747" class="Keyword">using</a> <a id="1753" class="Symbol">(</a><a id="1754" href="Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="1755" class="Symbol">;</a> <a id="1757" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="1760" class="Symbol">;</a> <a id="1762" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="1763" class="Symbol">;</a> <a id="1765" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="1773" class="Symbol">;</a> <a id="1775" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="1783" class="Symbol">)</a>
<a id="1785" class="Keyword">open</a> <a id="1790" class="Keyword">import</a> <a id="1797" href="plfa.Relations.html" class="Module">plfa.Relations</a> <a id="1812" class="Keyword">using</a> <a id="1818" class="Symbol">(</a><a id="1819" href="plfa.Relations.html#18100" class="Datatype Operator">_&lt;_</a><a id="1822" class="Symbol">;</a> <a id="1824" href="plfa.Relations.html#18127" class="InductiveConstructor">z&lt;s</a><a id="1827" class="Symbol">;</a> <a id="1829" href="plfa.Relations.html#18184" class="InductiveConstructor">s&lt;s</a><a id="1832" class="Symbol">)</a>
<a id="1834" class="Keyword">open</a> <a id="1839" class="Keyword">import</a> <a id="1846" href="plfa.Isomorphism.html" class="Module">plfa.Isomorphism</a> <a id="1863" class="Keyword">using</a> <a id="1869" class="Symbol">(</a><a id="1870" href="plfa.Isomorphism.html#3955" class="Record Operator">_≃_</a><a id="1873" class="Symbol">;</a> <a id="1875" href="plfa.Isomorphism.html#6602" class="Function">≃-sym</a><a id="1880" class="Symbol">;</a> <a id="1882" href="plfa.Isomorphism.html#6927" class="Function">≃-trans</a><a id="1889" class="Symbol">;</a> <a id="1891" href="plfa.Isomorphism.html#8776" class="Record Operator">_≲_</a><a id="1894" class="Symbol">;</a> <a id="1896" href="plfa.Isomorphism.html#2663" class="Postulate">extensionality</a><a id="1910" class="Symbol">)</a>
<a id="1912" class="Keyword">open</a> <a id="1917" href="plfa.Isomorphism.html#8011" class="Module">plfa.Isomorphism.≃-Reasoning</a>
</pre>{% endraw %}
## Equality

#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations][plfa.Relations]
can be written in a more readable form by using an anologue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.



## Isomorphism

#### Exercise `≃-implies-≲`

Show that every isomorphism implies an embedding.
{% raw %}<pre class="Agda"><a id="2443" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="2455" href="Assignment2.html#2455" class="Postulate">≃-implies-≲</a> <a id="2467" class="Symbol">:</a> <a id="2469" class="Symbol">∀</a> <a id="2471" class="Symbol">{</a><a id="2472" href="Assignment2.html#2472" class="Bound">A</a> <a id="2474" href="Assignment2.html#2474" class="Bound">B</a> <a id="2476" class="Symbol">:</a> <a id="2478" class="PrimitiveType">Set</a><a id="2481" class="Symbol">}</a>
    <a id="2487" class="Symbol">→</a> <a id="2489" href="Assignment2.html#2472" class="Bound">A</a> <a id="2491" href="plfa.Isomorphism.html#3955" class="Record Operator">≃</a> <a id="2493" href="Assignment2.html#2474" class="Bound">B</a>
      <a id="2501" class="Comment">-----</a>
    <a id="2511" class="Symbol">→</a> <a id="2513" href="Assignment2.html#2472" class="Bound">A</a> <a id="2515" href="plfa.Isomorphism.html#8776" class="Record Operator">≲</a> <a id="2517" href="Assignment2.html#2474" class="Bound">B</a>
</pre>{% endraw %}
#### Exercise `_⇔_` (recommended) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows.
{% raw %}<pre class="Agda"><a id="2650" class="Keyword">record</a> <a id="_⇔_"></a><a id="2657" href="Assignment2.html#2657" class="Record Operator">_⇔_</a> <a id="2661" class="Symbol">(</a><a id="2662" href="Assignment2.html#2662" class="Bound">A</a> <a id="2664" href="Assignment2.html#2664" class="Bound">B</a> <a id="2666" class="Symbol">:</a> <a id="2668" class="PrimitiveType">Set</a><a id="2671" class="Symbol">)</a> <a id="2673" class="Symbol">:</a> <a id="2675" class="PrimitiveType">Set</a> <a id="2679" class="Keyword">where</a>
  <a id="2687" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="2697" href="Assignment2.html#2697" class="Field">to</a>   <a id="2702" class="Symbol">:</a> <a id="2704" href="Assignment2.html#2662" class="Bound">A</a> <a id="2706" class="Symbol">→</a> <a id="2708" href="Assignment2.html#2664" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="2714" href="Assignment2.html#2714" class="Field">from</a> <a id="2719" class="Symbol">:</a> <a id="2721" href="Assignment2.html#2664" class="Bound">B</a> <a id="2723" class="Symbol">→</a> <a id="2725" href="Assignment2.html#2662" class="Bound">A</a>

<a id="2728" class="Keyword">open</a> <a id="2733" href="Assignment2.html#2657" class="Module Operator">_⇔_</a>
</pre>{% endraw %}Show that equivalence is reflexive, symmetric, and transitive.

#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin][plfa.Naturals#Bin] and
[Bin-laws][plfa.Induction#Bin-laws]
define a datatype of bitstrings representing natural numbers.
{% raw %}<pre class="Agda"><a id="3016" class="Keyword">data</a> <a id="Bin"></a><a id="3021" href="Assignment2.html#3021" class="Datatype">Bin</a> <a id="3025" class="Symbol">:</a> <a id="3027" class="PrimitiveType">Set</a> <a id="3031" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="3039" href="Assignment2.html#3039" class="InductiveConstructor">nil</a> <a id="3043" class="Symbol">:</a> <a id="3045" href="Assignment2.html#3021" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="3051" href="Assignment2.html#3051" class="InductiveConstructor Operator">x0_</a> <a id="3055" class="Symbol">:</a> <a id="3057" href="Assignment2.html#3021" class="Datatype">Bin</a> <a id="3061" class="Symbol">→</a> <a id="3063" href="Assignment2.html#3021" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="3069" href="Assignment2.html#3069" class="InductiveConstructor Operator">x1_</a> <a id="3073" class="Symbol">:</a> <a id="3075" href="Assignment2.html#3021" class="Datatype">Bin</a> <a id="3079" class="Symbol">→</a> <a id="3081" href="Assignment2.html#3021" class="Datatype">Bin</a>
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

Show sum is associative up to ismorphism.

#### Exercise `⊥-identityˡ` (recommended)

Show zero is the left identity of addition.

#### Exercise `⊥-identityʳ`

Show zero is the right identity of addition.

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds.
{% raw %}<pre class="Agda"><a id="3890" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="3902" href="Assignment2.html#3902" class="Postulate">⊎-weak-×</a> <a id="3911" class="Symbol">:</a> <a id="3913" class="Symbol">∀</a> <a id="3915" class="Symbol">{</a><a id="3916" href="Assignment2.html#3916" class="Bound">A</a> <a id="3918" href="Assignment2.html#3918" class="Bound">B</a> <a id="3920" href="Assignment2.html#3920" class="Bound">C</a> <a id="3922" class="Symbol">:</a> <a id="3924" class="PrimitiveType">Set</a><a id="3927" class="Symbol">}</a> <a id="3929" class="Symbol">→</a> <a id="3931" class="Symbol">(</a><a id="3932" href="Assignment2.html#3916" class="Bound">A</a> <a id="3934" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3936" href="Assignment2.html#3918" class="Bound">B</a><a id="3937" class="Symbol">)</a> <a id="3939" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3941" href="Assignment2.html#3920" class="Bound">C</a> <a id="3943" class="Symbol">→</a> <a id="3945" href="Assignment2.html#3916" class="Bound">A</a> <a id="3947" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="3949" class="Symbol">(</a><a id="3950" href="Assignment2.html#3918" class="Bound">B</a> <a id="3952" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="3954" href="Assignment2.html#3920" class="Bound">C</a><a id="3955" class="Symbol">)</a>
</pre>{% endraw %}This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

#### Exercise `⊎×-implies-×⊎`

Show that a disjunct of conjuncts implies a conjunct of disjuncts.
{% raw %}<pre class="Agda"><a id="4195" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="4207" href="Assignment2.html#4207" class="Postulate">⊎×-implies-×⊎</a> <a id="4221" class="Symbol">:</a> <a id="4223" class="Symbol">∀</a> <a id="4225" class="Symbol">{</a><a id="4226" href="Assignment2.html#4226" class="Bound">A</a> <a id="4228" href="Assignment2.html#4228" class="Bound">B</a> <a id="4230" href="Assignment2.html#4230" class="Bound">C</a> <a id="4232" href="Assignment2.html#4232" class="Bound">D</a> <a id="4234" class="Symbol">:</a> <a id="4236" class="PrimitiveType">Set</a><a id="4239" class="Symbol">}</a> <a id="4241" class="Symbol">→</a> <a id="4243" class="Symbol">(</a><a id="4244" href="Assignment2.html#4226" class="Bound">A</a> <a id="4246" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4248" href="Assignment2.html#4228" class="Bound">B</a><a id="4249" class="Symbol">)</a> <a id="4251" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4253" class="Symbol">(</a><a id="4254" href="Assignment2.html#4230" class="Bound">C</a> <a id="4256" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4258" href="Assignment2.html#4232" class="Bound">D</a><a id="4259" class="Symbol">)</a> <a id="4261" class="Symbol">→</a> <a id="4263" class="Symbol">(</a><a id="4264" href="Assignment2.html#4226" class="Bound">A</a> <a id="4266" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4268" href="Assignment2.html#4230" class="Bound">C</a><a id="4269" class="Symbol">)</a> <a id="4271" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4273" class="Symbol">(</a><a id="4274" href="Assignment2.html#4228" class="Bound">B</a> <a id="4276" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="4278" href="Assignment2.html#4232" class="Bound">D</a><a id="4279" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="Stable"></a><a id="5761" href="Assignment2.html#5761" class="Function">Stable</a> <a id="5768" class="Symbol">:</a> <a id="5770" class="PrimitiveType">Set</a> <a id="5774" class="Symbol">→</a> <a id="5776" class="PrimitiveType">Set</a>
<a id="5780" href="Assignment2.html#5761" class="Function">Stable</a> <a id="5787" href="Assignment2.html#5787" class="Bound">A</a> <a id="5789" class="Symbol">=</a> <a id="5791" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="5793" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="5795" href="Assignment2.html#5787" class="Bound">A</a> <a id="5797" class="Symbol">→</a> <a id="5799" href="Assignment2.html#5787" class="Bound">A</a>
</pre>{% endraw %}Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.


## Quantifiers

#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction.
{% raw %}<pre class="Agda"><a id="6020" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="6032" href="Assignment2.html#6032" class="Postulate">∀-distrib-×</a> <a id="6044" class="Symbol">:</a> <a id="6046" class="Symbol">∀</a> <a id="6048" class="Symbol">{</a><a id="6049" href="Assignment2.html#6049" class="Bound">A</a> <a id="6051" class="Symbol">:</a> <a id="6053" class="PrimitiveType">Set</a><a id="6056" class="Symbol">}</a> <a id="6058" class="Symbol">{</a><a id="6059" href="Assignment2.html#6059" class="Bound">B</a> <a id="6061" href="Assignment2.html#6061" class="Bound">C</a> <a id="6063" class="Symbol">:</a> <a id="6065" href="Assignment2.html#6049" class="Bound">A</a> <a id="6067" class="Symbol">→</a> <a id="6069" class="PrimitiveType">Set</a><a id="6072" class="Symbol">}</a> <a id="6074" class="Symbol">→</a>
    <a id="6080" class="Symbol">(∀</a> <a id="6083" class="Symbol">(</a><a id="6084" href="Assignment2.html#6084" class="Bound">x</a> <a id="6086" class="Symbol">:</a> <a id="6088" href="Assignment2.html#6049" class="Bound">A</a><a id="6089" class="Symbol">)</a> <a id="6091" class="Symbol">→</a> <a id="6093" href="Assignment2.html#6059" class="Bound">B</a> <a id="6095" href="Assignment2.html#6084" class="Bound">x</a> <a id="6097" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6099" href="Assignment2.html#6061" class="Bound">C</a> <a id="6101" href="Assignment2.html#6084" class="Bound">x</a><a id="6102" class="Symbol">)</a> <a id="6104" href="plfa.Isomorphism.html#3955" class="Record Operator">≃</a> <a id="6106" class="Symbol">(∀</a> <a id="6109" class="Symbol">(</a><a id="6110" href="Assignment2.html#6110" class="Bound">x</a> <a id="6112" class="Symbol">:</a> <a id="6114" href="Assignment2.html#6049" class="Bound">A</a><a id="6115" class="Symbol">)</a> <a id="6117" class="Symbol">→</a> <a id="6119" href="Assignment2.html#6059" class="Bound">B</a> <a id="6121" href="Assignment2.html#6110" class="Bound">x</a><a id="6122" class="Symbol">)</a> <a id="6124" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6126" class="Symbol">(∀</a> <a id="6129" class="Symbol">(</a><a id="6130" href="Assignment2.html#6130" class="Bound">x</a> <a id="6132" class="Symbol">:</a> <a id="6134" href="Assignment2.html#6049" class="Bound">A</a><a id="6135" class="Symbol">)</a> <a id="6137" class="Symbol">→</a> <a id="6139" href="Assignment2.html#6061" class="Bound">C</a> <a id="6141" href="Assignment2.html#6130" class="Bound">x</a><a id="6142" class="Symbol">)</a>
</pre>{% endraw %}Compare this with the result (`→-distrib-×`) in
Chapter [Connectives][plfa.Connectives].

#### Exercise `⊎∀-implies-∀⊎`

Show that a disjunction of universals implies a universal of disjunctions.
{% raw %}<pre class="Agda"><a id="6348" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="6360" href="Assignment2.html#6360" class="Postulate">⊎∀-implies-∀⊎</a> <a id="6374" class="Symbol">:</a> <a id="6376" class="Symbol">∀</a> <a id="6378" class="Symbol">{</a><a id="6379" href="Assignment2.html#6379" class="Bound">A</a> <a id="6381" class="Symbol">:</a> <a id="6383" class="PrimitiveType">Set</a><a id="6386" class="Symbol">}</a> <a id="6388" class="Symbol">{</a> <a id="6390" href="Assignment2.html#6390" class="Bound">B</a> <a id="6392" href="Assignment2.html#6392" class="Bound">C</a> <a id="6394" class="Symbol">:</a> <a id="6396" href="Assignment2.html#6379" class="Bound">A</a> <a id="6398" class="Symbol">→</a> <a id="6400" class="PrimitiveType">Set</a> <a id="6404" class="Symbol">}</a> <a id="6406" class="Symbol">→</a>
    <a id="6412" class="Symbol">(∀</a> <a id="6415" class="Symbol">(</a><a id="6416" href="Assignment2.html#6416" class="Bound">x</a> <a id="6418" class="Symbol">:</a> <a id="6420" href="Assignment2.html#6379" class="Bound">A</a><a id="6421" class="Symbol">)</a> <a id="6423" class="Symbol">→</a> <a id="6425" href="Assignment2.html#6390" class="Bound">B</a> <a id="6427" href="Assignment2.html#6416" class="Bound">x</a><a id="6428" class="Symbol">)</a> <a id="6430" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6432" class="Symbol">(∀</a> <a id="6435" class="Symbol">(</a><a id="6436" href="Assignment2.html#6436" class="Bound">x</a> <a id="6438" class="Symbol">:</a> <a id="6440" href="Assignment2.html#6379" class="Bound">A</a><a id="6441" class="Symbol">)</a> <a id="6443" class="Symbol">→</a> <a id="6445" href="Assignment2.html#6392" class="Bound">C</a> <a id="6447" href="Assignment2.html#6436" class="Bound">x</a><a id="6448" class="Symbol">)</a>  <a id="6451" class="Symbol">→</a>  <a id="6454" class="Symbol">∀</a> <a id="6456" class="Symbol">(</a><a id="6457" href="Assignment2.html#6457" class="Bound">x</a> <a id="6459" class="Symbol">:</a> <a id="6461" href="Assignment2.html#6379" class="Bound">A</a><a id="6462" class="Symbol">)</a> <a id="6464" class="Symbol">→</a> <a id="6466" href="Assignment2.html#6390" class="Bound">B</a> <a id="6468" href="Assignment2.html#6457" class="Bound">x</a> <a id="6470" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6472" href="Assignment2.html#6392" class="Bound">C</a> <a id="6474" href="Assignment2.html#6457" class="Bound">x</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction.
{% raw %}<pre class="Agda"><a id="6639" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="6651" href="Assignment2.html#6651" class="Postulate">∃-distrib-⊎</a> <a id="6663" class="Symbol">:</a> <a id="6665" class="Symbol">∀</a> <a id="6667" class="Symbol">{</a><a id="6668" href="Assignment2.html#6668" class="Bound">A</a> <a id="6670" class="Symbol">:</a> <a id="6672" class="PrimitiveType">Set</a><a id="6675" class="Symbol">}</a> <a id="6677" class="Symbol">{</a><a id="6678" href="Assignment2.html#6678" class="Bound">B</a> <a id="6680" href="Assignment2.html#6680" class="Bound">C</a> <a id="6682" class="Symbol">:</a> <a id="6684" href="Assignment2.html#6668" class="Bound">A</a> <a id="6686" class="Symbol">→</a> <a id="6688" class="PrimitiveType">Set</a><a id="6691" class="Symbol">}</a> <a id="6693" class="Symbol">→</a>
    <a id="6699" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6702" href="Assignment2.html#6702" class="Bound">x</a> <a id="6704" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6706" class="Symbol">(</a><a id="6707" href="Assignment2.html#6678" class="Bound">B</a> <a id="6709" href="Assignment2.html#6702" class="Bound">x</a> <a id="6711" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6713" href="Assignment2.html#6680" class="Bound">C</a> <a id="6715" href="Assignment2.html#6702" class="Bound">x</a><a id="6716" class="Symbol">)</a> <a id="6718" href="plfa.Isomorphism.html#3955" class="Record Operator">≃</a> <a id="6720" class="Symbol">(</a><a id="6721" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6724" href="Assignment2.html#6724" class="Bound">x</a> <a id="6726" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6728" href="Assignment2.html#6678" class="Bound">B</a> <a id="6730" href="Assignment2.html#6724" class="Bound">x</a><a id="6731" class="Symbol">)</a> <a id="6733" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="6735" class="Symbol">(</a><a id="6736" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6739" href="Assignment2.html#6739" class="Bound">x</a> <a id="6741" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6743" href="Assignment2.html#6680" class="Bound">C</a> <a id="6745" href="Assignment2.html#6739" class="Bound">x</a><a id="6746" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `∃×-implies-×∃`

Show that an existential of conjunctions implies a conjunction of existentials.
{% raw %}<pre class="Agda"><a id="6868" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="6880" href="Assignment2.html#6880" class="Postulate">∃×-implies-×∃</a> <a id="6894" class="Symbol">:</a> <a id="6896" class="Symbol">∀</a> <a id="6898" class="Symbol">{</a><a id="6899" href="Assignment2.html#6899" class="Bound">A</a> <a id="6901" class="Symbol">:</a> <a id="6903" class="PrimitiveType">Set</a><a id="6906" class="Symbol">}</a> <a id="6908" class="Symbol">{</a> <a id="6910" href="Assignment2.html#6910" class="Bound">B</a> <a id="6912" href="Assignment2.html#6912" class="Bound">C</a> <a id="6914" class="Symbol">:</a> <a id="6916" href="Assignment2.html#6899" class="Bound">A</a> <a id="6918" class="Symbol">→</a> <a id="6920" class="PrimitiveType">Set</a> <a id="6924" class="Symbol">}</a> <a id="6926" class="Symbol">→</a>
    <a id="6932" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6935" href="Assignment2.html#6935" class="Bound">x</a> <a id="6937" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6939" class="Symbol">(</a><a id="6940" href="Assignment2.html#6910" class="Bound">B</a> <a id="6942" href="Assignment2.html#6935" class="Bound">x</a> <a id="6944" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6946" href="Assignment2.html#6912" class="Bound">C</a> <a id="6948" href="Assignment2.html#6935" class="Bound">x</a><a id="6949" class="Symbol">)</a> <a id="6951" class="Symbol">→</a> <a id="6953" class="Symbol">(</a><a id="6954" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6957" href="Assignment2.html#6957" class="Bound">x</a> <a id="6959" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6961" href="Assignment2.html#6910" class="Bound">B</a> <a id="6963" href="Assignment2.html#6957" class="Bound">x</a><a id="6964" class="Symbol">)</a> <a id="6966" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="6968" class="Symbol">(</a><a id="6969" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="6972" href="Assignment2.html#6972" class="Bound">x</a> <a id="6974" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="6976" href="Assignment2.html#6912" class="Bound">C</a> <a id="6978" href="Assignment2.html#6972" class="Bound">x</a><a id="6979" class="Symbol">)</a>
</pre>{% endraw %}Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-even-odd`

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

#### Exercise `∃-+-≤`

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal.
{% raw %}<pre class="Agda"><a id="7474" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="7486" href="Assignment2.html#7486" class="Postulate">∃¬-implies-¬∀</a> <a id="7500" class="Symbol">:</a> <a id="7502" class="Symbol">∀</a> <a id="7504" class="Symbol">{</a><a id="7505" href="Assignment2.html#7505" class="Bound">A</a> <a id="7507" class="Symbol">:</a> <a id="7509" class="PrimitiveType">Set</a><a id="7512" class="Symbol">}</a> <a id="7514" class="Symbol">{</a><a id="7515" href="Assignment2.html#7515" class="Bound">B</a> <a id="7517" class="Symbol">:</a> <a id="7519" href="Assignment2.html#7505" class="Bound">A</a> <a id="7521" class="Symbol">→</a> <a id="7523" class="PrimitiveType">Set</a><a id="7526" class="Symbol">}</a>
    <a id="7532" class="Symbol">→</a> <a id="7534" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃[</a> <a id="7537" href="Assignment2.html#7537" class="Bound">x</a> <a id="7539" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">]</a> <a id="7541" class="Symbol">(</a><a id="7542" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7544" href="Assignment2.html#7515" class="Bound">B</a> <a id="7546" href="Assignment2.html#7537" class="Bound">x</a><a id="7547" class="Symbol">)</a>
      <a id="7555" class="Comment">--------------</a>
    <a id="7574" class="Symbol">→</a> <a id="7576" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="7578" class="Symbol">(∀</a> <a id="7581" href="Assignment2.html#7581" class="Bound">x</a> <a id="7583" class="Symbol">→</a> <a id="7585" href="Assignment2.html#7515" class="Bound">B</a> <a id="7587" href="Assignment2.html#7581" class="Bound">x</a><a id="7588" class="Symbol">)</a>
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
{% raw %}<pre class="Agda"><a id="8498" class="Keyword">postulate</a>
  <a id="_&lt;?_"></a><a id="8510" href="Assignment2.html#8510" class="Postulate Operator">_&lt;?_</a> <a id="8515" class="Symbol">:</a> <a id="8517" class="Symbol">∀</a> <a id="8519" class="Symbol">(</a><a id="8520" href="Assignment2.html#8520" class="Bound">m</a> <a id="8522" href="Assignment2.html#8522" class="Bound">n</a> <a id="8524" class="Symbol">:</a> <a id="8526" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8527" class="Symbol">)</a> <a id="8529" class="Symbol">→</a> <a id="8531" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8535" class="Symbol">(</a><a id="8536" href="Assignment2.html#8520" class="Bound">m</a> <a id="8538" href="plfa.Relations.html#18100" class="Datatype Operator">&lt;</a> <a id="8540" href="Assignment2.html#8522" class="Bound">n</a><a id="8541" class="Symbol">)</a>
</pre>{% endraw %}
#### Exercise `_≡ℕ?_`

Define a function to decide whether two naturals are equal.
{% raw %}<pre class="Agda"><a id="8635" class="Keyword">postulate</a>
  <a id="_≡ℕ?_"></a><a id="8647" href="Assignment2.html#8647" class="Postulate Operator">_≡ℕ?_</a> <a id="8653" class="Symbol">:</a> <a id="8655" class="Symbol">∀</a> <a id="8657" class="Symbol">(</a><a id="8658" href="Assignment2.html#8658" class="Bound">m</a> <a id="8660" href="Assignment2.html#8660" class="Bound">n</a> <a id="8662" class="Symbol">:</a> <a id="8664" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8665" class="Symbol">)</a> <a id="8667" class="Symbol">→</a> <a id="8669" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8673" class="Symbol">(</a><a id="8674" href="Assignment2.html#8658" class="Bound">m</a> <a id="8676" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8678" href="Assignment2.html#8660" class="Bound">n</a><a id="8679" class="Symbol">)</a>
</pre>{% endraw %}

#### Exercise `erasure`

Show that erasure relates corresponding boolean and decidable operations.
{% raw %}<pre class="Agda"><a id="8790" class="Keyword">postulate</a>
  <a id="∧-×"></a><a id="8802" href="Assignment2.html#8802" class="Postulate">∧-×</a> <a id="8806" class="Symbol">:</a> <a id="8808" class="Symbol">∀</a> <a id="8810" class="Symbol">{</a><a id="8811" href="Assignment2.html#8811" class="Bound">A</a> <a id="8813" href="Assignment2.html#8813" class="Bound">B</a> <a id="8815" class="Symbol">:</a> <a id="8817" class="PrimitiveType">Set</a><a id="8820" class="Symbol">}</a> <a id="8822" class="Symbol">(</a><a id="8823" href="Assignment2.html#8823" class="Bound">x</a> <a id="8825" class="Symbol">:</a> <a id="8827" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8831" href="Assignment2.html#8811" class="Bound">A</a><a id="8832" class="Symbol">)</a> <a id="8834" class="Symbol">(</a><a id="8835" href="Assignment2.html#8835" class="Bound">y</a> <a id="8837" class="Symbol">:</a> <a id="8839" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8843" href="Assignment2.html#8813" class="Bound">B</a><a id="8844" class="Symbol">)</a> <a id="8846" class="Symbol">→</a> <a id="8848" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8850" href="Assignment2.html#8823" class="Bound">x</a> <a id="8852" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8854" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">∧</a> <a id="8856" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8858" href="Assignment2.html#8835" class="Bound">y</a> <a id="8860" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8862" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8864" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8866" href="Assignment2.html#8823" class="Bound">x</a> <a id="8868" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">×-dec</a> <a id="8874" href="Assignment2.html#8835" class="Bound">y</a> <a id="8876" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="∨-×"></a><a id="8880" href="Assignment2.html#8880" class="Postulate">∨-×</a> <a id="8884" class="Symbol">:</a> <a id="8886" class="Symbol">∀</a> <a id="8888" class="Symbol">{</a><a id="8889" href="Assignment2.html#8889" class="Bound">A</a> <a id="8891" href="Assignment2.html#8891" class="Bound">B</a> <a id="8893" class="Symbol">:</a> <a id="8895" class="PrimitiveType">Set</a><a id="8898" class="Symbol">}</a> <a id="8900" class="Symbol">(</a><a id="8901" href="Assignment2.html#8901" class="Bound">x</a> <a id="8903" class="Symbol">:</a> <a id="8905" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8909" href="Assignment2.html#8889" class="Bound">A</a><a id="8910" class="Symbol">)</a> <a id="8912" class="Symbol">(</a><a id="8913" href="Assignment2.html#8913" class="Bound">y</a> <a id="8915" class="Symbol">:</a> <a id="8917" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8921" href="Assignment2.html#8891" class="Bound">B</a><a id="8922" class="Symbol">)</a> <a id="8924" class="Symbol">→</a> <a id="8926" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8928" href="Assignment2.html#8901" class="Bound">x</a> <a id="8930" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8932" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">∨</a> <a id="8934" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8936" href="Assignment2.html#8913" class="Bound">y</a> <a id="8938" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="8940" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8942" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8944" href="Assignment2.html#8901" class="Bound">x</a> <a id="8946" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">⊎-dec</a> <a id="8952" href="Assignment2.html#8913" class="Bound">y</a> <a id="8954" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
  <a id="not-¬"></a><a id="8958" href="Assignment2.html#8958" class="Postulate">not-¬</a> <a id="8964" class="Symbol">:</a> <a id="8966" class="Symbol">∀</a> <a id="8968" class="Symbol">{</a><a id="8969" href="Assignment2.html#8969" class="Bound">A</a> <a id="8971" class="Symbol">:</a> <a id="8973" class="PrimitiveType">Set</a><a id="8976" class="Symbol">}</a> <a id="8978" class="Symbol">(</a><a id="8979" href="Assignment2.html#8979" class="Bound">x</a> <a id="8981" class="Symbol">:</a> <a id="8983" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="8987" href="Assignment2.html#8969" class="Bound">A</a><a id="8988" class="Symbol">)</a> <a id="8990" class="Symbol">→</a> <a id="8992" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a> <a id="8996" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="8998" href="Assignment2.html#8979" class="Bound">x</a> <a id="9000" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9002" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9004" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9006" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a> <a id="9009" href="Assignment2.html#8979" class="Bound">x</a> <a id="9011" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}
#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from
Chapter [Isomorphism][plfa.Isomorphism#iff],
operation on booleans and decidables, and also show the corresponding erasure.
{% raw %}<pre class="Agda"><a id="9232" class="Keyword">postulate</a>
  <a id="_iff_"></a><a id="9244" href="Assignment2.html#9244" class="Postulate Operator">_iff_</a> <a id="9250" class="Symbol">:</a> <a id="9252" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="9257" class="Symbol">→</a> <a id="9259" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a> <a id="9264" class="Symbol">→</a> <a id="9266" href="Agda.Builtin.Bool.html#135" class="Datatype">Bool</a>
  <a id="_⇔-dec_"></a><a id="9273" href="Assignment2.html#9273" class="Postulate Operator">_⇔-dec_</a> <a id="9281" class="Symbol">:</a> <a id="9283" class="Symbol">∀</a> <a id="9285" class="Symbol">{</a><a id="9286" href="Assignment2.html#9286" class="Bound">A</a> <a id="9288" href="Assignment2.html#9288" class="Bound">B</a> <a id="9290" class="Symbol">:</a> <a id="9292" class="PrimitiveType">Set</a><a id="9295" class="Symbol">}</a> <a id="9297" class="Symbol">→</a> <a id="9299" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9303" href="Assignment2.html#9286" class="Bound">A</a> <a id="9305" class="Symbol">→</a> <a id="9307" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9311" href="Assignment2.html#9288" class="Bound">B</a> <a id="9313" class="Symbol">→</a> <a id="9315" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9319" class="Symbol">(</a><a id="9320" href="Assignment2.html#9286" class="Bound">A</a> <a id="9322" href="Assignment2.html#2657" class="Record Operator">⇔</a> <a id="9324" href="Assignment2.html#9288" class="Bound">B</a><a id="9325" class="Symbol">)</a>
  <a id="iff-⇔"></a><a id="9329" href="Assignment2.html#9329" class="Postulate">iff-⇔</a> <a id="9335" class="Symbol">:</a> <a id="9337" class="Symbol">∀</a> <a id="9339" class="Symbol">{</a><a id="9340" href="Assignment2.html#9340" class="Bound">A</a> <a id="9342" href="Assignment2.html#9342" class="Bound">B</a> <a id="9344" class="Symbol">:</a> <a id="9346" class="PrimitiveType">Set</a><a id="9349" class="Symbol">}</a> <a id="9351" class="Symbol">(</a><a id="9352" href="Assignment2.html#9352" class="Bound">x</a> <a id="9354" class="Symbol">:</a> <a id="9356" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9360" href="Assignment2.html#9340" class="Bound">A</a><a id="9361" class="Symbol">)</a> <a id="9363" class="Symbol">(</a><a id="9364" href="Assignment2.html#9364" class="Bound">y</a> <a id="9366" class="Symbol">:</a> <a id="9368" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a> <a id="9372" href="Assignment2.html#9342" class="Bound">B</a><a id="9373" class="Symbol">)</a> <a id="9375" class="Symbol">→</a> <a id="9377" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9379" href="Assignment2.html#9352" class="Bound">x</a> <a id="9381" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9383" href="Assignment2.html#9244" class="Postulate Operator">iff</a> <a id="9387" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9389" href="Assignment2.html#9364" class="Bound">y</a> <a id="9391" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a> <a id="9393" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="9395" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊</a> <a id="9397" href="Assignment2.html#9352" class="Bound">x</a> <a id="9399" href="Assignment2.html#9273" class="Postulate Operator">⇔-dec</a> <a id="9405" href="Assignment2.html#9364" class="Bound">y</a> <a id="9407" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌋</a>
</pre>{% endraw %}