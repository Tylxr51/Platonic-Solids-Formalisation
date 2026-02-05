**lake build output as of 00:04, 05.02.2026**


```
⚠ [967/971] Built MA4N1_Platonic_Solids.Current.File4_PlatonicGraphDefs
```
No comment required
```
warning: MA4N1_Platonic_Solids/Current/File4_PlatonicGraphDefs.lean:125:8: declaration uses 'sorry'
```
Explained in README.md, Euler's Characteristic Formula is assumed without proof

```
ℹ [968/971] Built MA4N1_Platonic_Solids.Current.File5a_InequalityDerivationTheorem
```
No comment required
```
info: MA4N1_Platonic_Solids/Current/File5a_InequalityDerivationTheorem.
lean:194:0: platonic_inequality.{u_1, u_2} (Pt : PlatonicGraph) : (Pt.m - 2) * (Pt.regular.n - 2) < 4
```
$\verb+#check+$ on platonic_inequality
```
⚠ [969/971] Built MA4N1_Platonic_Solids.Current.File6_InequalitySolutionClassification
```
No comment required
```
warning: MA4N1_Platonic_Solids/Current/File6_InequalitySolutionClassification.lean:14:8: aesop: failed to prove the goal after exhaustive search.
```
$\verb+aesop+$ solves part of the proof but not all of it. Proof is completed manually
```
warning: MA4N1_Platonic_Solids/Current/File6_InequalitySolutionClassification.lean:27:8: aesop: failed to prove the goal after exhaustive search.
```
$\verb+aesop+$ solves part of the proof but not all of it. Proof is completed manually
```
info: MA4N1_Platonic_Solids/Current/File6_InequalitySolutionClassification.lean:91:0: "Icosahedron Graph"
```
$\verb+#eval+$ on pair $(m,n)$
```
info: MA4N1_Platonic_Solids/Current/File6_InequalitySolutionClassification.lean:92:0: "Cube Graph"
```
$\verb+#eval+$ on pair $(m,n)$
```
info: MA4N1_Platonic_Solids/Current/File6_InequalitySolutionClassification.lean:93:0: "[Not a Platonic Graph]"
```
$\verb+#eval+$ on pair $(m,n)$
```
Build completed successfully (971 jobs).
```
No comment required