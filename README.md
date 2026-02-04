# MA4N1_Platonic_Solids

## Github

Link: https://github.com/Tylxr51/Platonic-Solids-Formalisation

Contributors:
- *Cadelliot* - Elliot Cadell **(2204857)**
- *Tylxr51* - Tyler Graves **(2202289)**
- *seantierney* - Sean Tierney **(2203421)**

We would like to be marked equally and all receive the same mark. You may look at the history if you're interested :)


## Original goals

At the start of this project, we set out to prove that there exists exactly $5$ Platonic Solids. Our approach to this was to define a Platonic Solid, derive an inequality, and show that this inequality only had $5$ solutions $-$ showing that there can only be $5$ unique Platonic Solids. We quickly found that this approach was flawed; we struggled to create a satisfactory definition for a Platonic Solid that didn't require a vast amount of geometric formalisation. In hindsight, this is quite obvious $-$ a Platonic Solid is after all a geometric object. We knew we wanted to steer clear of formalising geometric results in Lean as we had heard that it would be tricky and probably too much to handle. This is where we decided to take a different approach.

## Moving the Goalposts
We have now pivoted to proving that there exists exactly $5$ Platonic Graphs. This decision came from realising that, by doing this, we could follow virtually the same process as before but instead of having to formalising geometric notions, we could formalise results about graphs. This is much simpler, as we don't have to worry about the positions and distances of vertices $-$ just their relations to each other.

## Successes
As of this submission, we have shown that given a PlatonicGraph $-$ a finite graph that is regular, 3-connected, and planar, with the number of edges per face, $m>2$, and the degree of each vertex, $n>2$ $-$  then we have the inequality $(m-2)*(n-2)>4$. We can then solve this to show that there are only $5$ pairs $(m,n)$ that solve this, and therefore there are only $5$ unique PlatonicGraphs.

## Assumptions
To do this, we did have to cheat in a few places $-$ most importantly in our definition of a PlanarGraph. For a graph to be planar, we need to know whether the edges cross. This brings us back to our problem with geometry, with it being much more difficult to encode our vertices with a notion of their positions and distances in relation to each other. This then also means that defining a face becomes quite a challenge for the same reason.

To get around this, we simply defined a planar graph with the property $\verb+isPlanar+$. This doesn't actually say anything, but it is there as a placeholder for where a real definition of planarity would go. We have also defined a $\verb+Face+$ as just an abstract $\verb+Type*+$, without any real notion of what it is. We then just stated that there is a finite amount of them and that we can therefore count them. 

For our proof, we require three main theorems: 
- hVerts: $nV=2E$, 
- hFaces: $mF=2E$, 
- hEuler: $V-E+F=2$. 
  
where $V = |\text{Vertices}|$, $E =|\text{Edges}|$, $F =|\text{Faces}|$, $n = \deg{v}$ $\text{ (regular so equal for every vertex)}$, $m = \text{number of edges per face}$

We are able to build hVerts from just our definitions as it only requires vertices and their relations. However, the other two both require the number of faces, which we have no actual definition of. Therefore, we have had to make a few more assumptions about faces: first, that each face has the same number of edges; second, that the sum of the edges of each face is twice the total number of edges. From these assumptions, we can then prove that hFaces holds for every PlatonicGraph.

We also have to prove hEuler with `sorry` as it is both out of the scope of this project and would require a formal definition of both $F$ and $\verb+isPlanar.+$

### Shortcomings & Improvements

For the astute observers out there, you may have noticed that we haven't actually said anything about Platonic Solids. Instead, we have kind of worked on a problem that is parallel to our original goal. But there is good news $-$ Steinitz's Theorem states: 

```every convex polyhedron forms a 3-connected planar graph, and every 3-connected planar graph can be represented as the graph of a convex polyhedron```

Every convex polyhedron has an underlying graph formed by its vertices and edges in the natural way. A Platonic solid is a convex polyhedron with regular faces and the same degree at each vertex, which are encoded by the constants `m` and `n` in the definition of a `PlatonicGraph`.

Steinitz’s Theorem provides the link between such graphs and geometric solids, and justifies our graph-theoretic approach to classifying Platonic solids.

Steinitz’s Theorem has two relevant consequences for us:
1.  The graph of any convex polyhedron is planar and 3-connected. This guarantees that every Platonic solid gives rise to a graph satisfying the structural assumptions encoded in our definition of `PlatonicGraph`.

2. Conversely, Steinitz’s Theorem states that every planar, 3-connected graph can be realised as the graph of a convex polyhedron. When combined with the additional regularity and uniform face-degree assumptions of a `PlatonicGraph`, this polyhedron is necessarily a Platonic solid. This correspondence is unique up to graph isomorphism: different geometric realizations with the same graph are considered the same for classification purposes.

Our formalization therefore classifies Platonic solids by classifying their underlying graphs. The parameters `(m, n)`, representing the number of edges per face and the degree of each vertex respectively, have the same meaning in both graph-theoretic and geometric terms.

By proving that only five pairs `(m, n)` satisfy the necessary constraints, we show that there are exactly five Platonic graphs (up to isomorphism). By Steinitz’s Theorem, each of these graphs corresponds to a convex polyhedron, which are exactly the five Platonic solids. 