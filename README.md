# MA4N1_Platonic_Solids

## Original goals

At the start of this project, we set out to prove that there exists exactly $5$ Platonic Solids. Our approach to this was to define a Platonic Solid, derive an inequality, and show that this inequality only had $5$ solutions $-$ showing that there can only be $5$ unique Platonic Solids. We quickly found that this approach was flawed; we struggled to create a satisfactory definition for a Platonic Solid that didn't require a vast amount of geometric formalisation. In hindsight, this is quite obvious $-$ a Platonic Solid is after all a geometric object. We knew we wanted to steer clear of formalising geometric results in Lean as we knew it would be tricky and probably too much to handle. This is where we decided to take a different approach.

## Moving the Goalposts
We have now pivoted to proving that there exists exactly $5$ Platonic Graphs. This decision came from realising that by doing this, we could follow virtually the same process as before but instead of formalising geometric notions, we could formalise graph notions. This is much simpler, as we don't have to worry about the positions and distances of vertices $-$ just their relations to each other.

## Successes
We have shown that given a PlatonicGraph $-$ a finite graph that is regular, connected, and planar $-$ if the number of edges per face, $m>2$, and the degree of each vertex, $n>2$, then we have $(m-2)*(n-2)>4$. We can then solve this inequality to show that there are only $5$ pairs $(m,n)$ that solve this, and therefore there are only $5$ unique PlatonicGraphs.

## Assumptions
To do this, we have had to cheat in a few places $-$ most importantly in our definition of a PlanarGraph. For a graph to be planar, we need to know whether the edges cross. This brings us back to our problem with geometry, being that it is much more difficult to encode our vertices with a notion of their positions and distances in relation to each other. This then also means that defining a face becomes quite a challenge for the same reason.

To get around this, we simply defined a planar graph with the property $\verb+isPlanar+$. This doesn't actually say anything, but it is there as a placeholder for where a real definition of planarity would go. We have also defined a $\verb+Face+$ as just an abstract $\verb+Type*+$, without any real notion of what it is. We then just stated that there is a finite amount of them and that we can therefore count them. 

For our proof, we require three main theorems: 
- hVerts: $nV=2E$, 
- hFaces: $mF=2E$, 
- hEuler: $V-E+F=2$. 
  
where $V = |\text{Vertices}|$, $E =|\text{Edges}|$, $F =|\text{Faces}|$, $n = \deg{v}$ $\text{ (regular so equal for every vertex)}$, $m = \text{number of edges per face}$

We are able to build hVerts from just our definitions as it only requires vertices and their relations. However, the other two both require the number of faces, which we have no actual definition of. Therefore, we have had to make a few more assumptions about faces: first, that each face has the same number of edges; second, that the sum of the edges of each face is twice the total number of edges. From these assumptions, we can then prove that hFaces holds for every PlatonicGraph.

Unfortunately, we have had to leave hEuler as a `sorry` proof, as it is both out of the scope of this project to prove and would require a formal definition for $F$.

points: should we define a platonic graph with m > 2 and n > 2, and should a platonic graph take an m and n so that we can say they are uniquely defined by m and n?