needsPackage "Posets"
needsPackage "SimplicialPosets"

debuggingMode = true;

disp = (P) -> (
    displayPoset(P, SuppressLabels => false);
    );

-- From the Posets package.
-- Given an element "a" of P, returns its index in P.GroundSet.
-- (This index is a's row in P's relation matrix.)
indexElement = (P, a) -> (
    j := position(P.GroundSet, i -> i === a);
    if j === null then error("The element [" | toString a | "] is not in the poset.") else j
    );

-- From the Posets package.
-- Returns the nonzero indices in the ith row of P.relationMatrix, which correspond to 
-- elements greater than the ith element.
principalFilter' = (P, i) -> positions(first entries(P.RelationMatrix^{i}), j -> j != 0)

-- Modified "joinExists" from the Posets package.
-- Returns the index in P.GroundSet of every upper bound of a and b in P. 
-- Expects an element of P.GroundSet, not an index.
upperBounds = (P, a, b) -> (
    -- These are lists of the elements greater than a and b.
    OIa := principalFilter'(P, indexElement(P, a));
    OIb := principalFilter'(P, indexElement(P, b));
    -- "*" is the set intersection operator.
    toList (set(OIa)*set(OIb))
    );

-- Return the minimal upper bounds of a,b in P.
-- Only works on posets with zero.
minUpperBounds = (P, a, b) -> (
    allUB := upperBounds(P, a, b);
    minP := minimalElements(P);
    f := i -> (set(upperBounds(P, P.GroundSet#i, minP#0)))-set({i});
    nonminUB := sum(apply(allUB, f));
    -- minUB is a list of sets. Each element in a set can't be a minimal upper bound.
    if nonminUB == 0 then nonminUB = set();
    (set(allUB) - nonminUB)
    );

-- Finds the minimum upper bounds of the set L in P when P is a boolean lattice.
booleanMinUpperBound = (P, L) -> (
    --upperBound := toString(first L);
    upperBound := first L;
    for i from 1 to (length L)-1 do(
	--upperBound = first toList (minUpperBounds(P, toString(upperBound), toString(L#i)));
	upperBound = first toList (minUpperBounds(P, upperBound, L#i));
	upperBound = (P.GroundSet)#upperBound;
	);
    upperBound
    );



-- Erdős–Rényi random graph. Returns an edgeIdeals graph.
ERModel = (n, p) -> (
    R := QQ[vars(0..n)];
    E := select(edges completeGraph(R,n), (e -> random(1.0) < p));
    graph(R,E)
    );

-- Converts an edgeIdeals graph to a Graphs$graph.
toGraphsGraph = G -> (
    V := (vertices G)/(vert -> index vert);
    E := (edges G)/(edge -> {(index first edge), (index last edge)});
    Graphs$graph(V,E)
    );

-- Converts a Graphs$graph to an edgeIdeals graph.
toEdgeIdealsGraph = G -> (
    V := (vertices G)/(vert -> vars(vert));
    R := QQ[V];
    E := (Graphs$edges G)/(edge -> {(vars(first toList edge)), (vars(last toList edge))});
    E = E/(i -> {(first i)_R, (last i)_R});
    graph(R,E)
    );

-- Converts the output of getCliques to a list of boolean lattices.
-- Guarentees that the atoms of each boolean lattice will be the vertex set of the
-- corresponding clique, and that each boolean lattice's zero will be the same.
buildIntervals = cliques -> (
    for i from 0 to (length cliques)-1 list(
	P := booleanLattice (length (cliques#i));
	atomsP := atoms P;
	atomNo := 0;
	zeroP := first (minimalElements P);
	
	relabelTable := (P.GroundSet)/(vert -> 
	    if member(vert, set(atomsP)) then (
		atomNo = atomNo + 1;
		vert => (i,toString((cliques#i)#(atomNo-1)))
	    	) else if vert == zeroP then (
		zeroP => 0 
		) else(
	    	--vert => toString(i)|"|"|vert
		vert => (i,toString(vert))
	       	)
	    );
        labelPoset(P, hashTable relabelTable)
	)
    );

-- Given the facet intervals of two intersecting cliques and the cliques of their 
-- intersection, compute the edges to join to the relation graphs.
-- (Assumes the atoms and zero are already correct)
genEdges = (P1, P2, i1, i2, intCliques) -> (
    if intCliques == {} then return {};
    -- This converts intCliques to the corresponding faces in P1 and P2    
    newEdges := {};
    
    for i from 0 to (length intCliques)-1 do(
	    clique := intCliques#i;
    	    newEdges = newEdges | for j in subsets(clique) list(
		if j == {} then continue;
		
		L1 := j/(v -> (i1, toString v));
		L2 := j/(v -> (i2, toString v));
		
		A := booleanMinUpperBound(P1, L1);
		B := booleanMinUpperBound(P2, L2);
		if A==B then continue;	
		{A,B}
		);
	);
    newEdges        
    )

randSimplicialPoset = (n, p1, p2) -> (
    
    if (p1 < 0) or (p1 > 1) then error "p1 must be a probability.";
    if (p2 < 0) or (p2 > 1) then error "p2 must be a probability.";
    
    G := ERModel(n,p1);
    H := ERModel(n,p2);
    -- Note: there is a possible bug in getCliques that makes it return
    -- a subclique of a larger clique in some cases.
    -- This shouldn't matter for the sake of this program, but perhaps I should
    -- investigate this in the future.
    
    print("-- Generating intervals and computing the relation graph...");
    cliques := getCliques G;
    facetIntervals = buildIntervals(cliques);
    relGraphVerts := toList sum for i in facetIntervals list(set(i.GroundSet));
    relGraphEdges := {};
    for S in subsets(0..((length cliques)-1),2) do (
	indexA := first toList S;
	indexB := last toList S;
	A := cliques#(indexA);
	B := cliques#(indexB);
	int := set(A)*set(B);
	
	if int === set({}) then continue;
    	
       	intGraph := inducedSubgraph(toGraphsGraph H, (toList int)/(v -> index v));
	intGraph = toEdgeIdealsGraph intGraph;
        intCliques := getCliques intGraph;
	isolated := isolatedVertices intGraph;
	if isolated != {} then ( 
	    intCliques = intCliques | {isolated};
	    );
    	newEdges := genEdges(facetIntervals#indexA, facetIntervals#indexB, indexA, indexB, intCliques);	
	relGraphEdges = relGraphEdges | newEdges;
	);
    
    print("-- Computing connected components of relation graph...");
    relGraph := Graphs$graph(relGraphVerts, relGraphEdges);
    -- "classes" is guarenteed to be a set partition of relGraph.
    classes := Graphs$connectedComponents(relGraph);
    
    print("-- Relabeling the vertices of facetIntervals...");       
    -- Send every vertex to the first element of the list "classes" in it appears in.
    facetIntervals = for interval in facetIntervals list(
       	relabelTable := for vert in interval.GroundSet list(
	    newVert := vert;
	    for eqClass in classes do(
	       	if member(vert,set(eqClass)) then (
		    newVert = first eqClass;
		    break;
		    );
	       	);
	    vert => newVert
	    );
       labelPoset(interval, hashTable relabelTable)
       );
    print("-- Giving P the natural labeling...");  
    P := naturalLabeling sum facetIntervals;   
    P
    );
end--
load "randgraphtest.m2"
n = 10; p1 = 0.5; p2 = 0.75;
n = 5; p1 = 0.5; p2 = 0.75;
P = fromFVector{1,3,3,2}
P = randSimplicialPoset(n,p1,p2)
disp P


P = randSimplicialPoset(n,0.5,0.75);


outputTexPoset(P, "example.tex", SuppressLabels=>false)
runtimes := for i from 1 to 10 list(
    print("-- "|toString(i));
    T := elapsedTiming randSimplicialPoset(n,p1,p2);
    first T
    )

    sum(runtimes)/(length runtimes)
