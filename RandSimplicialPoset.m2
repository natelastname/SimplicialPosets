restart;
needsPackage "Posets"
needsPackage "SimplicialPosets"


-- Gets a random size amtToGet subset of the rank rankToGet vertices of P.
randSub = (gnd, k) -> (
    -- Get a random subset. (This could be probably be improved.)
    subs := subsets(gnd, k);
    samp := subs#(random(0, (length subs)-1));
    -- Shuffle samp so that it randomizes the isomorphism. 
    -- TODO: Double check the effect this has on the output.
    random samp
    );

-- Converts the two lists A and B to a hash table.
genRelabelTable = (A, B) -> (
    C := for i from 0 to (length flatten A)-1 list(
	(flatten A)#i => (flatten B)#i
	);
    new HashTable from C
    );

-- From the Posets package.
-- Given an element "a" of P, returns its index in P.GroundSet.
-- (This index is a's row in P's relation matrix.)
indexElement = (P, a) -> (
    j := position(P.GroundSet, i -> i === a);
    if j === null then error("The element [" | toString a | "] is not in the poset.") else j
    );

removeRelations = (P, Q) -> (
    A := set coveringRelations(P);
    B := set coveringRelations(Q);
    rels := toList(A-B);
    gnd := P.GroundSet;
    poset(gnd,rels)
    );

-- Returns a hash table for looking up the rank of a vertex in P.
-- Expects a list formatted like the output of the function rankPoset.
createRankTable = (ranks) -> (
    L := for i from 0 to (length ranks)-1 list(toList ((length (ranks#i)):i));
    L = flatten L;
    L = for i from 0 to (length L)-1 list ((flatten ranks)#i => L#i);
    hashTable L
    );

-- Returns P, relabeled with a "'" after the end of every vertex. 
addPrime = P -> (
    newLabels := (P.GroundSet)/(vert -> 
	vert => toString(vert)|"'"
	);
    newLabels = hashTable(newLabels);
    labelPoset(P, newLabels)
    );
-- Returns P, with the vertices in L relabeled by adding the string S to the end.  
renameVerts = (P, L, S) -> (
    newLabels := (P.GroundSet)/(vert -> 
		if member(vert, set(L)) then (
		    vert => toString(vert)|toString(S)
		    ) else (
		    vert => vert
		    )
		);
    newLabels = hashTable newLabels;
    labelPoset(P, newLabels)
    );


-- Randomly assigns the interval of vert to P.
-- Modifies isUsed appropriately. (TODO: check this.) 
assignInterval = (P, facet, rankTable, finalRanks, isUsed) -> (
    
    rankFacet := rankTable#facet;
    Q := booleanLattice rankFacet;
    ranksQ := rankPoset Q;    
    r := rankFacet;
    print("-- r:"|toString(r));
    print("-- samples:");
    samples := for i from 0 to rankFacet-1 list(
	samp := randSub(finalRanks#i, binomial(rankFacet, i));
	samp
	);
    samples = samples | {{facet}};
    print(samples);
    Q = labelPoset(Q, genRelabelTable(ranksQ, samples));
    -- Find the maximal used vertices of Q. Then, change Q so that every used vertex in Q has
    -- the same interval in Q as it does in P.
    usedVerts := select(Q.GroundSet, vert -> isUsed#vert);
    print("-- usedVerts:");
    print(usedVerts);
    if(usedVerts === {}) then (
	print("-- There are no used vertices.");
	for vert in Q.GroundSet do( isUsed#vert = true; );
	return Q;
	);
    unusedVerts := select(Q.GroundSet, vert -> not isUsed#vert);
    maximal := maximalElements subposet(Q, usedVerts);
    print("-- maximal used vertices:");
    print(maximal);    
    
    -------------------------------------------------------------------
    -- Experimental stuff
    -------------------------------------------------------------------

    -- 
    A := subposet(Q, orderIdeal(Q, maximal));
    B := subposet(P, orderIdeal(P, maximal));
    f := isomorphism(A,B);
    
    g := hashTable(for vert in Q.GroundSet list( 
    	if f#?vert then(
            vert => f#vert
	    ) else (
	    vert => vert
	    )
    ));

    --test := addPrime(Q);
    --test2 := renameVerts(Q, maximal, "!");
    if (#(set(Q.GroundSet))) =!= (length (Q.GroundSet)) then (
	print("-- The relabeling g produced duplicates");
	);
    Q = labelPoset(Q, g);
    
    
    for vert in Q.GroundSet do(
	isUsed#vert = true;
	);
    
    return Q;
    -------------------------------------------------------------------
    
    
    H := subposet(Q, unusedVerts | maximal);
    unassigned := toList(set(minimalElements H)-set(maximal));
    print("-- Unassigned vertices:");
    print(unassigned);
    
    for vert in H.GroundSet do(
	isUsed#vert = true;
	);
    return H;
    ); 



allSteps = {};

randFromFVector = fVec -> (
   if  (testFVector fVec) == false then error "Invalid f-vector:" | toString(f);
   -- Initialize P to a poset of isolated vertices.
   verts := toList (1..(sum fVec));
   P := poset(verts, {});
   -- Construct the desired ranks of our poset.
   finalRanks := for i from 1 to (length fVec) list(
       take(verts,{sum(take(fVec, i-1)), sum(take(fVec,i))-1})
       );
   -- Make tables to store whether a vertex is used and the intended ranks.
   isUsed := new MutableHashTable from P.GroundSet/(x -> x => false);
   rankTable := createRankTable(finalRanks);
   vertNo := (length flatten finalRanks)-1;
   
   steps := {};
   
   while vertNo >= 0 do(
       print("---------------------------");
       facet := (flatten finalRanks)#vertNo;
       print("-- Selected facet:"|toString(facet));
       
       
       if(rankTable#facet != 0 and isUsed#facet == false) then (
	   Q := assignInterval(P, facet, rankTable, finalRanks, isUsed);	   
	   P = P + Q;
	   usedPoset := subposet(P, select(P.GroundSet,vert -> isUsed#vert));
	   print("-- isSimplicial(usedPoset)");
	   print(isSimplicial(usedPoset));
    	   steps = steps | {(P, Q, usedPoset)};
	   );
       vertNo = vertNo - 1;
       );
      
   for i in steps do(
       displayPoset(last i, SuppressLabels => false);       
       );   
   P
   );

end--

load "RandSimplicialPoset.m2"

P = randFromFVector {1,3,4,2};
P = randFromFVector {1,5,7,5,2};



for i in allSteps do(
    displayPoset(last i, SuppressLabels => false);       
    );


isSimplicial P
Q = closedInterval(P, 1, 19)
isBoolean Q
displayPoset(Q, SuppressLabels => false)
Q = closedInterval(P, 1, 10)
displayPoset(Q, SuppressLabels => false)
isBoolean Q

Q = first (allSteps#1)
displayPoset(Q, SuppressLabels => false)



isBoolean Q
length steps 

displayPoset(first (steps#0), SuppressLabels => false)
displayPoset(first (steps#1), SuppressLabels => false)
