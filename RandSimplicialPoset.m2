restart;
needsPackage "Posets"
needsPackage "SimplicialPosets"

debuggingMode = true;


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

-- Returns a hash table for looking up the rank of a vertex in P.
-- Expects a list formatted like the output of the function rankPoset.
createRankTable = (ranks) -> (
    L := for i from 0 to (length ranks)-1 list(toList ((length (ranks#i)):i));
    L = flatten L;
    L = for i from 0 to (length L)-1 list ((flatten ranks)#i => L#i);
    hashTable L
    );

-- Randomly assigns the interval of vert to P.
-- Modifies isUsed appropriately. 
assignInterval = (P, facet, rankTable, finalRanks, isUsed) -> (
    
    rankFacet := rankTable#facet;
    Q := booleanLattice rankFacet;
    ranksQ := rankPoset Q;    
    r := rankFacet;
    --print("-- r:"|toString(r));
    --print("-- samples:");
    samples := for i from 0 to rankFacet-1 list(
	samp := randSub(finalRanks#i, binomial(rankFacet, i));
	samp
	);
    samples = samples | {{facet}};
    --print(samples);
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
    A := subposet(Q, orderIdeal(Q, maximal));
    B := subposet(P, orderIdeal(P, maximal));
    -- This call to "isomorphism" is a bottleneck of this funciton
    f := isomorphism(A,B);
    
    g := hashTable(for vert in Q.GroundSet list( 
    	if f#?vert then(
            vert => f#vert
	    ) else (
	    vert => vert
	    )
    ));
    
    Q = labelPoset(Q, g);
    
    for vert in Q.GroundSet do(
	isUsed#vert = true;
	);
    
    return Q;
    ); 

randFromFVector = fVec -> (
   if  (testFVector fVec) == false then error "Invalid f-vector:" | toString(f);
   -- Initialize P to a poset of isolated vertices.
   verts := toList (1..(sum fVec));
   P := poset(verts, {});
   -- Construct the desired ranks of our poset.
   finalRanks := for i from 1 to (length fVec) list(
       take(verts,{sum(take(fVec, i-1)), sum(take(fVec,i))-1})
       );
   -- Make tables to store whether vertices are used and their intended rank.
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
	   --print("-- isSimplicial(usedPoset)");
	   --print(isSimplicial(usedPoset));
    	   steps = steps | {(P, Q, usedPoset)};
	   );
       vertNo = vertNo - 1;
       );
   for i in steps do(
       --displayPoset(last i, SuppressLabels => false);       
       );   
   P
   );

indexElement = (P, a) -> (
    j := position(P.GroundSet, i -> i === a);
    if j === null then error("The element [" | toString a | "] is not in the poset.") else j
    );

getZVector = P -> (
    rankFn := rankFunction P;
    data := for i in (maximalElements P) list(
	rankFn#(indexElement(P, i))
	);
    freqs := tally data;
    use ZZ;
    for i from 0 to (max rankFn) list(       	
	if freqs#?i then ( 
	    freqs#i
	    ) else (
	    0_ZZ
	    )
	)
    );
    
-- The probability that the Z_i rank i facets of P hit N rank i-1 faces
layerProb = (P, i, N) -> (
    Z := getZVector P;
    F := getFVector P;
            
    --k := Z#i; 
    k := F#i;
        
    L := for j from 0 to k list(
	-- j is the size of the set X
    	sgn := (-1)^j;
	-- The size of the complement of X
	comp := (N - j);
	-- Remember, each of the Z#i facets corresponds to a subset of i elements of [n].
	-- Here, a is the number of ways to select k i-subsets from the complement of X.
	a := (binomial(comp,i))^k;
	-- The number of times we will get this term in the sum
	numHit := binomial(N,j);
	sgn*a*numHit
	);
    A := sum L;    
    -- The amount of ways to choose the fixed set that we're covering:
    chooseFixed := binomial(F#(i-1), F#(i-1)-Z#(i-1));
    -- The amount of outcomes that would produce this event:
    good := chooseFixed*A;
    -- The number of ways we can choose k i-subsets of the F#(i-1) faces, with no restrictions. 
    total := (binomial(F#(i-1), i))^k; 

    print("-------------------------");    
    print("-- z-vector:");
    print(Z);
    print("-- f-vector:");
    print(F);

    print("-- i:");
    print(i);
    print("-- k:");
    print(k);
    print("-- F#(i-1):");
    print(F#(i-1));
    
    print("-- The amount of ways to cover some fixed "|toString( (F#(i-1)) - (Z#(i-1))   )|"-subset of ["|toString(F#(i-1))|"] with "|toString(k)|" size "|toString(i)|" subsets:");
    print(A);
    print("-- The amount of ways to choose the fixed set that we're covering: ");
    print(chooseFixed);
    print("-- The amount of outcomes that we are counting for this event:");
    print(good);
    print("-- The total amount of ways to choose k i-subsets of the F#(i-1) faces:");
    print(total);
    (good / total)_RR
    );

-- Get the probability of Z's  z-vector.
testZVector = (P) -> (
    F := getFVector P;
    Z := getZVector P;

    n := max (rankFunction P);


    L := for i from 1 to n list (
	-- If Z#i is zero, that means that this event never happens.
	if (Z#i == 0) then 1 else(
	    k := (F#(i-1)) - (Z#(i-1));
	    layerProb(P, i, k)
	    )
	);
    print L;
    product L
    );

-- Print the observed vs predicted Z-vector frequencies.
-- n is the number of trials to perform, fVec is the f-vector to use.
testVecProbs = (fVec, n) -> (
    
    probTable := new MutableHashTable from {};
    posetTable := new MutableHashTable from {};

    L = tally for i from 1 to n list(
	P := randFromFVector fVec;
       	Z := getZVector P;
	
	
	if not (probTable#?Z) then (
	    probTable#Z = testZVector P;
	    posetTable#Z = P;
	    );
	Z
    	);
    print("---------------------RESULTS----------------------");
    for i in pairs L do(
	Z := first i;
	observed := (L#Z)_RR;
	predicted := ((probTable#Z)*n)_RR;
      	print("-------------");
	print(Z);
	print("-- observed:"|toString(observed));
	print("-- predicted:"|toString(predicted));
	);
    
    return (L, posetTable);
    );

end--

load "RandSimplicialPoset.m2"
add = {0,0,6,5,2};
(observed, posetTable) = testVecProbs({1,4,6,4,1}+add,25);
peek observed
Q = posetTable#{0,0,1,1,3}
(testZVector Q)*25

Q = posetTable#{0,0,0,3,3}

testZVector Q




testVec = {0,0,1,2};


P = randFromFVector {1,3,4,2}
getZVector P


getFVector P
getZVector P
testZVector P

displayPoset(P, SuppressLabels => false);






P = randFromFVector {1,5,7,5,2};

isSimplicial P
Q = closedInterval(P, 1, 19)
isBoolean Q
displayPoset(Q, SuppressLabels => false)
Q = closedInterval(P, 1, 10)
displayPoset(Q, SuppressLabels => false)
isBoolean Q

Q = first (allSteps#1)
displayPoset(Q, SuppressLabels => false)


