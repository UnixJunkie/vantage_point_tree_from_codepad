(* A Vantage Point Tree is a Binary Space Partitioning structure which allows
 * for fast nearest neighbour searches in a general metric space. In a VPTree
 * we select a distinguished point and call it the vantage point. The remaining
 * points may then be divided into two groups. Those which are within distance
 * d of the vantage point and those which are not. These two groups are referred
 * to as the inner and outer points respectively. This subdivision is performed
 * recursively on both the inner and outer points to form a tree.
 *
 * When searching a VPTree we use distance from the vantage point to cull the
 * search space. Assume we wish to find the nearest neighbour of a point q
 * and let the closest point to q found so far be denoted by c. If q is far
 * enough away from the vantage point and c is sufficiently close to q then it
 * is unnecessary to search the inner points as all such points will be further
 * away from q then c. Similarly, if q is close enough to the vantage point and
 * c is close enough to q it is unnecessary to search the outer points.
 *
 * Because VPTree's do not rely on the representation of the points stored and
 * require only the ability to compute distances between points they are well
 * suited for storage of points in non-euclidean spaces. For example, a VPTree
 * may be used to store strings using the edit-distance in a spell checking
 * application.
 *
 * For more details about VPTree's see:
 *     http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.41.4193
 *)

(* The representation of VPTree's used is an optimization of the idea outlined
 * above. As in the above idea we split points into two groups. Those which
 * are within distance d of the vantage point and those which are further
 * then d from the vantage point. In contrast to the above description,
 * however, we don't store d but instead store the distances to the closest
 * and furthest point from the vantage point in both the inner and outer
 * groups. This information allows for more aggressive pruning of the search
 * space during nearest neighbour queries.
 *)

type VPTree< 'a , 'b >
    = (*private*)
          Node of 'a * BoundedTree< 'a , 'b > * BoundedTree< 'a , 'b >
        | Pair of 'a * 'a
        | Leaf of 'a

and (*private*) BoundedTree< 'a , 'b > =
    { tree        : VPTree< 'a , 'b >
    ; innerRadius : 'b
    ; outerRadius : 'b
    }

(* Before proceeding with the implementation of the VPTree we some additional
 * functions are required. These are a partition function and a selection
 * function. Due to the size of the datasets involved we cannot afford to copy
 * the input arrays. As a result both functions perform their work inplace and
 * act on a subset of the input array, [i, j].
 *
 * In addition to partitioning the array the partition function tracks the 
 * smallest and largest value in each partition and ensures that this value
 * is at the start and end of the corresponding partition. This is necessary
 * to minimize the number of distance computations performed by the VPTree
 * implementation as distance computations are usually expensive.
 *
 * The selection algorithm used has expected linear time and is a modified
 * version of the partition based algorithm presented at
 *     http://en.wikipedia.org/wiki/Selection_algorithm
 *)
    
module Utilities =

    let rec partition (f : 'a -> 'b) (mu : 'b) (xs : 'a []) (i : int) (j : int) =
        let swap (i : int) (j : int) = let x = xs.[j] in xs.[j] <- xs.[i] ; xs.[i] <- x
        
        let setLeftMin  (k : int) = swap i (k - 1) ; swap k i
        let setLeftMax  (k : int) = ()
        let setRightMin (l : int) = ()
        let setRightMax (l : int) = swap j (l + 1) ; swap l j
        
        let rec left (min : 'b) (max : 'b) (k : int) =
            if j < k then k else
                let x = f xs.[k]
                if x < mu then
                    if x < min then setLeftMin k ; left x max (k + 1) else
                    if max < x then setLeftMax k ; left min x (k + 1) else
                        swap k (k - 1) ; left min max (k + 1)
                else
                    swap k j ; partition min max x x k (j - 1)
        
        and right (min : 'b) (max : 'b) (l : int) =
            if l < i then i else
                let x = f xs.[l]
                if not (x < mu) then
                    if x < min then setRightMin l ; right x max (l - 1) else
                    if max < x then setRightMax l ; right min x (l - 1) else
                        swap l (l + 1) ; right min max (l - 1)
                else
                    swap i l ; partition x x min max (i + 1) l
        
        and partition (lmin : 'b) (lmax : 'b) (rmin : 'b) (rmax : 'b) (k : int) (l : int) =
            if l < k then k else
                let x = f xs.[k]
                if x < mu then
                    if x < lmin then setLeftMin k ; partition x lmax rmin rmax (k + 1) l else
                    if lmax < x then setLeftMax k ; partition lmin x rmin rmax (k + 1) l else
                        swap k (k - 1) ; partition lmin lmax rmin rmax (k + 1) l
                else
                    if x < rmin then swap k l ; setRightMin l ; partition lmin lmax x rmax k (l - 1) else
                    if rmax < x then swap k l ; setRightMax l ; partition lmin lmax rmin x k (l - 1) else
                        swap k l ; swap l (l + 1) ; partition lmin lmax rmin rmax k (l - 1)
        
        if j < i then i else
            let x = f xs.[i]
            if x < mu
            then            left  x x (i + 1)
            else swap i j ; right x x (j - 1)

    let private selectPivot =
        let rng = new System.Random(int System.DateTime.Now.Ticks) in
        fun (i : int) (j : int) -> i + rng.Next(j - i + 1)

    let rec select (f : 'a -> 'b) (n : int) (xs : 'a []) (i : int) (j : int) : 'b =
        let k = partition f (f xs.[selectPivot i j]) xs i j
        if n = k || n = i || n = j || (k > i && n = k - 1) then f xs.[n] else
            if n < k
            then select f n xs (i + 1) (k - 1)
            else select f n xs (k + 1) (j - 1)

module VPTree =

    open Utilities

    let inline distance (x : ^a) (y : ^a) : ^b =
        (^a : (static member Distance : ^a * ^a -> ^b)(x, y))

    (* VPTree's are constructed using a recursive top down algorithm. First a
     * vantage point and distance d are selected and the points are divided
     * into inner and outer groups. Next VPTree's are constructed from these
     * two groups of points. Finally the resulting VPTree is constructed from
     * the vantage point and the two recursively constructed VPTree's.
     *
     * Two important factors determining the quality of the produced VPTree are
     * the selection of the vantage point and distance, d. In order to ensure a
     * balanced tree is produced we always select d to be the median of the
     * distances from the vantage point. This ensures that half of the points
     * will end up in the inner group and half in the outer group.
     *
     * Selection of the vantage point is more difficult. Ideally we wish to
     * select the vantage point such that the cost of searches in the resulting
     * VPTree is minimized. An often used heuristic for achieving this is to
     * select a vantage point such that the deviation from the median distance
     * is maximized. This helps to ensure that the inner and outer groups are
     * well separated.
     *
     * Unfortunately, it is not possible to try all vantage points to find the
     * best one as this would be too expensive, requiring O(n^2) time. To avoid
     * this problem we take a small random sample of points and let the vantage
     * point be the best point in this set.
     *)

    let inline private median (f : 'a -> 'b) (xs : 'a []) (i : int) (j : int) : 'b =
        select f (i + (j - i + 1) / 2) xs i j

    let inline private sndMoment (vp : 'a) (mu : 'b) (xs : 'a []) : float =
        let square x = x * x in Array.sumBy (fun x -> square (float (distance vp x - mu))) xs

    let private sample< 'a > =
        let rng = new System.Random(int System.DateTime.Now.Ticks) in
        fun (xs : 'a []) (i : int) (j : int) ->
            Seq.initInfinite (fun _ -> i + rng.Next(j - i + 1)) 
                |> Seq.distinct |> Seq.take (j - i + 1)
    
    let rec inline private selectVantagePoint (xs : 'a []) (i : int) (j : int) : int =
        let candidates = max 10 (min ((j - i + 1) / 50) 100)
        let samples    = max 20 (min ((j - i + 1) / 10) 200)
        let vantagePoints =
            sample xs i j |> Seq.truncate candidates |> Seq.map (fun vpi ->
                let vp = xs.[vpi]
                let is = Seq.truncate samples (sample xs i j)
                let ss = Array.ofSeq <| Seq.map (Array.get xs) is
                let mu = select (distance vp) (ss.Length / 2) ss 0 (ss.Length - 1)
                let sp = sndMoment vp mu ss
                (vpi, sp))
        fst (Seq.maxBy snd vantagePoints)

    (**************************************************************************)

    let inline ofArray (xs : 'a []) : VPTree< 'a , 'b > =
        let rec ofArray (i : int) (j : int) =
            if j - i = 0 then Leaf(xs.[i])         else
            if j - i = 1 then Pair(xs.[i], xs.[j]) else
                let k  = selectVantagePoint xs i j
                let vp = xs.[k] in xs.[k] <- xs.[i] ; xs.[i] <- vp
                (* If we select a really bad pivot and all elements of the
                 * input array are the same distance from vp this will fail.
                 * Fixing this isn't hard but it is annoying. As such it's
                 * left as an exercise for the reader.
                 *)
                let mu = median    (distance vp)    xs (i + 1) j
                let k  = partition (distance vp) mu xs (i + 1) j
                let inner =
                    { innerRadius = distance vp xs.[i + 1]
                    ; outerRadius = distance vp xs.[k - 1]
                    ; tree        = ofArray (i + 1) (k - 1)
                    }
                let outer =
                    { innerRadius = distance vp xs.[k]
                    ; outerRadius = distance vp xs.[j]
                    ; tree        = ofArray k j
                    }
                Node(vp, inner, outer)
        ofArray 0 (xs.Length - 1)
    
    (**************************************************************************)
    
    (* Computation of the nearest neighbour to a given query point uses a
     * recursive branch and bound algorithm. Subtree's are eliminated from
     * the search by employing the triangle rule to determine cases when no
     * element of a given subtree can possibly be the closest point to the
     * query.
     *)
    
    (* v = vantage point
     * q = query point
     * c = closest so far
     * x = true closest
     *
     * d(q, x) <= d(q, c)
     * 
     * d(v, q) <= d(v, x) + d(x, q)
     * d(v, q) <= d(v, x) + d(q, c)
     * d(v, q) - d(q, c) <= d(v, x)
     *
     * d(v, x) <= d(v, q) + d(q, x)
     * d(v, x) <= d(v, q) + d(q, c)
     *
     * iu < d(v, q) - d(q, c) <= d(v, x) --> not in inner
     * ou < d(v, q) - d(q, c) <= d(v, x) --> not in inner or outer
     * d(v, x) <= d(v, q) + d(q, c) < il --> not in inner or outer
     * d(v, x) <= d(v, q) + d(q, c) < ol --> not in outer
     *)
    let inline nearest (q : 'a) (vptree : VPTree< 'a , 'b >) =
        let rec nearest (dqc : 'b) (c : 'a) (vptree : VPTree< 'a , 'b >) : 'b * 'a =
            match vptree with
              Node(v, inner, outer) ->
                  let dvq = distance v q
                  let c   = if dvq < dqc then v else c
                  let dqc = min dvq dqc
                  if outer.outerRadius < dvq - dqc then (dqc, c)                 else
                  if dvq + dqc < inner.innerRadius then (dqc, c)                 else
                  if inner.outerRadius < dvq - dqc then nearest dqc c outer.tree else
                  if dvq + dqc < outer.innerRadius then nearest dqc c inner.tree else
                      (* The search order for the two subtrees is determined
                       * by a simple heuristic.
                       *)
                      if dvq + dvq < inner.outerRadius + outer.innerRadius then
                          let (dqc, c) = nearest dqc c inner.tree
                          let (dqc, c) = nearest dqc c outer.tree
                          (dqc, c)
                      else
                          let (dqc, c) = nearest dqc c outer.tree
                          let (dqc, c) = nearest dqc c inner.tree
                          (dqc, c)
            | Pair(x, y) ->
                  let dqx = distance q x
                  let dqy = distance q y
                  let c   = if dqx < dqc then x else c
                  let dqc = min dqx dqc
                  let c   = if dqy < dqc then y else c
                  let dqc = min dqy dqc
                  (dqc, c)
            | Leaf(x) ->
                  let dqx = distance q x
                  let c   = if dqx < dqc then x else c
                  let dqc = min dqx dqc
                  (dqc, c)

        match vptree with
          Node(v, _, _) -> snd (nearest (distance q v) v vptree)
        | Leaf(x)       -> x
        | Pair(x, y)    ->
              let dqx = distance q x
              let dqy = distance q y
              if dqx < dqy then x else y

module Example =

    open VPTree

    type Vector = V of int with
        static member Distance(V x, V y) = abs (x - y)
                
    let rng    = new System.Random(int System.DateTime.Now.Ticks)
    let xs     = Seq.distinct (List.init 1000 (fun i -> V <| rng.Next(i * i)))
    let vptree = VPTree.ofArray (Array.ofSeq xs)
    do printfn "%A" (List.map (fun i -> VPTree.nearest (V i) vptree) [ 1 ; 10 ; 100 ; 1000 ; 10000 ])
    do printfn "%A" (List.init 10 (fun i -> VPTree.nearest (V (rng.Next(1000 * 1000))) vptree))
