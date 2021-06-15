module BTree

open Cp
open List 
open Seq

// (1) Datatype definition -----------------------------------------------------

type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = either (konst Empty) Node x

let outBTree x =
    match x with
    | Empty -> Left ()
    | Node (a,(t1,t2)) -> Right (a,(t1,t2))

// (2) Ana + cata + hylo --------------------------------------------------------

let baseBTree f g = id -|- (f >< (g >< g))
let recBTree g = baseBTree id g
let rec cataBTree g = g << (recBTree (cataBtree g)) << outBTree
let rec anaBTree g = inBTree << (recBTree (anaBTree g)) << g 
let hyloBTree h g = cataBTree h << anaBTree g

// (3) Map ---------------------------------------------------------------------

let fmap f = cataBTree ( inBTree << baseBTree f id)

// (4) Examples
// (4.1) Inversion (mirror)

let invBTree x = cataBTree ( inBTree << (id -|- id >< swap)) x 

// (4.2) Counting

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization

let inord x =
    let join (a,(l,r)) = l @ [a] @ r 
    in either nil join x 

let inordt x = cataBTree inord x 

let preord x =
    let f (a,(l,r)) = a :: (l @ r) 
    in either nil f x 

let preordt x = cataBTree preord x 

let postordt x = 
    let f (a,(l,r)) = l @ r @ [a] 
    in cataBTree (either nil f) x

// (4.4) Quicksort

let rec part x y = 
    match x y with
    | p [] -> ([],[])
    | p (h::t) -> if p h then let (s,l) = part p t in (h::s,l) else let (s,l) = part p t in (s,h::l)

let qsep x =
    match x with 
    | [] -> Left ()
    | (h::t) ->
        let (s,l) = part (<h) t
        in Right (h,(s,l))

let qSort x = hyloBTree inord qsep x 

// (4.5) Traces

let union left right =
    List.append left right |> Seq.distinct |> List.ofSeq

let tunion (a,(l,r)) = union (List.map (a::) l) (List.map (a::) r)

let traces x = cataBTree (either (konst [[]]) tunion) x

// (4.6)

let present x = inord x 

let strategy (d,x) =
    match (d,x) with
    | (d,0) = Left ()
    | (d,x+1) = Right ((x,d),((not d,x),(not d,x)))

let hanoi x = hyloBTree present strategy x

// (5) Depth and balancing (using mutual recursion)

let baldepth x =
    let g = either (konst(True,1)) (h << (id><f))
    h(a,((b1,b2),(d1,d2))) = (b1 && b2 && abs(d1-d2)<=1,1+max d1 d2)
    f((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2))
    in cataBTree g x 

let balBTree x = p1 << baldepth x

let depthBTree x = p2 << baldepth x 

// (6) Going polytipic

let tnat f x =
    let theta = uncurry mappend
    in either (konst mempty) (theta << (f >< theta)) x 

let monBTree f x = cataBTree (tnat f) x 

let preordt' x = monBTree singl x

let countBTree' x = monBTree (konst (Sum 1)) x 

// (7) Zipper

type Deriv<'a> = Dr bool of 'a (BTree of 'a) 
type Zipper<'a> = List<Deriv<'a>> 

let rec plug x y =
    match x y with
    | [] t = t 
    | ((Dr false a l)::z) t = Node (a,(plug z t,l))
    | ((Dr true a r)::z) t = Node (a,(r,plug z t))