(********************** Biblioteka PMap **********************)
type ('k, 'v) map =
  | Empty
  | Node of ('k, 'v) map * 'k * 'v * ('k, 'v) map * int

type ('k, 'v) t =
  {
    cmp : 'k -> 'k -> int;
    map : ('k, 'v) map;
  }

let height = function
  | Node (_, _, _, _, h) -> h
  | Empty -> 0

let make l k v r = Node (l, k, v, r, max (height l) (height r) + 1)

let bal l k v r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lv, lr, _) ->
        if height ll >= height lr then make ll lk lv (make lr k v r)
        else
          (match lr with
          | Node (lrl, lrk, lrv, lrr, _) ->
              make (make ll lk lv lrl) lrk lrv (make lrr k v r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rv, rr, _) ->
        if height rr >= height rl then make (make l k v rl) rk rv rr
        else
          (match rl with
          | Node (rll, rlk, rlv, rlr, _) ->
              make (make l k v rll) rlk rlv (make rlr rk rv rr)
          | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, v, r, max hl hr + 1)

let rec min_binding = function
  | Node (Empty, k, v, _, _) -> k, v
  | Node (l, _, _, _, _) -> min_binding l
  | Empty -> raise Not_found

let rec remove_min_binding = function
  | Node (Empty, _, _, r, _) -> r
  | Node (l, k, v, r, _) -> bal (remove_min_binding l) k v r
  | Empty -> invalid_arg "PMap.remove_min_binding"

let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k, v = min_binding t2 in
      bal t1 k v (remove_min_binding t2)

let create cmp = { cmp = cmp; map = Empty }
let empty = { cmp = compare; map = Empty }

let is_empty x = 
	x.map = Empty

let add x d { cmp = cmp; map = map } =
  let rec loop = function
    | Node (l, k, v, r, h) ->
        let c = cmp x k in
        if c = 0 then Node (l, x, d, r, h)
        else if c < 0 then
          let nl = loop l in
          bal nl k v r
        else
          let nr = loop r in
          bal l k v nr
    | Empty -> Node (Empty, x, d, Empty, 1) in
  { cmp = cmp; map = loop map }

let find x { cmp = cmp; map = map } =
  let rec loop = function
    | Node (l, k, v, r, _) ->
        let c = cmp x k in
        if c < 0 then loop l
        else if c > 0 then loop r
        else v
    | Empty -> raise Not_found in
  loop map

let remove x { cmp = cmp; map = map } =
  let rec loop = function
    | Node (l, k, v, r, _) ->
        let c = cmp x k in
        if c = 0 then merge l r else
        if c < 0 then bal (loop l) k v r else bal l k v (loop r)
    | Empty -> Empty in
  { cmp = cmp; map = loop map }

let mem x { cmp = cmp; map = map } =
  let rec loop = function
    | Node (l, k, v, r, _) ->
        let c = cmp x k in
        c = 0 || loop (if c < 0 then l else r)
    | Empty -> false in
  loop map

let exists = mem

let iter f { map = map } =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, v, r, _) -> loop l; f k v; loop r in
  loop map

let map f { cmp = cmp; map = map } =
  let rec loop = function
    | Empty -> Empty
    | Node (l, k, v, r, h) -> 
	  let l = loop l in
	  let r = loop r in
	  Node (l, k, f v, r, h) in
  { cmp = cmp; map = loop map }

let mapi f { cmp = cmp; map = map } =
  let rec loop = function
    | Empty -> Empty
    | Node (l, k, v, r, h) ->
	  let l = loop l in
	  let r = loop r in
	  Node (l, k, f k v, r, h) in
  { cmp = cmp; map = loop map }

let fold f { cmp = cmp; map = map } acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, v, r, _) ->
	  loop (f v (loop acc l)) r in
  loop acc map

let foldi f { cmp = cmp; map = map } acc =
  let rec loop acc = function
    | Empty -> acc
	| Node (l, k, v, r, _) ->
       loop (f k v (loop acc l)) r in
  loop acc map

(************************************************)
(******* ZADANIE: SORTOWANIE TOPOLOGICZNE *******)
(*********** AUTOR: MAREK DROZDOWSKI ************)
(***** CODE REVIEWER: RASTSISLAU MATUSEVICH *****)
(************************************************)


exception Cykliczne

let topol l = 
	let mapempty = List.fold_left (fun a x -> (List.fold_left (fun a y -> add y [] a) 
	              a (snd x))) (create (compare)) l in
	let mapneighbours = List.fold_left (fun a x -> add (fst x) (snd x) a) (mapempty) (l)
	in let score = ref [] 
	and used = ref (foldi (fun x _ a -> add x [-1] a)  mapneighbours (create (compare) ))
	in
	begin
		let rec dfs x = 
			if List.hd (find x !used) = -1 then
			begin
				used := add x [0] (!used);
				List.iter (fun y -> begin
					if (List.hd (find y (!used)) = 0) then
						raise Cykliczne;
					if (List.hd (find y (!used)) = -1) then
						dfs y;
						end) (find x mapneighbours);
				used := (add x [1] (!used));
				score := x::(!score);
			end
		in 
		List.iter ( fun x -> dfs (fst x) ) l;
		!score
	end

(******** SPRAWDZACZKA *********)
(**** POZYCJA a W LIŚCIE l *****)
let pos a l = 
	let poz = ref 0 and use = ref false in
	List.iter (fun x -> if (x <> a && (!use) = false) then poz := (!poz) + 1
	           else use := true ) l;
	(!poz);;	
(***FUNKCJA SPRAWDZAJĄCA POPRAWNOŚĆ ROZWIĄZANIA, GDY NIE MA CYKLU***)
let is_valid l ans =
	let rec pom_valid acc li ans =
		match li with 
			|[] -> acc
			|(f,s)::t -> 
				if (List.fold_left (fun a x -> (if (pos f ans) > (pos x ans) then false else a)) 
				(true) s) then (pom_valid acc t ans)
				else (pom_valid false t ans)
	in pom_valid true l ans	
			 
(*******TESTY*******)
(*******CYKLICZNE*******)

let l = (1,[1])::[];;
try(let _ = topol l in assert(false))
with Cykliczne -> ();;
let l =(1,[2])::(2,[3])::(3,[2])::[];;
try(let _ = topol l in assert(false))
with Cykliczne -> ();;
let l = (1,[2])::(2,[3])::(3,[4;5])::(4,[5])::[];;
assert(is_valid l (topol l));;
let l = (1,[2])::(2,[3])::(3,[4;5])::(4,[2;5])::[];;
try(let _ = topol l in assert(false))
with Cykliczne -> ();;

(******NIEISTNIEJĄCE_W_LIŚCIE_GŁÓWNEJ_WIERZCHOŁKI******)
let l = [];;
let l = (1,[0])::l;;
assert (is_valid l (topol l));;
let l = (2,[0])::l;;
assert (is_valid l (topol l));;

(*******SPRAWDZENIE_CZY_DZIAŁA_NA_INNYCH_TYPACH_NIŻ_INT******)
let l = [];;
let l = ('a',['b';'d'])::l;;
let l = ('b',['c';'d'])::l;;
let l = ('c',['d'])::l;;
assert (is_valid l (topol l));;
let l = [];;
let l = ("fst",["snd";"thr"])::l;;
let l = ("xyz",["abc";"snd"])::l;;
let l = ("cos",["fst";"xyz"])::l;;
assert (is_valid l (topol l));;
let l = [];;
let l = (true,[false])::l;;
let l = (false,[true])::l;;
try(let _ = topol l in assert(false))
with Cykliczne -> ();;

(******TESTY_RÓŻNE******)
let l = [];;
let l = (1,[0])::l;;
assert (is_valid l (topol l));;
let l = (0,[2])::l;;
assert (is_valid l (topol l));;
let l = (2,[3])::l;;
assert (is_valid l (topol l));;
let l = (4,[2;3])::l;;
assert (is_valid l (topol l));;
let l = (6,[2;3])::l;;
assert (is_valid l (topol l));;
let l = (9,[10;11])::l;;
assert (is_valid l (topol l));;
let l = (10,[9])::l;;
try(let _ = topol l in assert(false))
with Cykliczne -> ();;
