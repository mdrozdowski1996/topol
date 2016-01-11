
(************************************************)
(******* ZADANIE: SORTOWANIE TOPOLOGICZNE *******)
(*********** AUTOR: MAREK DROZDOWSKI ************)
(***** CODE REVIEWER: RASTSISLAU MATUSEVICH *****)
(************************************************)
open PMap;;

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
