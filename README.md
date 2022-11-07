Mini-Macle
==========

Ré-implémentation "légère" du compilateur Macle 
produisant du code VHDL synthétisable sur FPGA.

Le but de ce prototype est d'expérimenter en profondeur la combinaison 
sûre de constructions de haut niveau (*valeurs fonctionnelles, polymorphisme paramétrique*) et de bas niveau (*signaux, entrées/sorties, automates, produit synchrone*).

--------------------

# usage :

```
$ make

$ cat examples/compose.ml
circuit twice_plus_one n =
  output o, u;
  ?u <- 5;
  let compose = fun f -> 
                ?o <- 42; 
                fun g -> 
                fun x -> f (g x) in
    let inc x = x + 1
    and twice x = x * 2 in
    compose inc twice n

$ ./maclec examples/compose.ml -vhdl
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.macle_runtime.all;

entity twice_plus_one is
  port(signal clock : in std_logic;
       signal reset : in std_logic;
       signal ml_arg1 : in int;
       signal ml_return : out int;
       signal z : out int;
       signal u : out int);
end entity;

architecture rtl of twice_plus_one is
  
begin
  u <= macle_int(5);
  z <= macle_int(42);
  ml_return <= macle_add(macle_mul(ml_arg1,macle_int(2)),macle_int(1));
  
end architecture;

$ make check-cc
(cd gen; make check)
ghdl -a -fno-color-diagnostics rtl/misc/*.vhdl rtl/*.vhdl;
rm -f *.o *.cf
```

---------------------


un programme Mini-Macle à la forme suivante :

```
circuit x =
  input i1, ... in;
  outputs o1, ... on;
  <exp>
```

les clause `inputs` et `outputs` sont optionnelles.

Le langage d'expressions comporte notamment la lecture d'une entrée `?x` et l'écriture d'une sortie `?x <- <exp>`. Par exemple :

```
circuit identity =
  input i;
  output o;
  ?o <- ?i
```
On distingue par typage une entrées `i` et son contenu `?i`. 

```
circuit identity =
  input i;
  output o;
  ?o <- i
line 4, characters 2-9:
Error: output o has type 'a5 input but it should have a basic type
```

Les entrées sont de type `'a input` et les sorties de types `'a output`. Cela permet de garantir que les entrées ne sont pas écrites et que les sorties ne sont pas lues.

### circuits combinatoires

Le langage comprend un *if-then-else*, les expressions arithmétiques et logiques,
 la séquence et la liaison locale. Par exemple :

```
circuit absolute_value =
  input i;
  output o;
  let x = (if ?i < 0 then 0 - ?i else ?i) in
  ?o <- x
```

Le langage offre aussi des signaux locaux accessibles en lecture (`~x`) et en écriture (`~x <- <exp>`).
Par exemple :

```
circuit swap =
  signal s1 = 4 in
  signal s2 = 6 in
  signal t = 0 in
  ~t <- ~s1;
  ~s1 <- ~s2;
  ~s2 <- ~t 
```

Là encore, on distingue par typage un signal (`x`) de type `'a signal` et son contenu (`~x`) de type `'a` pour un certain `'a`.

### circuits séquentiels

Il y a, en Macle, des automate synchrone. Par exemple :

```
circuit gcd_fsm =
  input n, m;
  output result;
  signal a = ?n in
  signal b = ?m in
  automaton
  | idle -> ?result <- ~a; continue idle
  | gcd  -> if ~a > ~b then (~a <- ~a - ~b; continue gcd) else 
            if ~a < ~b then (~b <- ~b - ~a; continue gcd) else
            (?result <- ~a; continue idle)
  in continue idle ;;
```

Les expressions Macle peuvent être composées en parallèle. Elles s'exécutent alors de façon réactive, mettant à jour les sorties à chaque cycle d'horloge. 
Par exemple :

```
circuit c =
  output o;
  signal count = 0 in
  signal sum = 0 in
  ((~count <- ~count + 1) // (~sum <- ~sum + ~count; ?o <- ~sum))
```

On peut notamment composer des automates en parallèle de cette manière.

### circuits paramétrés et valeur de retour

Les circuits peuvent prendre des arguments et retourner une valeur.
Par exemple :

```
circuit f x y =
  x + y 
```

qui est expansé en : 

```
circuit f =
  input ml_arg1, ml_arg2;
  output ml_return;
  ?ml_return <- (?ml_arg1) + (?ml_arg2)
```
 
Les entrées/sorties `ml_return`, `ml_arg-i`,`ml_start` et `ml_rdy` sont réservées. `ml_start` et `ml_rdy` sont utilisés pour s'interfacer avec le circuit si celui-ci est séquentiel. 

### récursion terminale et liaisons locales parallèle.

Les automates et produits synchrones calculant une valeur peuvent être formulées sous forme de fonctions récursives terminales. Dans l'exemple suivant, la fonction *gcd* est instanciée (dupliquée) deux fois, en sorte d'effectuer deux calculs en parallèle. 

```
circuit test i1 i2 i3 i4 =
  let rec gcd a b =
    if a > b then gcd (a-b) b else
    if a < b then gcd a (b-a) else a 
  in 
  let u = gcd i1 i2 
  and v = gcd i3 i4 
  in u + v
```

Ces fonctions récursives terminales prennent en paramètres des valeurs immédiates (de type `bool`, `int` ou `unit`) et retourne une valeur immédiate.


### valeurs fonctionnelles et polymorphisme paramétrique

Macle comprend aussi des fonctions unaires `(fun x -> e)` qui sont éliminées par réécriture et évaluation partielle. Par exemple :

```
circuit twice_plus_one n =
  output o;
  let compose = fun f -> 
                ?o <- 42; 
                fun g -> 
                fun x -> f (g x) in
    let inc x = x + 1
    and twice x = x * 2 in
    compose inc twice n
```

ce circuit est réécrit automatiquement en :

```
circuit twice_plus_one =
  input ml_arg1;
  output ml_return, o;
  (?o <- 42); ?ml_return <- ((?ml_arg1) * 2) + 1
```

Les paramètres des fonctions peuvent même être des signaux/entrées sorties, comme dans l'expression : `let signal x = 42 in (fun s -> ?s) x`, à la manière d'un  passage par référence.
Par exemple : 

```
circuit f =
  input i1, i2; 
  output o1, o2; 
  
  let counter o i init step =
    signal s = 0 in
    automaton 
    | q -> if ?i then (~s <- ~s+step; ?o <- ~s); continue q
    in ~s <- init; continue q 
  in
  
  (counter o1 i1 0 1) // (counter o2 i2 0 10)
```

--------------

Mini-Macle devrait pouvoir servir de base pour implémenter, non seulement un mini-ML (en utilisant de la mémoire via le runtime de l'implémentation O2B de la machine virtuelle OCaml), mais aussi un langage de description de matériel expressif pour programmer de façon sûre des interactions avec un environnement de capteur sur le FPGA.
