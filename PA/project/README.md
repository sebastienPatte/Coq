## Build 
```
coq_makefile -f _CoqProject -o Makefile
make
```

## Multivariate Polynomials 

### `PolyDefs.v`
Les définitions pour les questions 1.1 et 1.2 sont dans `PolyDefs.v`  

### `Coeff.v`
- Preuve d'équivalence entre `valid_poly` et l'inductif de la question 1.1.a (`valid_pol`)
- égalité des preuves de validité (`leibniz`), la preuve de proof-irrelevance pour les booléens est dans `BoolHelp.v`
- Preuve que 2 polynomes ayant les mêmes coefficients sont les mêmes (`all_coeff_eq`)

### `PolyArith` 

- Définitions de la somme et la multiplication de polynomes (`sum_poly_` et `mul_poly_`)  
- définition de la somme de polynomes valides `sum_poly`, grâce à la preuve de conservation de validité `sum_valid` 
- définition de la multiplication de polynomes valides `mul_poly`, grâce à la preuve (incomplète et admise) de conservation de validité (`mul_valid`) 

### `PolyVal` 

Je n'ai pas réussi la preuve de la question 1.2.d, mais mes essais et le théorème admis `val_coeff` sont dans `PolyVal`. Ce fichier contient aussi les preuves suivantes :  
- la preuve que la somme de 2 polynomes est un morphisme pour l'évaluation (`sum_poly_val`)
- la preuve (incomplète et admise) que la multiplication de 2 polynomes est un morphisme pour l'évaluation (`mul_poly_val`) 



## Multivariate Polynomials 
Le fichier `BTauto.v` contient : 
- la défintion du type des formules booléennes (`form`)
- l'évaluation de cet inductif (`eval_form`) 
- la tactique `read_term` qui construit une formule `form` et une valuation, à partir d'une expression du type `bool` de coq.
- la transformation (`to_poly`) d'une formule `form` vers un polynome valide
- la preuve (`eval_form_to_poly`) que la valeur d'une formule booléene `f` est égale à l'évaluation du polynome `to_poly f`


## Expérience précédente avec Coq 
J'ai suivi ce même cours l'année dernière (je suis redoublant), ainsi q'un cours de Coq du LMFI au premier semestre de cette année (qui est plus un cours d'introduction).
J'ai aussi suivi un cours d'introdution à l'assistant de preuve "Isabelle" il y a 2 ans.

## Choix d'implémentation 
Pour représenter les monoïdes, j'ai utilisé la bibliothèque `FMapList`, avec du recul je pense qu'il aurait été plus simple d'utiliser des listes. 

Pour la multiplication des polynômes, j'ai utilisé `Equations`, mais la manière de dérouler la définition (avec des `simp`) n'est pas forcément la plus pratique pour les preuves nécessaires, une solution avec des fixpoints aurait san doute été plus pratique

Pour la preuve des tautologies booléennes je n'ai pas réussi / pas eu le temps, de faire une tactique automatisée, mais j'ai fourni quelques exemples à la fin du fichier `BTauto.v`. 