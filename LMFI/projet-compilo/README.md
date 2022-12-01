Projet Coq LMFI : Mini-compilateur
==================================

Marthe : un mini-compilateur certifié. Vous trouverez des instructions plus détaillées en commentaire dans le fichier à compléter [`Marthe.v`](Marthe.v).

Listes de tactiques utiles pour le projet
-----------------------------------------

- `revert` préalablement à certaines utilisations de `induction` ;
- `eauto` ainsi que sa variante `eauto using` ; vous pouvez également ajouter des indices pour `eauto` à l'aide de la commande `Hint Resolve` ;
- `eapply` peut être également utile notamment pour appliquer les lemmes de transitivité.
