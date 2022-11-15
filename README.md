
# Categories Sandbox

LMFI Coq project with Clémence & Sidney.

Useful actions :

 - To build the project : `make`
 - To remove the build files* : `make cleanall`
 - To open the projet with VSCode & VSCoq : `code .`
 - To add a file to the project : add it in '_CoqProject'

Files need to be built to be opened in the IDE (with `Require Import XYZ`).

\* Only 'CoqMakefile.conf' is not removed despite being generated, but I don't want to touch the make rules since they are in 'CoqMakefile', which is a generated file as well. So I just put it in the .gitignore file.

Additional axioms :
 - Functional extentionality
 - Proof irrelevance (used for equalities)

Notations : 

    Category
        "a ~> b" := (hom a b)
        "f >> g" := (comp f g)
        "[ C ]" := (@ob C)

    Functor
        "C → D" := (Functor C D) \to
        "ob[ F ]" := (@f_ob _ _ F) 
        "hom[ F ]" := (@f_hom _ _ F _ _) 

    Transform
        "F ⇒ G" := (@Transform _ _ F G) \impl
        "tf[ t ]" := (@transform _ _ _ _ t) 
        "nat[ t ]" := (@naturality _ _ _ _ _ _ t) 
        "s # t" := (compose_transform s t) 
        "id_nat[ F ]" := (@id_transform _ _ F%Functor)
        "[ C , D ]" := (functor_category C D).
        
    Limit
        "a ---> b" := (universal_arrow a b)
