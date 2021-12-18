
# Categories Sandbox

LMFI Coq project with Mathieu & Sidney.

Useful actions :

 - To build the project : `make`
 - To remove the build files* : `make cleanall`
 - To open the projet with VSCode & VSCoq : `code .`
 - To add a file to the project : add it in '_CoqProject'

Files need to be built to be opened in the IDE (with `Require Import XYZ`).

\* Only 'CoqMakefile.conf' is not removed despite being generated, but I don't want to touch the make rules since they are in 'CoqMakefile', which is a generated file as well. So I just put it in the .gitignore file.
