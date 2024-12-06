#include <stdio.h>
#include <SWI-Prolog.h>

int main(int argc, char **argv) {
  printf("initialise -> %i\n", PL_initialise(argc, argv));

  atom_t atom1 = PL_new_atom("my_atom");
  atom_t atom2 = PL_new_atom("my_atom");
  term_t node1 = PL_new_term_ref();
  term_t node2 = PL_new_term_ref();
  PL_put_atom(node1, atom1);
  PL_put_atom(node2, atom2);

  printf("unify -> %i\n", PL_unify(node1, node2));

  return 0;
}
