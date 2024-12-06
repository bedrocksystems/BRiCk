#include <stdio.h>
#include <SWI-Prolog.h>

int main(int argc, char **argv) {
  printf("initialise -> %i\n", PL_initialise(argc, argv));

  term_t goal1 = PL_new_term_ref();

  fid_t f1 = PL_open_foreign_frame();
  if(f1 == 0) printf("Failed to open f1.\n");

  term_t goal2 = PL_new_term_ref();
  PL_put_integer(goal2, 73);

  fid_t f2 = PL_open_foreign_frame();
  if(f2 == 0) printf("Failed to open f1.\n");

  term_t goal3 = PL_new_term_ref();
  PL_put_integer(goal3, 42);

  PL_rewind_foreign_frame(f1);

  term_t goals = PL_new_term_refs(1000);
  for(int k = 0; k < 1000; k++) {
    PL_put_integer(goals + k, 0);
  }

  int i;

  PL_get_integer(goal3, &i);

  printf("Integer 3: %i\n", i);

  PL_get_integer(goal2, &i);
  printf("Integer 2: %i\n", i);

  //PL_close_foreign_frame(f2);
  PL_close_foreign_frame(f1);

  return 0;
}
