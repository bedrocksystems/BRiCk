// What [Egnu_null] relies on: an integer constant 0 of pointer size.
static_assert(__null == 0, "");
static_assert(sizeof(__null) == sizeof(void *), "");

void* test() {
  (void)(__null + 1);
  return __null;
}
