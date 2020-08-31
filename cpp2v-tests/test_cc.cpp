
__attribute__((regcall)) int foo() {
  return 0;
}

__attribute__((ms_abi)) int bar() {
  return 1;
}
