#include <stdint.h>

uint32_t bswap(uint32_t x) {
    return __builtin_bswap32(x);
}
