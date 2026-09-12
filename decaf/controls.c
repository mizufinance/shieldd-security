#include <stdint.h>

volatile uint8_t decaf_secret[32];
volatile uint8_t decaf_output;
volatile uint8_t table[256];

__attribute__((noinline)) void decaf_done(void) { (void)decaf_output; }
__attribute__((noinline)) void decaf_entry(void) {
#if CONTROL == 1
    if (decaf_secret[0] & 1) decaf_output = 1;
    else decaf_output = 2;
#elif CONTROL == 2
    decaf_output = table[decaf_secret[0]];
#else
    decaf_output = decaf_secret[0] & 1;
#endif
    decaf_done();
}
int main(void) { decaf_entry(); return 0; }
