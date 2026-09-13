#include <stdint.h>

volatile uint64_t decaf_secret;
volatile uint64_t decaf_output;
volatile uint32_t decaf_gate;
volatile uint64_t decaf_memory[8];

__attribute__((noinline)) uint64_t mix_add(uint64_t value) {
    volatile uint64_t temporary = value + 17;
    return temporary ^ 0x55;
}
__attribute__((noinline)) uint64_t mix_xor(uint64_t value) {
    return (value ^ 0xa7) + 5;
}
__attribute__((noinline)) uint64_t load_memory(void) {
    return decaf_memory[0];
}
__attribute__((noinline)) void decaf_done(void) { (void)decaf_output; }

__attribute__((noinline)) void decaf_entry(void) {
    uint64_t value = decaf_secret;
#if CONTROL == 1
    value = mix_add(value);
    value = mix_xor(value);
    if (value & 1) decaf_output = 1;
    else decaf_output = 2;
#elif CONTROL == 2
    value = mix_add(value);
    value = mix_xor(value);
    decaf_output = decaf_memory[(value >> 3) & 7];
#elif CONTROL == 3
    if (decaf_gate) {
#if defined(__x86_64__)
        __asm__ volatile("ucomisd %%xmm1, %%xmm0" ::: "cc");
#elif defined(__aarch64__)
        /* Deliberately undefined instruction: a reached path must fail. */
        __asm__ volatile(".inst 0" ::: "cc");
#else
#error Unsupported qualification target
#endif
    }
    decaf_output = mix_add(value);
#elif CONTROL == 4
    for (uint64_t i = 0; i < UINT64_C(1000000000); ++i)
        value = mix_add(value);
    decaf_output = value;
#elif CONTROL == 5
    decaf_memory[0] = value;
    value = load_memory();
    if (value & 1) decaf_output = 1;
    else decaf_output = 2;
#else
    uint64_t (*operation)(uint64_t) = (decaf_gate & 1) ? mix_add : mix_xor;
    for (uint64_t i = 0; i < 4; ++i) {
        value = operation(value);
        if (decaf_gate & 1) value += i;
        else value ^= i;
    }
    decaf_output = value;
#endif
    decaf_done();
}

int main(void) { decaf_entry(); return 0; }
