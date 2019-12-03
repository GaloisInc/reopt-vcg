

#include<inttypes.h>
#include<stdint.h>
#include<stdio.h>

uint64_t fib(uint64_t x) {
    if (x <= 1) {
	return x;
    } else {
	return fib(x-1)+fib(x-2);
    }
}

static char digits[] = "0123456789abcdef";

void
write_hex_number_to_stdout(uint64_t num)
{
    for(int i = 15; i >= 0; i--)
        putchar(digits[(num >> i * 4) & 0xf]);

    putchar('\n');
}

int main() {
  uint64_t r = fib(5);
  write_hex_number_to_stdout(r);
  //printf("fib(5): %" PRIx64 "\n", r);
  // return 0;
  return r;
}
