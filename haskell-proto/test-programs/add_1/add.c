long add(long x) {
  long y = x;
  return y + 1;
}

unsigned long fib(unsigned long x) {
    if (x <= 1) {
	return x;
    } else {
	return fib(x-1)+fib(x-2);
    }
}

int main() {
  long x = add(42);
  return 0;
}
