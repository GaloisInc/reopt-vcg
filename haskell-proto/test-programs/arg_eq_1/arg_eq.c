long g(long a, long b) {
  return a + b;
}

long f(long x, long y, long z) {
  long x1 = x + 1;
  long y1 = y + 2;
  long w = g(x1, y1);
  return z;
}

int main() {
  return 0;
}
