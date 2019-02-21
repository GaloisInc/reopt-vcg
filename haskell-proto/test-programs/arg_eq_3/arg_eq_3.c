long g(long a, long b) {
  return a + b;
}

long f(long x, long y) {
  long x1 = x + 2;
  long y1 = y + 3;
  long w = g(x1, y1);
  return w + 1;
}

int main() {
  return 0;
}
