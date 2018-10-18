long g(long a) {
  return a;
}

long f(long x) {
  long x1 = x + 2;
  long w = g(x1);
  return w + 1;
}

int main() {
  return 0;
}
