// Exact Haar-mean optimal canonical base-3/2 digit cost.  See bellman.py for the recurrence.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  int Nmax = atoi(argv[1]);
  uint8_t *V = calloc(1, 1); double prev = 0;
  for (int N = 0; N < Nmax; N++) {
    uint64_t M = 1ULL << N, mask = M - 1;
    uint8_t *W = malloc(2 * M);
    if (!W) { fprintf(stderr, "oom at N=%d\n", N + 1); return 1; }
    uint64_t tot = 0;
    #pragma omp parallel for reduction(+:tot) schedule(static)
    for (uint64_t m = 0; m < M; m++) {
      uint64_t t = 3 * m;
      uint8_t a = V[t & mask], b = 2 + V[(t + 1) & mask];
      uint8_t e = a < b ? a : b, o = 1 + V[(t + 2) & mask];
      W[2 * m] = e; W[2 * m + 1] = o; tot += e + o;
    }
    free(V); V = W;
    double A = (double)tot / (2.0 * M);
    printf("%d %llu A/N=%.6f dA=%.6f\n", N + 1, (unsigned long long)tot, A / (N + 1), A - prev);
    fflush(stdout); prev = A;
  }
  return 0;
}
