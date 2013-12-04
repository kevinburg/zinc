struct foo <a> {
  int size;
  a[] array;
};

int main() {
  int[] A = alloc_array(int, 5);
  struct foo <int> *s = alloc(struct foo <int>);
  s->size = 5;
  A[3] = 3;
  s->array = A;
  return 0;
}
