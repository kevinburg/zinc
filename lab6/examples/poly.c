struct foo <a> {
  int size;
  a[] array;
};

int front(struct foo <a> *s) {
  return s->size;
}

int main() {
  int size = 5;
  int[] A = alloc_array(int, size);
  struct foo <int> *s = alloc(struct foo <int>);
  s->size = size;
  A[0] = 10;
  s->array = A;
  return front(s);
}
