struct foo <a> {
  int size;
  a[] array;
};

int main() {
  int size = 5;
  int[] A = alloc_array(int, size);
  struct foo <int> *s = alloc(struct foo <int>);
  s->size = size;
  s->array = A;
  (s->array)[1]=10;
  return (s->array)[1];
}
