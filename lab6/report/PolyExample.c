struct foo <a> {
  int size;
  a[] array;
};

int getSize(struct foo <a> *s) {
  return s->size;
}

int main() {
  int[] A = alloc_array(int, 5);
  struct foo <int> *s = alloc(struct foo <int>);
  s->size = 5;
  s->array = A;
  return getSize(s);
}
