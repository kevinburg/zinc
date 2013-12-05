struct list <a> {
  int size;
  a[] array;
};

int mean(struct list <int> *l) {
  int sum = 0;
  for (int i = 0; i < l->size; i++)
    sum += (l->array)[i];
  return sum/(l->size);
}

int main() {
  int[] A = alloc_array(int, 5);
  for (int i = 0; i < 5; i++)
    A[i] = i+1;
  struct list <int> *l = alloc(struct list <int>);
  l->size = 5;
  l->array = A;
  return mean(l);
}
