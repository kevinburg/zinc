struct list <a> {
  a data;
  struct list <a> *next;
};

int length(struct list <a> *l) {
  if (l == NULL)
    return 0;
  else
    return 1 + length(l->next);
}

int main() {
  struct list <bool> *a = alloc(struct list <bool>);
  struct list <bool> *b = alloc(struct list <bool>);
  a->next = b;
  return length(a);
}
