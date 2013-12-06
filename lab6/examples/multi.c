struct foo <a> {
  int x;
  a y;
};

a bigger(struct foo <a> *s1, struct foo <a> *s2) {
  if (s1->x > s2->x)
    return s1->y;
  else
    return s2->y;
}

int main() {
  struct foo <int> *a = alloc(struct foo <int>);
  struct foo <int> *b = alloc(struct foo <int>);
  a->x = 10;
  a->y = 1;
  b->x = 5;
  b->y = 0;
  return bigger(a,b);
}
