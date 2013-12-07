struct pair <a,b> {
  a x;
  b y;
};

a first(struct pair <a,b> *p) {
  return p->x;
}

b second(struct pair <a,b> *p) {
  return p->y;
}

int main() {
  struct pair <int,int> *a = alloc(struct pair <int,int>);
  struct pair <int,int> *b = alloc(struct pair <int,int>);
  a->x = 10; a->y = 5;
  b->x = 10; b->y = 5;
  if ((first(a) == first(b)) && (second(a) == second(b)))
    return 1;
  else
    return 0;
}
