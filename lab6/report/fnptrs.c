struct item<a>{
  a elem;
};

int intEq(int i1, int i2){
  return i1 == i2 ? 1 : 0;
}

int maxInt(int i1, int i2){
  return i1 > i2 ? i1 : i2;
}

int doItem(struct item<int>* i1, struct item<int>*i2, int (*f)(int, int)){
  return (*f)(i1->elem,i2->elem);
}

int main(){
  struct item<int>* item1 = alloc(struct item<int>);
  struct item<int>* item2 = alloc(struct item<int>);
  item1->elem = 5;
  item2->elem = 10;
  if(doItem(item1, item2, &intEq) == 0)
    return doItem(item1,item2, &maxInt);
  return item1->elem;
}
