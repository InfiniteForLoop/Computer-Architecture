int main (void) {
    int a = 0;
    int i;
    for (i = 0; i < 10000; i++){
        if((i % 6) == 0){
            a = 3;
        }
    }
    return 0;
}
