class Point {};

void test() {

    {
        Point* p = new Point();
        delete p;
    }

    {
        Point* p = new Point[10];
        delete[] p;
    }

    {
        int* p = new int;
        delete p;
    }
    {
        int* p = new int[10];
        delete[] p;
    }
}
