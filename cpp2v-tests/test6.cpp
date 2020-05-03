/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:MIT-0
 */

class P {
private:
    int p;
public:
    P() {}
    P(int x):p(x) {}
    P(int x, int y):p(x+y) {}


};

class Q : public P {
public:
    Q() {}
    Q(int x):P(x) {}
};

int go(Q &x) {
    return 1;
}

int go(P &x) {
    return 0;
}
