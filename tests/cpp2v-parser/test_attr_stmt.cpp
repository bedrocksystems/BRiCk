int f(int i)
{
    switch (i) {
    case 1:
        [[fallthrough]];
        case 2 : return 1;
    }
    return -1;
}
