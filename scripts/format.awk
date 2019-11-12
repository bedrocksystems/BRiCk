BEGIN { printf "%-30s\t%s\t%-5s\t%-5s\t%-5s\r\n", " ","real", "user", "sys","mem"; }
{
    split($0, a, ",");
    split(a[1], real, ":");
    split(a[2], user, ":");
    split(a[3], sys, ":");
    split(a[4], mem, " ");
    split($0, name, " ");
    printf "%-30s\t%.2fs\t%.2fs\t%.2fs\t%d ko\r\n", name[1],real[2],user[2],sys[2],mem[2]
}
