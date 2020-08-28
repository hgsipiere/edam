f n = g n (sub n 1);
g n k = if (eq k 2) (mod n k) (h n k);
p n k = eq (mod n k) 0;
h n k = if (p n k) 0 (g n (sub k 1));
main = f 79;
