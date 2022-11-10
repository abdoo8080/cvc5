solver="./lean-proof.sh"
options=""
options=""
time=""
ulimit="ulimit -S -t 30"
# file="qflia-liageneric-nocutlemmas.txt"
# file="qflia-liageneric.txt"
file="leanUfRegressions.txt"

echo "Options: $options"
echo

while read name; do
    echo "$solver on $name";
    $ulimit; $time $solver $name $options;
    echo "=====================================";
done < $file
