for filename in ./*.sal; do
    echo $filename
    sal-wfc $filename
done
