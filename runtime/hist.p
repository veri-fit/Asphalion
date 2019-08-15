set title "histogram"
set term png
set output 'hist.png'
set auto x
set yrange [0.4:6.0]
set style data histogram
set style histogram cluster gap 1
set style fill solid border -1
#set boxwidth 0.9
#set xtic rotate by -45 scale 0
#set bmargin 10 
plot 'pbft.dat' using 2
#6:xtic(1) ti col, '' u 12 ti col, '' u 13 ti col, '' u 14 ti col
