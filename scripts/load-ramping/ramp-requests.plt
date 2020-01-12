# Two plots: success rate plot on top, rate/latency distribution below
set multiplot layout 2,1


#
# Shared config
#

# Scale (x/color)
set autoscale xfix
set logscale xycb 10

# Grid
set mxtics 10
set mytics 10
set tics scale 0.0000000001  # Tics themselves can't be styled indepedently, so use grid only
set grid xtics ytics mxtics mytics lc rgb '#888888' lw 0.5 lt 1, lc rgb '#888888' lt 1 lw 0.1


#
# Top plot: success rate
#

# Manual positioning to align both plots
set lmargin at screen 0.10
set rmargin at screen 0.87
set bmargin at screen 0.80
set tmargin at screen 0.95

# Scale (y only)
set yrange [1.0:100.0]

# Axes
unset xlabel
set xtics format ""
set ylabel "Success"
set ytics format "%.2f%%"

# Plot (incl. fraction to percentage conversion)
plot "results_success.txt" using 1:($2 * 100.0):(0.0) with line lw 3 lc rgb "red" title ""


#
# Bottom plot: rate vs latency
#

# Manual positioning to align both plots
set lmargin at screen 0.10
set rmargin at screen 0.87
set tmargin at screen 0.75
set bmargin at screen 0.15

# Scale (y only)
unset yrange
set autoscale yfix

# Axes
set xlabel "Requests (per sec)"
set xtics format "%.f"
set ylabel "Latency" offset -1.5,0,0
set ytics ( \
    "1ns" 1.0e0, "10ns" 1.0e1, "100ns" 1.0e2, \
    "1us" 1.0e3, "10us" 1.0e4, "100us" 1.0e5, \
    "1ms" 1.0e6, "10ms" 1.0e7, "100ms" 1.0e8, \
    "1s" 1.0e9, "10s" 1.0e10, "100s" 1.0e11 )

# Color box
set cblabel ""
set cbrange[0.001:100.0]
set format cb "%.9g%%"

# Plot (incl. fraction to percentage conversion)
set datafile separator " "
set pm3d map corners2color c1
splot "results_latency.txt" u 1:2:($3 * 100.0) with pm3d title ""
