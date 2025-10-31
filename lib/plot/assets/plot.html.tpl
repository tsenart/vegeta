<!doctype html>
<html>
<head>
  <title>{{.Title}}</title>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <style>{{.UPlotCSS}}</style>
  <style>
    * {
      box-sizing: border-box;
    }
    
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', 'Roboto', 'Oxygen', 'Ubuntu', 'Cantarell', sans-serif;
      margin: 0;
      padding: 20px;
      transition: background 0.2s ease, color 0.2s ease;
    }
    
    body.dark {
      background: #0f1419;
      color: #e6edf3;
    }
    
    body.light {
      background: #ffffff;
      color: #1f2937;
    }
    
    .container {
      max-width: 1600px;
      margin: 0 auto;
    }
    
    .header {
      display: flex;
      justify-content: space-between;
      align-items: center;
      margin-bottom: 20px;
      flex-wrap: wrap;
      gap: 16px;
    }
    
    h1 {
      font-size: 24px;
      font-weight: 600;
      margin: 0;
    }
    
    .controls {
      display: flex;
      gap: 8px;
      flex-wrap: wrap;
      align-items: center;
    }
    
    .btn {
      padding: 6px 12px;
      border-radius: 6px;
      font-size: 13px;
      font-weight: 500;
      cursor: pointer;
      transition: all 0.15s ease;
      font-family: inherit;
    }
    
    body.dark .btn {
      border: 1px solid #30363d;
      background: #161b22;
      color: #e6edf3;
    }
    
    body.dark .btn:hover {
      background: #1f2937;
      border-color: #3d444d;
    }
    
    body.dark .btn:active {
      background: #0d1117;
    }
    
    body.dark .btn.active {
      background: #1f6feb;
      border-color: #1f6feb;
      color: #fff;
    }
    
    body.light .btn {
      border: 1px solid #d1d5db;
      background: #ffffff;
      color: #1f2937;
    }
    
    body.light .btn:hover {
      background: #f3f4f6;
      border-color: #9ca3af;
    }
    
    body.light .btn:active {
      background: #e5e7eb;
    }
    
    body.light .btn.active {
      background: #2563eb;
      border-color: #2563eb;
      color: #fff;
    }
    
    .chart-container {
      border-radius: 8px;
      padding: 20px;
      transition: background 0.2s ease, border-color 0.2s ease;
    }
    
    body.dark .chart-container {
      background: #161b22;
      border: 1px solid #30363d;
    }
    
    body.light .chart-container {
      background: #ffffff;
      border: 1px solid #e5e7eb;
    }
    
    .uplot {
      margin: 0 auto;
    }
    
    body.dark .uplot .u-legend {
      background: #0d1117;
      border: 1px solid #30363d;
      border-radius: 6px;
      padding: 12px;
      font-size: 13px;
    }
    
    body.light .uplot .u-legend {
      background: #f9fafb;
      border: 1px solid #e5e7eb;
      border-radius: 6px;
      padding: 12px;
      font-size: 13px;
    }
    
    .uplot .u-legend .u-series {
      cursor: pointer;
      padding: 4px 8px;
      border-radius: 4px;
      transition: background 0.15s ease;
    }
    
    .uplot .u-legend .u-value {
      font-family: 'SF Mono', 'Monaco', 'Menlo', 'Consolas', 'Liberation Mono', monospace;
      font-size: 12px;
      min-width: 80px;
      display: inline-block;
      text-align: right;
    }
    
    .uplot .u-axis text {
      font-family: 'SF Mono', 'Monaco', 'Menlo', 'Consolas', 'Liberation Mono', monospace;
    }
    
    
    body.dark .uplot .u-legend .u-series:hover {
      background: #161b22;
    }
    
    body.light .uplot .u-legend .u-series:hover {
      background: #f3f4f6;
    }
    
    .uplot .u-legend .u-series.u-off {
      opacity: 0.4;
    }
    
    .uplot .u-cursor-pt {
      background: #1f6feb;
      border: 2px solid #fff;
      border-radius: 50%;
    }
    
    body.dark .uplot .u-hz .u-cursor-x,
    body.dark .uplot .u-vt .u-cursor-y {
      border-color: #3d444d;
    }
    
    body.light .uplot .u-hz .u-cursor-x,
    body.light .uplot .u-vt .u-cursor-y {
      border-color: #d1d5db;
    }
    
    body.dark .uplot .u-select {
      background: rgba(31, 111, 235, 0.1);
      border: 1px solid #1f6feb;
    }
    
    body.light .uplot .u-select {
      background: rgba(37, 99, 235, 0.1);
      border: 1px solid #2563eb;
    }
    
    body.dark .uplot .u-axis {
      color: #8b949e;
    }
    
    body.light .uplot .u-axis {
      color: #6b7280;
    }
    
    body.dark .uplot .u-grid {
      stroke: #30363d;
    }
    
    body.light .uplot .u-grid {
      stroke: #e5e7eb;
    }
    
    @media (max-width: 768px) {
      body {
        padding: 12px;
      }
      
      .header {
        flex-direction: column;
        align-items: flex-start;
      }
      
      h1 {
        font-size: 20px;
      }
      
      .controls {
        width: 100%;
        justify-content: flex-start;
      }
      
      .chart-container {
        padding: 12px;
      }
    }
  </style>
</head>
<body class="dark">
  <div class="container">
    <div class="header">
      <h1>{{.Title}}</h1>
      <div class="controls">
        <button id="toggleTheme" class="btn">☀️ Light</button>
        <button id="resetZoom" class="btn">Reset Zoom</button>
        <button id="toggleLogScale" class="btn active">Log Scale</button>
        <button id="exportPNG" class="btn">Export PNG</button>
      </div>
    </div>
    
    <div class="chart-container">
      <div id="plot"></div>
    </div>
  </div>

  <script>{{.UPlotJS}}</script>
  <script>{{.PluginsJS}}</script>
  <script>
    (function() {
      const opts = {{.Opts}};
      const rowData = {{.Data}};
      
      // Pivot data from row-oriented to column-oriented
      const data = pivotData(rowData);
      
      // State
      let isDarkTheme = true;
      let isLogScale = true;
      let currentPlot = null;
      
      function createPlot(logScale) {
        // Build fresh series configuration each time to avoid state mutation
        const series = [{ label: opts.labels[0] }];
        for (let i = 1; i < opts.labels.length; i++) {
          series.push({
            label: opts.labels[i],
            stroke: opts.colors[i - 1] || '#8b949e',
            width: 2,
            points: { show: false },
            value: (u, v) => formatDuration(v)
          });
        }
        const plotWidth = Math.max(600, document.getElementById('plot').parentElement.clientWidth - 40);
        
        const axisColor = isDarkTheme ? '#8b949e' : '#6b7280';
        const gridColor = isDarkTheme ? '#30363d' : '#e5e7eb';
        
        // Build Y scale configuration conditionally
        const yScale = logScale
          ? {
              distr: 3,
              log: 10
            }
          : {
              // Linear is default - no distr needed
            };
        
        const uplotOpts = {
          title: null,
          width: plotWidth,
          height: 500,
          series: series,
          scales: {
            x: {
              time: false
            },
            y: yScale
          },
          axes: [
            {
              label: "Seconds elapsed",
              labelSize: 30,
              size: 50,
              stroke: axisColor,
              grid: {
                show: true,
                stroke: gridColor,
                width: 1
              },
              ticks: {
                show: false
              }
            },
            {
              label: "Latency",
              labelSize: 30,
              size: 80,
              stroke: axisColor,
              grid: {
                show: true,
                stroke: gridColor,
                width: 1
              },
              ticks: {
                show: false,
                size: 0
              },
              values: (u, vals) => vals.map(v => formatDuration(v))
            }
          ],
          legend: {
            show: true,
            live: true
          },
          cursor: {
            drag: {
              x: true,
              y: false
            },
            points: {
              show: true,
              size: 8,
              width: 2
            }
          },
          hooks: {
            setSelect: [
              function(u) {
                const min = u.posToVal(u.select.left, 'x');
                const max = u.posToVal(u.select.left + u.select.width, 'x');
                u.setScale('x', { min, max });
              }
            ]
          }
        };
        
        if (currentPlot) {
          currentPlot.destroy();
        }
        
        currentPlot = new uPlot(uplotOpts, data, document.getElementById('plot'));
        return currentPlot;
      }
      
      // Initialize plot
      createPlot(isLogScale);
      
      // Handle window resize
      let resizeTimeout;
      window.addEventListener('resize', function() {
        clearTimeout(resizeTimeout);
        resizeTimeout = setTimeout(function() {
          const plotWidth = Math.max(600, document.getElementById('plot').parentElement.clientWidth - 40);
          currentPlot.setSize({ width: plotWidth, height: 500 });
        }, 150);
      });
      
      // Toggle theme
      document.getElementById('toggleTheme').addEventListener('click', function() {
        isDarkTheme = !isDarkTheme;
        document.body.className = isDarkTheme ? 'dark' : 'light';
        this.textContent = isDarkTheme ? '☀️ Light' : '🌙 Dark';
        createPlot(isLogScale);
      });
      
      // Reset zoom
      document.getElementById('resetZoom').addEventListener('click', function() {
        currentPlot.setScale('x', { min: data[0][0], max: data[0][data[0].length - 1] });
      });
      
      // Toggle log scale
      document.getElementById('toggleLogScale').addEventListener('click', function() {
        isLogScale = !isLogScale;
        this.classList.toggle('active', isLogScale);
        createPlot(isLogScale);
      });
      
      // Export PNG
      document.getElementById('exportPNG').addEventListener('click', function() {
        exportToPNG(currentPlot, 'vegeta-plot.png');
      });
    })();
  </script>
</body>
</html>
