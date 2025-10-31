// Data pivoting: Convert row-oriented data to column-oriented for uPlot
function pivotData(rowData) {
  if (!rowData || rowData.length === 0) return [[], []];
  
  const numCols = rowData[0].length;
  const cols = Array.from({ length: numCols }, () => []);
  
  for (let i = 0; i < rowData.length; i++) {
    for (let j = 0; j < numCols; j++) {
      cols[j].push(rowData[i][j]);
    }
  }
  
  return cols;
}

// Format milliseconds as human-readable duration
function formatDuration(ms) {
  if (ms == null) return '     -   ';
  
  let value, unit;
  
  if (ms < 1) {
    value = (ms * 1000).toFixed(ms * 1000 < 10 ? 1 : 0);
    unit = 'μs';
  } else if (ms < 1000) {
    value = ms.toFixed(ms < 10 ? 1 : 0);
    unit = 'ms';
  } else {
    value = (ms / 1000).toFixed(ms / 1000 < 10 ? 1 : 0);
    unit = ' s';
  }
  
  // Pad to ensure consistent width and add spacing to avoid tick overlap
  return value.padStart(4, ' ') + unit + '      ';
}

// PNG export functionality using native canvas
function exportToPNG(uplotInstance, filename) {
  const canvas = uplotInstance.root.querySelector('canvas');
  if (!canvas) return;
  
  canvas.toBlob(function(blob) {
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.setAttribute('download', filename || 'vegeta-plot.png');
    a.setAttribute('href', url);
    a.click();
    URL.revokeObjectURL(url);
  });
}
