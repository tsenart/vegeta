<!doctype html>
<html>
<head>
  <title>{{.Title}}</title>
  <meta charset="utf-8">
  <style>{{.DygraphsCSS}}</style>
</head>
<body>
  <div id="latencies" style="font-family: Courier; width: 100%%; height: 600px"></div>
  <button id="download">Download as PNG</button>
	<script>{{.HTML2CanvasJS}}</script>
	<script>{{.DygraphsJS}}</script>
  <script>
  document.getElementById("download").addEventListener("click", function(e) {
    html2canvas(document.body, {background: "#fff"}).then(function(canvas) {
      var url = canvas.toDataURL('image/png').replace(/^data:image\/[^;]/, 'data:application/octet-stream');
      var a = document.createElement("a");
      a.setAttribute("download", "vegeta-plot.png");
      a.setAttribute("href", url);
      a.click();
    });
  });

  var container = document.getElementById("latencies");
  var opts = {{.Opts}};
  var data = {{.Data}};
  var plot = new Dygraph(container, data, opts);
  </script>
</body>
</html>
