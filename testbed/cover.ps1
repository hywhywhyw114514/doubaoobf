$javap = 'C:\Program Files\Eclipse Adoptium\jdk-11.0.31.11-hotspot\bin\javap.exe'
$classes = Get-Content classes.txt
$bizMap = @{
  'o.a.e' = 'Calc(iface)'
  'o.a.h' = 'Color'
  'o.a.m' = 'FlowHeavy'
  'o.a.q' = 'Main'
  'o.a.r' = 'Main$1'
  'o.a.y' = 'Setters'
  'o.a.z' = 'Setters$Box'
}
$report = @()
foreach ($cn in $classes) {
  $dump = & $javap -c -p -cp m_sm.jar $cn 2>$null
  $cur = $null
  $sw = 0; $ts = 0; $len = 0; $isAbstract = $false
  $flush = {
    if ($cur -ne $null) {
      $script:report += [pscustomobject]@{ cls=$cn; mtd=$cur; lkp=[int]$sw; tbl=[int]$ts; ins=[int]$len; abstr=$isAbstract }
    }
  }
  foreach ($line in $dump) {
    if ($line -match '^\s+(public|private|protected|static|final|synchronized|abstract|native|default).*\s([A-Za-z0-9_$<>]+)\(.*\)') {
      & $flush
      $cur = $Matches[2]; $sw = 0; $ts = 0; $len = 0
      $isAbstract = ($line -match 'abstract|native')
    }
    if ($line -match 'lookupswitch') { $sw++ }
    if ($line -match 'tableswitch') { $ts++ }
    if ($line -match '^\s+\d+:\s') { $len++ }
  }
  & $flush
}
$concrete = $report | Where-Object { -not $_.abstr -and $_.mtd -ne '<init>' -and $_.mtd -ne '<clinit>' }
"总具体方法(非init): $($concrete.Count)  含lookupswitch: $(($concrete|?{$_.lkp -gt 0}).Count)  裸方法(无switch,<40条): $(($concrete|?{$_.lkp -eq 0 -and $_.tbl -eq 0 -and $_.ins -lt 40}).Count)"
"===== 业务类方法明细（裸=无lookupswitch）====="
$concrete | Where-Object { $bizMap.ContainsKey($_.cls) } | Sort-Object cls,mtd | ForEach-Object {
  "{0,-8} {1,-12} ins={2,-5} lkp={3} tbl={4}" -f $bizMap[$_.cls], $_.mtd, $_.ins, $_.lkp, $_.tbl
}
"===== 业务类中的裸方法（ins>=40 才算有实质逻辑却没平坦化）====="
$concrete | Where-Object { $bizMap.ContainsKey($_.cls) -and $_.lkp -eq 0 -and $_.ins -ge 20 } | ForEach-Object {
  "{0,-8} {1,-12} ins={2} tbl={3}" -f $bizMap[$_.cls], $_.mtd, $_.ins, $_.tbl
}
