param([string[]]$Modules = @(
    'Mathlib.Data.Finset.Sym', 'Mathlib.Data.Finset.Card',
    'Mathlib.Order.Interval.Finset.Nat', 'Mathlib.Data.Set.Basic',
    'Mathlib.Tactic.Linarith'
))
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
$previousElanHome = $env:ELAN_HOME
$previousCacheSetting = $env:MATHLIB_NO_CACHE_ON_UPDATE
try {
    $localElan = Join-Path $PSScriptRoot '.tools\elan'
    if (Test-Path -LiteralPath (Join-Path $localElan 'bin\lake.exe')) {
        $env:ELAN_HOME = $localElan
        $lake = Join-Path $localElan 'bin\lake.exe'
    } else { $lake = (Get-Command lake -ErrorAction Stop).Source }
    python bootstrap_mathlib.py
    if ($LASTEXITCODE -ne 0) { throw 'Pinned source bootstrap failed.' }
    $env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
    & $lake update
    if ($LASTEXITCODE -ne 0) { throw 'Local dependency resolution failed.' }
    & $lake build cache
    if ($LASTEXITCODE -ne 0) { throw 'Official cache tool build failed.' }
    & $lake env python cache_mathlib.py @Modules
    if ($LASTEXITCODE -ne 0) { throw 'Targeted cache download failed.' }
} finally {
    $env:ELAN_HOME = $previousElanHome
    $env:MATHLIB_NO_CACHE_ON_UPDATE = $previousCacheSetting
    Pop-Location
}
