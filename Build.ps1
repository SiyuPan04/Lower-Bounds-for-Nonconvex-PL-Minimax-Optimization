$ErrorActionPreference = 'Stop'

$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
if ($null -eq $lakeCommand) {
    throw 'lake was not found. Install Elan/Lean 4.32.0 or add lake to PATH.'
}
$lakeExe = $lakeCommand.Source

$leanFiles = @(
    Get-Item -LiteralPath (Join-Path $PSScriptRoot 'NCPLRevised.lean')
) + @(
    Get-ChildItem -LiteralPath (Join-Path $PSScriptRoot 'NCPLRevised') `
        -Filter '*.lean' -File -Recurse
)

# Requiring either a type colon or the end of the declaration-name line avoids
# treating ordinary prose in block comments as a Lean declaration.
$declarationTail = '(?:(?:\s.*)?:|\s*(?:--.*)?$)'
$badPattern = '\bsorry\b|\badmit\b|^\s*opaque\s+\S+' +
    $declarationTail + '|^\s*constant\s+\S+' + $declarationTail
$bad = $leanFiles | Select-String -Pattern $badPattern
if ($bad) {
    $bad | Format-Table Path, LineNumber, Line -AutoSize
    throw 'Forbidden proof placeholder, opaque declaration, or constant declaration found.'
}

# The manuscript states Lemma 2.2 without a proof, and the user has explicitly
# authorized treating precisely that statement as given. Reject every other
# project axiom, as well as a renamed or moved declaration.
$axiomPattern = '^\s*axiom\s+\S+' + $declarationTail
$axioms = @($leanFiles | Select-String -Pattern $axiomPattern)
$acceptedAxiomFile = Join-Path $PSScriptRoot 'NCPLRevised/AcceptedLemma22.lean'
$acceptedAxiomName = '^\s*axiom\s+acceptedFiniteHorizonSaddleResistingOracle\b'
if ($axioms.Count -ne 1 -or
    $axioms[0].Path -ne $acceptedAxiomFile -or
    $axioms[0].Line -notmatch $acceptedAxiomName) {
    $axioms | Format-Table Path, LineNumber, Line -AutoSize
    throw 'Axiom audit failed: exactly the accepted Lemma 2.2 declaration is allowed.'
}

$foreignImports = $leanFiles | Select-String `
    -Pattern '^import\s+(?!Mathlib(?:\.|$)|NCPLRevised(?:\.|$))'
if ($foreignImports) {
    $foreignImports | Format-Table Path, LineNumber, Line -AutoSize
    throw 'A Lean module imports a package other than Mathlib or this project.'
}

$expectedRootImports = Get-ChildItem `
        -LiteralPath (Join-Path $PSScriptRoot 'NCPLRevised') `
        -Filter '*.lean' -File -Recurse |
    Where-Object { $_.Name -ne 'AxiomAudit.lean' } |
    ForEach-Object {
        $relativePath = $_.FullName.Substring($PSScriptRoot.Length + 1)
        $relativePath.Substring(0, $relativePath.Length - 5) -replace '[\\/]', '.'
    } |
    Sort-Object
$actualRootImports = Get-Content `
        -LiteralPath (Join-Path $PSScriptRoot 'NCPLRevised.lean') |
    Where-Object { $_ -match '^import\s+' } |
    ForEach-Object { ($_ -replace '^import\s+', '').Trim() } |
    Sort-Object
$rootImportDifference = Compare-Object $expectedRootImports $actualRootImports
if ($rootImportDifference) {
    $rootImportDifference | Format-Table -AutoSize
    throw 'The root module does not import every non-audit proof module exactly once.'
}

# Refuse to publish host-specific absolute paths in tracked project files. The
# pattern itself is assembled in pieces so that this script does not match it.
$privatePathPatterns = @(
    '[A-Za-z]:[/\\](?:Use' + 'rs|Documents and Settings)[/\\]',
    '/Use' + 'rs/[^/]+/',
    '/ho' + 'me/[^/]+'
)
$leakPattern = '(?i)(' + ($privatePathPatterns -join '|') + ')'
$publicFiles = Get-ChildItem -LiteralPath $PSScriptRoot -File -Recurse |
    Where-Object {
        $_.FullName -notmatch '[\\/]\.lake[\\/]' -and
        $_.FullName -notmatch '[\\/]\.git[\\/]'
    }
$leaks = $publicFiles | Select-String -Pattern $leakPattern
if ($leaks) {
    $leaks | Format-Table Path, LineNumber, Line -AutoSize
    throw 'Private absolute path found.'
}

Push-Location $PSScriptRoot
try {
    & $lakeExe build
    if ($LASTEXITCODE -ne 0) { throw "lake build failed with exit code $LASTEXITCODE" }

    & $lakeExe env lean 'NCPLRevised/AxiomAudit.lean'
    if ($LASTEXITCODE -ne 0) { throw "axiom audit failed with exit code $LASTEXITCODE" }
}
finally {
    Pop-Location
}

Write-Host 'Verification passed: build, root coverage, axiom audit, placeholder scan, import scan, and privacy scan succeeded.'
