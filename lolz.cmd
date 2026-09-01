@echo off
title corporate

powershell.exe -NoProfile -Command "$marker=':'+'POWERSHELL:'; $text=[IO.File]::ReadAllText('%~f0'); Invoke-Expression (($text -split [regex]::Escape($marker),2)[1])"

echo.
echo Stopped or encountered an error.
pause
exit /b

:POWERSHELL:

$mouse = Add-Type -MemberDefinition @"
[System.Runtime.InteropServices.DllImport("user32.dll")]
public static extern void mouse_event(
    uint flags,
    int dx,
    int dy,
    uint data,
    System.UIntPtr extraInfo
);
"@ -Name "MouseInput" -Namespace "Wiggler" -PassThru

$MOVE = 0x0001
$radius = 240
$steps = 120
$pauseBetweenCircles = 0

Write-Host "lolz"

while ($true) {
    $previousX = $radius
    $previousY = 0

    for ($step = 1; $step -le $steps; $step++) {
        $angle = 2 * [Math]::PI * $step / $steps

        $x = [int][Math]::Round(
            $radius * [Math]::Cos($angle)
        )

        $y = [int][Math]::Round(
            $radius * [Math]::Sin($angle)
        )

        $mouse::mouse_event(
            $MOVE,
            $x - $previousX,
            $y - $previousY,
            0,
            [UIntPtr]::Zero
        )

        $previousX = $x
        $previousY = $y

        Start-Sleep -Milliseconds 10
    }

    if ($pauseBetweenCircles -gt 0) {
        Start-Sleep -Seconds $pauseBetweenCircles
    }
}
